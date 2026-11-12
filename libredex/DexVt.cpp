/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DexVt.h"

#include <algorithm>
#include <fstream>
#include <functional>
#include <iterator>
#include <map>
#include <set>
#include <unordered_map>

#include <boost/io/quoted.hpp>
#include <boost/locale/encoding_utf.hpp>
#include <json/value.h>
#include <json/writer.h>
#include <memory>
#include <sstream>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "BaselineProfile.h"
#include "BlockOffsetSink.h"
#include "CallGraph.h"
#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "DexEncoding.h"
#include "DexOutput.h"
#include "DexPosition.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "IRList.h"
#include "IROpcode.h"
#include "LoopInfo.h"
#include "MethodOverrideGraph.h"
#include "MethodProfiles.h"
#include "RedexContext.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "Trace.h"
#include "Walkers.h"

namespace dexvt {

namespace {
// Descriptors are interned MUTF-8, while JsonCpp accepts UTF-8. Decode before
// serialization so supplementary identifiers retain their catalog join key.
std::string json_descriptor(const std::string& value) {
  std::string result;
  const char* ptr = value.c_str();
  while (*ptr != '\0') {
    char32_t cp = mutf8_next_code_point(ptr);
    if (cp >= 0xd800 && cp <= 0xdbff) {
      always_assert_log(*ptr != '\0', "Unpaired surrogate in descriptor");
      const auto low = mutf8_next_code_point(ptr);
      always_assert_log(low >= 0xdc00 && low <= 0xdfff,
                        "Invalid surrogate in descriptor");
      cp = 0x10000 + ((cp - 0xd800) << 10) + low - 0xdc00;
    }
    result += boost::locale::conv::utf_to_utf<char>(&cp, &cp + 1);
  }
  return result;
}

// The deobfuscated method name is fully-qualified ("Lclass;.name:proto"); strip
// the class prefix so the record's `method` field holds just "name:proto"
// (class is a separate field; the full canonical id is `obfuscated_name`).
std::string bare_method(const std::string& full_deobf) {
  auto pos = full_deobf.find(";.");
  return pos == std::string::npos ? full_deobf : full_deobf.substr(pos + 2);
}

// Replace TAB/newline so a value is safe to embed in a TSV/ctags field.
std::string tsv_safe(std::string s) {
  for (char& c : s) {
    if (c == '\t' || c == '\n' || c == '\r') {
      c = ' ';
    }
  }
  return s;
}

// Short lowercase word for a CFG edge type (the vocabulary of ControlFlow's
// Edge printer, minus its pointer-bearing verbosity).
std::string_view edge_word(cfg::EdgeType t) {
  switch (t) {
  case cfg::EDGE_GOTO:
    return "goto";
  case cfg::EDGE_BRANCH:
    return "branch";
  case cfg::EDGE_THROW:
    return "throw";
  case cfg::EDGE_GHOST:
    return "ghost";
  case cfg::EDGE_TYPE_SIZE:
    break; // sentinel, not a real edge
  }
  return "edge";
}

// Deterministic, diffable CFG text. redex's show(cfg, code_only) prefixes every
// line with a live MethodItemEntry heap address (Show.cpp: `o << "[" << &mie`),
// which is non-reproducible across runs and breaks byte-stable/diffable output.
// Render our own from the same CFG: blocks in ascending id order, opcode lines
// only (via the pointer-free show(insn)), and branch structure as a sorted
// successor list -- targets are CFG edges, never inline in the instruction
// text.
std::string render_disasm(const cfg::ControlFlowGraph& cfg) {
  std::vector<cfg::Block*> blocks = cfg.blocks();
  std::sort(blocks.begin(), blocks.end(),
            [](const cfg::Block* a, const cfg::Block* b) {
              return a->id() < b->id();
            });
  const cfg::Block* entry = cfg.entry_block();
  std::ostringstream ss;
  for (cfg::Block* b : blocks) {
    ss << 'B' << b->id() << (b == entry ? ": entry\n" : ":\n");
    for (const auto& mie : *b) {
      if (mie.type == MFLOW_OPCODE) {
        const IRInstruction* insn = mie.insn;
        if (insn->has_string()) {
          // Dex strings are MUTF-8: a supplementary char (e.g. an emoji) is a
          // surrogate pair, invalid as UTF-8, so the default show() emits bytes
          // the NDJSON writer then mangles to U+FFFD. Re-render the trailing
          // string operand via show_escaped, which decodes MUTF-8 -> proper
          // UTF-8.
          const std::string line = show(insn);
          const auto q = line.find('"');
          ss << "  " << (q == std::string::npos ? line : line.substr(0, q));
          if (q != std::string::npos) {
            ss << boost::io::quoted(show_escaped(insn->get_string()));
          }
          ss << '\n';
        } else {
          ss << "  " << json_descriptor(show(insn)) << '\n';
        }
      }
    }
    std::vector<std::pair<size_t, std::string_view>> succs;
    for (const cfg::Edge* e : b->succs()) {
      if (e->target() != nullptr) {
        succs.emplace_back(e->target()->id(), edge_word(e->type()));
      }
    }
    std::sort(succs.begin(), succs.end());
    if (!succs.empty()) {
      ss << "  ->";
      for (const auto& [target_id, word] : succs) {
        ss << ' ' << word << " B" << target_id;
      }
      ss << '\n';
    }
  }
  return ss.str();
}

// The method's loops: LoopInfo's loops (its WTO components) on this CFG, with
// LoopInfo's nesting. Every edge counts, throw edges included, so a retry loop
// that only returns to its header through a catch handler is a loop, exactly
// as it is for SyntheticBlockCountsPass.
//
// Output order is (depth, header id): deterministic, and a parent always
// precedes its children.
void capture_loops(const cfg::ControlFlowGraph& cfg, MethodRecord* rec) {
  loop_impl::LoopInfo loop_info(cfg);
  if (loop_info.num_loops() == 0) {
    return;
  }
  struct Found {
    loop_impl::Loop* loop;
    uint32_t header;
    int depth;
  };
  std::vector<Found> order;
  order.reserve(loop_info.num_loops());
  for (auto& loop : loop_info) {
    order.push_back(Found{&loop, static_cast<uint32_t>(loop.get_header()->id()),
                          loop.get_loop_depth()});
  }
  std::sort(order.begin(), order.end(), [](const Found& a, const Found& b) {
    return a.depth != b.depth ? a.depth < b.depth : a.header < b.header;
  });
  UnorderedMap<const loop_impl::Loop*, int32_t> position;
  for (size_t pos = 0; pos < order.size(); ++pos) {
    position.emplace(order[pos].loop, static_cast<int32_t>(pos));
  }
  rec->loops.reserve(order.size());
  for (const auto& found : order) {
    const auto* parent = found.loop->get_parent_loop();
    rec->loops.push_back(
        LoopRecord{found.header, parent == nullptr ? -1 : position.at(parent)});
  }
  for (auto* block : cfg.blocks()) {
    if (const auto* loop = loop_info.get_loop_for(block)) {
      rec->block_loop.emplace_back(static_cast<uint32_t>(block->id()),
                                   static_cast<uint32_t>(position.at(loop)));
    }
  }
  std::sort(rec->block_loop.begin(), rec->block_loop.end());
}
// redex-debug-line-map-v2 files each method under DexOutput's method_to_id key:
// (index of the method in its dex << 32) | the first four bytes of that dex's
// signature. The export records the index per method and the signature once per
// dex, so the read side can rebuild the key and find a method's line stacks
// without parsing any dex.
struct LineMapKeys {
  std::map<std::string, uint32_t> dex_signatures; // dex tag -> signature
  UnorderedMap<const DexMethod*, uint32_t> dex_method_idx;
};

// Splits each method's key into its two halves. Every method of one dex carries
// the same signature; a dex whose methods disagree gets none, so no key is
// built for it rather than a wrong one.
LineMapKeys split_line_map_keys(
    const std::vector<const DexMethod*>& order,
    const UnorderedMap<DexMethod*, uint64_t>* method_to_id,
    const std::function<const std::string&(const DexMethod*)>& dex_of) {
  LineMapKeys keys;
  if (method_to_id == nullptr) {
    return keys;
  }
  std::set<std::string> conflicting_dexes;
  for (const DexMethod* method : order) {
    auto it = method_to_id->find(const_cast<DexMethod*>(method));
    if (it == method_to_id->end()) {
      continue;
    }
    keys.dex_method_idx.emplace(method,
                                static_cast<uint32_t>(it->second >> 32));
    const std::string& dex = dex_of(method);
    if (dex.empty()) {
      continue;
    }
    const auto signature = static_cast<uint32_t>(it->second & 0xffffffffu);
    auto [sig_it, inserted] = keys.dex_signatures.emplace(dex, signature);
    if (!inserted && sig_it->second != signature) {
      conflicting_dexes.insert(dex);
    }
  }
  for (const auto& dex : conflicting_dexes) {
    TRACE(MAIN, 1,
          "[dexvt] methods of %s carry different dex signatures; no line map "
          "key is recorded for it",
          dex.c_str());
    keys.dex_signatures.erase(dex);
  }
  return keys;
}

} // namespace

void Exporter::capture_pre_lowering(DexStoresVector& stores,
                                    ConfigFiles& conf) {
  auto scope = build_class_scope(stores);

  // 1) The class -> "<store>/<dex_index>" map from the finalized InterDex split
  // (dexen are final by the backend), so records can be grouped by dex file.
  UnorderedMap<const DexClass*, std::string> class_dex;
  for (auto& store : stores) {
    const auto& dexen = store.get_dexen();
    for (size_t di = 0; di < dexen.size(); ++di) {
      const std::string tag = store.get_name() + "/" + std::to_string(di);
      for (auto* cls : dexen[di]) {
        class_dex.emplace(cls, tag);
      }
    }
  }

  // Deterministic id assignment (serial, stable order) reused by emit():
  // methods first, then fields (static then instance per class), all in one id
  // space.
  uint32_t next_id = 0;
  for (auto* cls : scope) {
    for (auto* m : cls->get_dmethods()) {
      m_ids.emplace(m, next_id++);
    }
    for (auto* m : cls->get_vmethods()) {
      m_ids.emplace(m, next_id++);
    }
  }
  for (auto* cls : scope) {
    auto it = class_dex.find(cls);
    const std::string dx = it != class_dex.end() ? it->second : std::string();
    for (auto* f : cls->get_sfields()) {
      m_fields.push_back(FieldRecord{f, next_id++, dx});
    }
    for (auto* f : cls->get_ifields()) {
      m_fields.push_back(FieldRecord{f, next_id++, dx});
    }
  }

  // Class inheritance edges (deobfuscated super + directly-implemented
  // interfaces). Subclasses/implementors are derived on the read side by
  // inverting these, so only the forward edges are captured here.
  auto deobf_type = [](const DexType* t) -> std::string {
    auto* c = type_class(t);
    return c != nullptr ? c->get_deobfuscated_name_or_empty_copy() : show(t);
  };
  m_classes.reserve(scope.size());
  for (auto* cls : scope) {
    ClassRecord cr;
    cr.name = cls->get_deobfuscated_name_or_empty_copy();
    if (auto* super = cls->get_super_class(); super != nullptr) {
      cr.super = deobf_type(super);
    }
    for (const auto* intf : *cls->get_interfaces()) {
      cr.interfaces.push_back(deobf_type(intf));
    }
    m_classes.push_back(std::move(cr));
  }

  // 2) SourceBlock interaction index -> name (its own index space, distinct
  // from the MethodProfiles interaction ids).
  m_sb_interaction_names.assign(g_redex->num_sb_interaction_indices(),
                                std::string());
  for (auto&& [name, idx] :
       UnorderedIterable(g_redex->get_sb_interaction_indices())) {
    if (idx < m_sb_interaction_names.size()) {
      m_sb_interaction_names[idx] = name;
    }
  }

  // 3) Betamap coldstart rank: position of each real class in the coldstart
  // order. The order list interleaves marker sentinels (dex boundaries, pct-end
  // markers, interaction sections) that are synthetic and do not resolve to a
  // loaded class, so skipping types with no DexClass drops them cleanly.
  UnorderedMap<const DexType*, uint32_t> coldstart_rank;
  {
    uint32_t rank = 0;
    for (const auto& name : conf.get_coldstart_classes()) {
      auto* type = DexType::get_type(name);
      if (type == nullptr || type_class(type) == nullptr) {
        continue;
      }
      coldstart_rank.emplace(type, rank++);
    }
  }

  // Coarse InterDex grouping (lazily built; fetch once before the parallel
  // walk).
  const auto& interdex_groups = conf.get_cls_interdex_groups();
  const bool has_interdex_groups = conf.get_num_interdex_groups() > 0;

  // ART baseline profile (default/driver-input profile), if configured.
  const auto& mp = conf.get_method_profiles();
  for (const auto& interaction : mp.all_interactions()) {
    m_pgo_interactions.push_back(interaction.first);
  }
  // Sort for a deterministic manifest: all_interactions() iteration order is
  // not guaranteed stable across runs (consumers join by name, so order is
  // free).
  std::sort(m_pgo_interactions.begin(), m_pgo_interactions.end());
  m_baseline_available = !conf.get_baseline_profile_configs().empty();
  baseline_profiles::BaselineProfile baseline;
  if (m_baseline_available) {
    baseline = baseline_profiles::get_default_baseline_profile(scope, conf);
  }

  // Method -> callers xref. complete_call_graph folds MethodOverrideGraph
  // resolution into the caller edges, so virtual/interface callers are
  // complete.
  auto override_graph = method_override_graph::build_graph(scope);
  const call_graph::CompleteCallers complete_callers(*override_graph, scope);

  // 4) Parallel per-method capture. The CFG was cleared by PassManager before
  // the backend. It is rebuilt on a copy of the code, never on the code
  // itself: building and linearizing a CFG is not idempotent -- some methods
  // come out of every round trip in the other of two layouts -- so a round
  // trip here would change the DEX that ships, and only in builds that emit
  // dexvt. Anchors found in the copy are mapped back to the code's own entries.
  // The file of the position entries that mark gotos in a method's copy.
  const DexString* goto_mark_file = DexString::make_string("dexvt goto mark");
  walk::parallel::code(scope, [&](DexMethod* method, IRCode& code) {
    MethodRecord rec;
    rec.id = m_ids.at(method);

    std::unique_ptr<IRCode> copy;
    UnorderedMap<const MethodItemEntry*, const MethodItemEntry*> to_code;
    // The copy's CFG turns every goto into an edge, so a block whose only DEX
    // in the code is a goto -- an empty loop, `while (true) {}` -- keeps no
    // entry of its own. Each goto's place in the copy is marked with a position
    // entry before the CFG is built; the mark stays in the goto's block and
    // maps back to the code's goto.
    UnorderedMap<const DexPosition*, const MethodItemEntry*> goto_at_mark;
    const cfg::ControlFlowGraph* cfg = nullptr;
    if (code.cfg_built()) {
      cfg = &code.cfg();
    } else {
      copy = std::make_unique<IRCode>(code);
      // The copy holds one entry per entry of the code, in the same order.
      auto it = code.begin();
      for (auto copied = copy->begin(); copied != copy->end(); ++copied) {
        always_assert(it != code.end());
        to_code.emplace(&*copied, &*it);
        if (copied->type == MFLOW_OPCODE &&
            copied->insn->opcode() == OPCODE_GOTO) {
          auto mark = std::make_unique<DexPosition>(goto_mark_file, 0);
          goto_at_mark.emplace(mark.get(), &*it);
          copy->insert_before(copied, std::move(mark));
        }
        ++it;
      }
      always_assert(it == code.end());
      copy->build_cfg();
      cfg = &copy->cfg();
    }
    // Where a block begins in the code itself, given its first DEX-emitting
    // opcode in the code: the first entry after the previous DEX-emitting
    // opcode, skipping load-params (instruction lowering disposes the `this`
    // one). IRCode::sync gives that entry the address of whatever it emits
    // first for the block -- including an instruction it inserts in front of
    // the opcode, such as the nop before a branch to itself, which would put
    // the opcode's own entry one code unit late.
    auto start_in_code =
        [&](const MethodItemEntry* code_op) -> const MethodItemEntry* {
      auto op = code.iterator_to(const_cast<MethodItemEntry&>(*code_op));
      auto start = op;
      while (start != code.begin()) {
        auto prev = std::prev(start);
        if (prev->type == MFLOW_OPCODE &&
            !opcode::is_an_internal(prev->insn->opcode())) {
          break;
        }
        start = prev;
      }
      while (start != op && start->type == MFLOW_OPCODE &&
             opcode::is_a_load_param(start->insn->opcode())) {
        ++start;
      }
      return &*start;
    };
    // The same, given the block's first DEX-emitting opcode in the copy.
    auto block_start_in_code =
        [&](const MethodItemEntry* first_op) -> const MethodItemEntry* {
      return copy == nullptr ? first_op : start_in_code(to_code.at(first_op));
    };
    // The code's goto that branches to itself, among the gotos marked in an
    // instruction-less block of the copy. The CFG keeps such a block only when
    // it loops to itself (simplify removes every other empty block and may
    // move its marks along), so its own goto is the one whose branch target
    // sits right in front of it in the code.
    auto self_goto_in = [&](const cfg::Block* block) -> const MethodItemEntry* {
      for (const auto& mie : *block) {
        if (mie.type != MFLOW_POSITION) {
          continue;
        }
        auto found = goto_at_mark.find(mie.pos.get());
        if (found == goto_at_mark.end()) {
          continue;
        }
        const MethodItemEntry* go = found->second;
        for (auto e = code.iterator_to(const_cast<MethodItemEntry&>(*go));
             e != code.begin();) {
          --e;
          if (e->type == MFLOW_TARGET && e->target->src == go) {
            return go;
          }
          if (e->type == MFLOW_OPCODE &&
              !opcode::is_an_internal(e->insn->opcode())) {
            break;
          }
        }
      }
      return nullptr;
    };

    // Deterministic in-house CFG text (see render_disasm); hotness is captured
    // structurally in rec.blocks rather than double-encoded in the text.
    rec.disasm = render_disasm(*cfg);
    capture_loops(*cfg, &rec);

    UnorderedMap<const MethodItemEntry*, uint32_t> leaders;
    for (auto* block : cfg->blocks()) {
      // Anchor each block that emits DEX in the code (block_start_in_code
      // above). The anchor is a raw MethodItemEntry* of the code, and the sink
      // only compares pointers, so it relies on nothing between here and
      // DexOutput's sync pass disposing an anchored entry. That holds because
      // redex_backend runs instruction_lowering::normalize_cfg before this
      // capture, and instruction lowering then rewrites entries in place and
      // disposes only the `this` load-param, which is never an anchor. A
      // disposed anchor would not crash: a later allocation can reuse its
      // address, which then resolves to a wrong offset.
      //
      // A block whose only DEX in the code is a goto the copy's CFG absorbed
      // into an edge (`while (true) {}`) is anchored on that goto. An entry
      // block of only load-params emits no DEX and gets no anchor.
      const MethodItemEntry* first_op = nullptr;
      for (const auto& mie : *block) {
        if (mie.type == MFLOW_OPCODE &&
            !opcode::is_an_internal(mie.insn->opcode())) {
          first_op = &mie;
          break;
        }
      }
      if (first_op != nullptr) {
        leaders.emplace(block_start_in_code(first_op),
                        static_cast<uint32_t>(block->id()));
      } else if (const auto* go = self_goto_in(block); go != nullptr) {
        leaders.emplace(start_in_code(go), static_cast<uint32_t>(block->id()));
      }
      // Source-blocked blocks additionally carry hotness.
      const auto* sb = source_blocks::get_first_source_block(block);
      if (sb == nullptr) {
        continue;
      }
      for (size_t i = 0; i < sb->vals_size; ++i) {
        auto val = sb->get_val(i);
        auto appear = sb->get_appear100(i);
        float v = val ? *val : 0.f;
        float a = appear ? *appear : 0.f;
        if (v == 0.f && a == 0.f) {
          continue; // sparse: omit the default (0,0) sample
        }
        rec.blocks.push_back(BlockHotness{static_cast<uint32_t>(block->id()),
                                          static_cast<uint32_t>(i), v, a});
      }
    }
    if (!leaders.empty()) {
      block_offset_sink::set_leaders(method, std::move(leaders));
    }

    for (const auto& interaction : mp.all_interactions()) {
      const std::string& interaction_id = interaction.first;
      auto stat = mp.get_method_stat(interaction_id, method);
      if (!stat) {
        continue;
      }
      rec.pgo.push_back(MethodPgoStat{interaction_id, stat->appear_percent,
                                      stat->call_count, stat->order_percent});
    }

    auto* cls_type = method->get_class();
    if (auto it = coldstart_rank.find(cls_type); it != coldstart_rank.end()) {
      rec.betamap_rank = static_cast<int64_t>(it->second);
    }
    if (has_interdex_groups) {
      if (auto it = interdex_groups.find(cls_type);
          it != interdex_groups.end()) {
        rec.interdex_group = static_cast<int64_t>(it->second);
      }
    }
    if (auto it = baseline.methods.find(method); it != baseline.methods.end()) {
      rec.baseline_hot = it->second.hot;
      rec.baseline_startup = it->second.startup;
      rec.baseline_post_startup = it->second.post_startup;
    }

    const auto callers = complete_callers.get_callers(method);
    std::vector<uint32_t> caller_ids;
    caller_ids.reserve(callers.size());
    for (const auto* caller : UnorderedIterable(callers)) {
      if (auto it = m_ids.find(caller); it != m_ids.end()) {
        caller_ids.push_back(it->second);
      }
    }
    if (!caller_ids.empty()) {
      std::sort(caller_ids.begin(), caller_ids.end());
      rec.callers = m_caller_sets.insert(std::move(caller_ids)).first;
    }

    if (auto* dcls = type_class(cls_type); dcls != nullptr) {
      if (auto it = class_dex.find(dcls); it != class_dex.end()) {
        rec.dex = it->second;
      }
    }

    m_records.emplace(method, std::move(rec));
  });

  // Enable the block-offset sink so IRCode::sync (driven later by DexOutput)
  // records each SourceBlock's final code-unit offset; emit() drains it.
  block_offset_sink::enable();

  TRACE(MAIN,
        1,
        "[dexvt] pre-lowering captured %zu methods (%zu SB interactions)",
        m_records.size(),
        m_sb_interaction_names.size());
}

void Exporter::emit(ConfigFiles& conf,
                    const enhanced_dex_stats_t& output_totals,
                    const UnorderedMap<DexMethod*, uint64_t>* method_to_id) {
  const std::string path = conf.metafile("redex-dexvt.ndjson");
  std::ofstream ofs(path);
  always_assert_log(ofs.is_open(), "dexvt: failed to open %s for writing",
                    path.c_str());

  Json::StreamWriterBuilder builder;
  builder["indentation"] = "";
  // Hotness/PGO floats (SourceBlock val/appear, MethodProfiles percents) carry
  // ~15 meaningless digits; 7 significant figures is well beyond real precision
  // and cuts ~17-char literals to ~5. Ints (ids, sizes, access) are unaffected.
  builder["precision"] = 7;
  builder["precisionType"] = "significant";
  auto writer = std::unique_ptr<Json::StreamWriter>(builder.newStreamWriter());

  // Join-key validation: the pre-lowering capture and the post-lowering sizes
  // are joined by the interned DexMethod*. Every sized method must have a
  // captured id, otherwise identity drifted across lowering and records would
  // mis-associate sizes with bodies.
  size_t sized_without_id = 0;
  for (auto&& entry : UnorderedIterable(output_totals.method_size)) {
    if (m_ids.find(entry.first) == m_ids.end()) {
      ++sized_without_id;
    }
  }
  // Degrade, don't abort: --emit-dexvt is an opt-in diagnostic, so a method
  // that appeared after capture (identity drift) just loses its size in the
  // artifact rather than crashing the whole redex build. Expected to be 0 today
  // (capture runs after PassManager, before instruction_lowering).
  if (sized_without_id != 0) {
    TRACE(MAIN, 1,
          "[dexvt] %zu post-lowering sized methods had no captured id "
          "(DexMethod* join key drifted across lowering); sizes omitted",
          sized_without_id);
  }
  if (!m_records.empty() && output_totals.method_size.empty()) {
    // Degrade, don't abort (see above): emit the artifact without sizes rather
    // than crashing the build for an opt-in diagnostic.
    TRACE(MAIN, 1,
          "[dexvt] no per-method sizes captured for %zu records; sizes omitted",
          m_records.size());
  }

  // Deterministic order by the stable id (reproducible / diffable output).
  // Built before the manifest so the interned caller-set count is known when it
  // is written.
  std::vector<const DexMethod*> order;
  order.reserve(m_records.size());
  for (auto&& entry : UnorderedIterable(m_records)) {
    order.push_back(entry.first);
  }
  std::sort(order.begin(), order.end(),
            [this](const DexMethod* a, const DexMethod* b) {
              return m_ids.at(a) < m_ids.at(b);
            });

  // Intern caller-sets: the override-resolved call graph emits O(overrides x
  // callsites) IDENTICAL caller lists, so store each distinct (already
  // sorted+unique) list once in redex-dexvt.callersets.tsv and reference it by
  // a dense set_id. First-seen over the id-sorted `order` makes the set_ids
  // deterministic.
  UnorderedMap<const std::vector<uint32_t>*, uint32_t> caller_set_ids;
  std::vector<const std::vector<uint32_t>*> sets_by_id;
  for (const DexMethod* method : order) {
    const MethodRecord& rec = m_records.at_unsafe(method);
    if (rec.callers == nullptr) {
      continue;
    }
    auto [it, inserted] = caller_set_ids.emplace(
        rec.callers, static_cast<uint32_t>(sets_by_id.size()));
    if (inserted) {
      sets_by_id.push_back(rec.callers);
    }
  }

  const LineMapKeys line_map_keys = split_line_map_keys(
      order, method_to_id, [this](const DexMethod* m) -> const std::string& {
        return m_records.at_unsafe(m).dex;
      });

  // Manifest (first line): schema + the SourceBlock interaction index->name map
  // so consumers can label the blocks[] columns.
  Json::Value manifest;
  manifest["record"] = "manifest";
  // This is the on-disk EXPORT format version, independent of the derived
  // SQLite catalog's `sqlite._USER_VERSION` -- the two count separately and are
  // expected to differ (see facebook/dexvt/ARCHITECTURE.md). v10 adds
  // per-method `dex_method_idx` and the manifest's `dex_signatures` (the line
  // maps' method key); v9 adds per-method `loops` and `block_loop`; v8 carries
  // block_offsets for every block with code, entry block included, so a block's
  // three levels slice to the same region; v7 and v6 carry them for a narrower
  // set of blocks; v5 adds kind:"class" records (super + interfaces); v4
  // interns caller lists into callersets.tsv, referenced per method via
  // caller_set.
  manifest["schema_version"] = 10;
  manifest["method_count"] = static_cast<Json::UInt64>(m_records.size());
  manifest["field_count"] = static_cast<Json::UInt64>(m_fields.size());
  manifest["class_count"] = static_cast<Json::UInt64>(m_classes.size());
  manifest["callerset_count"] = static_cast<Json::UInt64>(sets_by_id.size());
  Json::Value sb_interactions(Json::arrayValue);
  for (const auto& name : m_sb_interaction_names) {
    sb_interactions.append(name);
  }
  manifest["sb_interactions"] = sb_interactions;
  Json::Value pgo_interactions(Json::arrayValue);
  for (const auto& id : m_pgo_interactions) {
    pgo_interactions.append(id);
  }
  manifest["pgo_interactions"] = pgo_interactions;
  manifest["proguard_map"] =
      conf.get_json_config().get("proguard_map", std::string());
  manifest["callgraph"] = "complete";
  manifest["baseline_available"] = m_baseline_available;
  // Method-profile resolution health (raw counts; size() and unresolved_size()
  // have different denominators, so do not divide them). Low unresolved => the
  // profile<->dex join landed.
  const auto& mp = conf.get_method_profiles();
  manifest["pgo_resolved"] = static_cast<Json::UInt64>(mp.size());
  manifest["pgo_unresolved"] = static_cast<Json::UInt64>(mp.unresolved_size());
  if (!line_map_keys.dex_signatures.empty()) {
    Json::Value signatures(Json::objectValue);
    for (const auto& [dex, signature] : line_map_keys.dex_signatures) {
      signatures[dex] = static_cast<Json::UInt>(signature);
    }
    manifest["dex_signatures"] = signatures;
  }
  writer->write(manifest, &ofs);
  ofs << "\n";

  // Skeleton entries (one per method, id-sorted) drive the O(1) seek sidecar
  // and the line-addressable ctags skeleton written after the body loop.
  struct SkelEntry {
    uint32_t id;
    uint64_t byte_off; // offset of the body record within the NDJSON
    uint64_t code_item_size;
    std::string obf; // precomputed, tsv-safe -- works for methods and fields
    std::string deobf_class;
    std::string deobf_member;
    char kind; // 'm' method, 'f' field
  };
  std::vector<SkelEntry> skeleton;
  skeleton.reserve(order.size() + m_fields.size());

  for (const DexMethod* method : order) {
    const MethodRecord& rec = m_records.at_unsafe(method);
    Json::Value r;
    r["id"] = static_cast<Json::UInt>(rec.id);
    r["obfuscated_name"] =
        json_descriptor(show(method)); // canonical cross-artifact join key
    r["method"] = json_descriptor(
        bare_method(method->get_deobfuscated_name_or_empty_copy())); // display
    if (auto* cls = type_class(method->get_class()); cls != nullptr) {
      r["class"] = json_descriptor(cls->get_deobfuscated_name_or_empty_copy());
    } else {
      r["class"] = json_descriptor(show(method->get_class()));
    }
    r["access"] = static_cast<Json::UInt>(method->get_access());
    r["kind"] = "method";
    if (!rec.dex.empty()) {
      r["dex"] = rec.dex;
    }
    if (auto it = line_map_keys.dex_method_idx.find(method);
        it != line_map_keys.dex_method_idx.end()) {
      r["dex_method_idx"] = static_cast<Json::UInt>(it->second);
    }

    if (auto it = output_totals.method_size.find(method);
        it != output_totals.method_size.end()) {
      r["code_item_size"] = static_cast<Json::UInt64>(it->second);
    }
    if (!rec.disasm.empty()) {
      r["disasm"] = rec.disasm;
    }
    if (!rec.blocks.empty()) {
      // Columnar (struct-of-arrays): the 4 keys are spelled once per method
      // instead of once per sample, and `ix` is the SourceBlock interaction
      // index (resolve via manifest `sb_interactions`) rather than the name
      // re-spelled every sample.
      Json::Value blk(Json::arrayValue), ix(Json::arrayValue),
          val(Json::arrayValue), a100(Json::arrayValue);
      for (const auto& b : rec.blocks) {
        blk.append(static_cast<Json::UInt>(b.block_id));
        ix.append(static_cast<Json::UInt>(b.interaction_idx));
        val.append(b.val);
        a100.append(b.appear100);
      }
      Json::Value blocks(Json::objectValue);
      blocks["blk"] = blk;
      blocks["ix"] = ix;
      blocks["val"] = val;
      blocks["a100"] = a100;
      r["blocks"] = blocks;
    }
    // block_offsets: [blk, start_code_unit] for EVERY cfg block. The
    // BlockOffsetSink resolved each block's first-MethodItemEntry anchor
    // (registered pre-lowering) to its final code-unit offset during
    // IRCode::sync, so every block -- source-blocked or not -- is addressable
    // by its shipped-DEX offset and its three levels (IR/true-DEX/native) slice
    // to exactly the same region. Sorted by (offset, blk) to match the read
    // side. Empty unless a sync pass ran under the enabled sink (the real
    // backend, or a driving test).
    if (const auto* offs = block_offset_sink::get(method); offs != nullptr) {
      std::vector<std::pair<uint32_t, uint32_t>> sorted(offs->begin(),
                                                        offs->end());
      std::sort(sorted.begin(), sorted.end(), [](const auto& a, const auto& b) {
        return a.second != b.second ? a.second < b.second : a.first < b.first;
      });
      Json::Value block_offsets(Json::arrayValue);
      for (const auto& [blk, off] : sorted) {
        Json::Value pair(Json::arrayValue);
        pair.append(static_cast<Json::UInt>(blk));
        pair.append(static_cast<Json::UInt>(off));
        block_offsets.append(pair);
      }
      if (!block_offsets.empty()) {
        r["block_offsets"] = block_offsets;
      }
    }
    if (!rec.loops.empty()) {
      // Columnar like `blocks`: loop i is (header[i], parent[i]), the parent
      // null for an outermost loop. Depth and loop sizes follow from these and
      // block_loop, so the read side derives them instead of the artifact
      // carrying a second copy that could disagree.
      Json::Value header(Json::arrayValue), parent(Json::arrayValue);
      for (const auto& loop : rec.loops) {
        header.append(static_cast<Json::UInt>(loop.header_blk));
        parent.append(loop.parent < 0
                          ? Json::Value(Json::nullValue)
                          : Json::Value(static_cast<Json::UInt>(loop.parent)));
      }
      Json::Value loops(Json::objectValue);
      loops["header"] = header;
      loops["parent"] = parent;
      r["loops"] = loops;
      Json::Value block_loop(Json::arrayValue);
      for (const auto& [blk, loop_id] : rec.block_loop) {
        Json::Value pair(Json::arrayValue);
        pair.append(static_cast<Json::UInt>(blk));
        pair.append(static_cast<Json::UInt>(loop_id));
        block_loop.append(pair);
      }
      r["block_loop"] = block_loop;
    }
    if (!rec.pgo.empty()) {
      Json::Value pgo(Json::objectValue);
      for (const auto& p : rec.pgo) {
        Json::Value jp;
        jp["appear_pct"] = p.appear_percent;
        jp["call_count"] = p.call_count;
        jp["order_pct"] = p.order_percent;
        pgo[p.interaction] = jp;
      }
      r["pgo"] = pgo;
    }
    if (rec.betamap_rank >= 0) {
      r["betamap_rank"] = static_cast<Json::Int64>(rec.betamap_rank);
    }
    if (rec.interdex_group >= 0) {
      r["interdex_group"] = static_cast<Json::Int64>(rec.interdex_group);
    }
    if (rec.baseline_hot || rec.baseline_startup || rec.baseline_post_startup) {
      Json::Value bp;
      bp["hot"] = rec.baseline_hot;
      bp["startup"] = rec.baseline_startup;
      bp["post_startup"] = rec.baseline_post_startup;
      r["baseline"] = bp;
    }
    if (rec.callers != nullptr) {
      // Reference the interned caller set (caller lists are often huge and
      // shared). Empty sets omit the field entirely.
      r["caller_set"] = static_cast<Json::UInt>(caller_set_ids.at(rec.callers));
    }

    // Record this body record's byte offset for the O(1) seek sidecar.
    const uint64_t byte_off = static_cast<uint64_t>(ofs.tellp());
    writer->write(r, &ofs);
    ofs << "\n";
    skeleton.push_back(SkelEntry{
        rec.id, byte_off,
        r.isMember("code_item_size") ? r["code_item_size"].asUInt64() : 0,
        tsv_safe(r["obfuscated_name"].asString()),
        tsv_safe(r["class"].asString()), tsv_safe(r["method"].asString()),
        'm'});
  }

  // Field records (kind:"field"): fields have no code, so no
  // size/disasm/blocks/ pgo/callers. Emitted after methods (their ids follow
  // the method id space) so the skeleton stays id-ascending.
  for (const FieldRecord& fr : m_fields) {
    Json::Value r;
    r["id"] = static_cast<Json::UInt>(fr.id);
    r["kind"] = "field";
    r["obfuscated_name"] = json_descriptor(show(fr.field));
    if (auto* cls = type_class(fr.field->get_class()); cls != nullptr) {
      r["class"] = json_descriptor(cls->get_deobfuscated_name_or_empty_copy());
    } else {
      r["class"] = json_descriptor(show(fr.field->get_class()));
    }
    r["field"] = json_descriptor(
        bare_method(fr.field->get_deobfuscated_name_or_empty()));
    r["access"] = static_cast<Json::UInt>(fr.field->get_access());
    if (!fr.dex.empty()) {
      r["dex"] = fr.dex;
    }
    const uint64_t byte_off = static_cast<uint64_t>(ofs.tellp());
    writer->write(r, &ofs);
    ofs << "\n";
    skeleton.push_back(SkelEntry{
        fr.id, byte_off, 0, tsv_safe(r["obfuscated_name"].asString()),
        tsv_safe(r["class"].asString()), tsv_safe(r["field"].asString()), 'f'});
  }

  // Class records (kind:"class"): inheritance edges only (super + interfaces),
  // no code/size, so they are not in the skeleton. Empty super/interfaces are
  // omitted; the read side derives subclasses/implementors by inverting these.
  for (const ClassRecord& cr : m_classes) {
    Json::Value r;
    r["kind"] = "class";
    r["class"] = json_descriptor(cr.name);
    if (!cr.super.empty()) {
      r["super"] = json_descriptor(cr.super);
    }
    if (!cr.interfaces.empty()) {
      Json::Value intfs(Json::arrayValue);
      for (const auto& i : cr.interfaces) {
        intfs.append(json_descriptor(i));
      }
      r["interfaces"] = intfs;
    }
    writer->write(r, &ofs);
    ofs << "\n";
  }

  // A line-addressable skeleton (one method/line; the 1-based line
  // number is the ctags address -- ctags cannot address by byte offset), a
  // byte-offset sidecar (id -> NDJSON offset + skeleton line) for the mmap/seek
  // path, and a universal-ctags file targeting the skeleton.
  const std::string skeleton_name = "redex-dexvt.skeleton.tsv";
  {
    std::ofstream skel(conf.metafile(skeleton_name));
    std::ofstream side(conf.metafile("redex-dexvt.sidecar.tsv"));
    std::ofstream tags(conf.metafile("redex-dexvt.tags"));
    always_assert_log(
        skel.is_open() && side.is_open() && tags.is_open(),
        "dexvt: failed to open skeleton/sidecar/tags for writing");
    tags << "!_TAG_FILE_FORMAT\t2\t/extended format/\n";
    tags << "!_TAG_FILE_SORTED\t0\t/0=unsorted,1=sorted/\n";
    for (size_t i = 0; i < skeleton.size(); ++i) {
      const auto& e = skeleton[i];
      const uint32_t skel_line = static_cast<uint32_t>(i + 1);
      skel << e.id << '\t' << e.obf << '\t' << e.deobf_class << '\t'
           << e.deobf_member << '\t' << e.code_item_size << '\n';
      side << e.id << '\t' << e.byte_off << '\t' << skel_line << '\n';
      // Every entity gets a ctags entry (fall back to the obfuscated name when
      // there is no deobfuscated name -- synthetic/unrenamed), so the tag count
      // equals the record count and the reader can navigate to all of them.
      // tsv_safe already stripped any TAB. kind: 'm' method, 'f' field.
      const std::string& tag_name =
          e.deobf_member.empty() ? e.obf : e.deobf_member;
      tags << tag_name << '\t' << skeleton_name << '\t' << skel_line
           << ";\"\tkind:" << e.kind << "\tclass:" << e.deobf_class << '\n';
    }
  }

  // Caller-set sidecar: one line per distinct set, `set_id<TAB>comma,ids` in
  // artifact (sorted+unique) order. Uncompressed at rest so the pure-stdlib
  // reader can line-seek it. Empty sets never consume a set_id (methods omit
  // `caller_set`).
  {
    std::ofstream cs(conf.metafile("redex-dexvt.callersets.tsv"));
    always_assert_log(cs.is_open(),
                      "dexvt: failed to open callersets for writing");
    for (size_t sid = 0; sid < sets_by_id.size(); ++sid) {
      cs << sid << '\t';
      const auto& ids = *sets_by_id[sid];
      for (size_t j = 0; j < ids.size(); ++j) {
        if (j != 0) {
          cs << ',';
        }
        cs << ids[j];
      }
      cs << '\n';
    }
  }

  TRACE(
      MAIN,
      1,
      "[dexvt] wrote %s (%zu methods, %zu fields, %zu caller-sets, %zu method "
      "sizes)",
      path.c_str(),
      m_records.size(),
      m_fields.size(),
      sets_by_id.size(),
      output_totals.method_size.size());

  // Drop the (whole-app-sized) recorded offsets now they are emitted, and
  // disable the sink so any later IRCode::sync in the process is a no-op.
  block_offset_sink::clear();
}

} // namespace dexvt
