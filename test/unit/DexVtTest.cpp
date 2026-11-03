/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DexVt.h"

#include <algorithm>
#include <climits>
#include <filesystem>
#include <fstream>
#include <gtest/gtest.h>
#include <json/reader.h>
#include <json/value.h>
#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <string>
#include <vector>

#include "BlockOffsetSink.h"
#include "ConfigFiles.h"
#include "Creators.h"
#include "DexClass.h"
#include "DexInstruction.h"
#include "DexOutput.h"
#include "DexStore.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "InstructionLowering.h"
#include "RedexTest.h"

namespace {

DexClass* create_foo_class() {
  ClassCreator cc(DexType::make_type("LFoo;"));
  cc.set_super(type::java_lang_Object());
  cc.add_method(assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:()I"
      (
        (const v0 42)
        (return v0)
      )
    )
  )"));
  cc.add_method(assembler::method_from_string(R"(
    (method (public static) "LFoo;.baz:()V"
      (
        (return-void)
      )
    )
  )"));
  cc.add_field(DexField::make_field("LFoo;.counter:I")
                   ->make_concrete(ACC_PRIVATE | ACC_STATIC));
  return cc.create();
}

DexStoresVector make_stores(DexClass* cls) {
  DexStoresVector stores;
  DexStore store("classes");
  store.add_classes({cls});
  stores.emplace_back(std::move(store));
  return stores;
}

ConfigFiles make_config() {
  std::istringstream ss(R"({"redex":{"passes":[]}})");
  Json::Value cfg;
  ss >> cfg;
  return ConfigFiles(cfg);
}

// Two static methods where `caller` invokes `callee`, so the override-resolved
// call graph records a real caller edge (exercises caller-set
// capture/interning).
DexClass* create_caller_class() {
  ClassCreator cc(DexType::make_type("LCallers;"));
  cc.set_super(type::java_lang_Object());
  cc.add_method(assembler::method_from_string(R"(
    (method (public static) "LCallers;.callee:()V"
      (
        (return-void)
      )
    )
  )"));
  cc.add_method(assembler::method_from_string(R"(
    (method (public static) "LCallers;.caller:()V"
      (
        (invoke-static () "LCallers;.callee:()V")
        (return-void)
      )
    )
  )"));
  DexClass* cls = cc.create();
  // Mark `caller` a root so the complete call graph includes it (and hence the
  // caller->callee edge); synthetic test methods are otherwise unreachable,
  // which would leave the graph -- and every record's callers -- empty.
  for (auto* m : cls->get_dmethods()) {
    if (show(m).find("caller") != std::string::npos) {
      m->rstate.set_root();
    }
  }
  return cls;
}

// A class whose method carries SourceBlocks across a branch (entry /
// fallthrough / left / join), so capture records per-block anchors and, after
// lower+sync, emit can place block_offsets.
DexClass* create_sb_class() {
  ClassCreator cc(DexType::make_type("LSb;"));
  cc.set_super(type::java_lang_Object());
  cc.add_method(assembler::method_from_string(R"(
    (method (public static) "LSb;.m:()V"
      (
        (.src_block "LSb;.m:()V" 1 (1.0 1.0))
        (const v0 0)
        (if-eqz v0 :left)
        (.src_block "LSb;.m:()V" 3 (1.0 1.0))
        (const v1 1)
        (goto :end)
        (:left)
        (.src_block "LSb;.m:()V" 2 (1.0 1.0))
        (const v1 2)
        (:end)
        (.src_block "LSb;.m:()V" 4 (1.0 1.0))
        (return-void)
      )
    )
  )"));
  // An INSTANCE method too: a non-static method's leading `this` load-param is
  // erase_and_dispose()d by instruction_lowering, so a block anchored on it has
  // no anchor left at sync. Params occupy the highest registers of the frame.
  //
  // The load-param MUST come before the SourceBlock, as it does in real code:
  // check_load_params() reads get_param_instructions(), the PREFIX of
  // fallthrough/load-param entries. A leading MFLOW_SOURCE_BLOCK empties that
  // prefix, so check_load_params returns early without erasing, the `this`
  // load-param is merely retyped in place by remove_opcode, its anchor survives
  // -- and this test is disarmed.
  cc.add_method(assembler::method_from_string(R"(
    (method (public) "LSb;.i:()V"
      (
        (load-param-object v2)
        (.src_block "LSb;.i:()V" 1 (1.0 1.0))
        (const v0 0)
        (if-eqz v0 :ileft)
        (.src_block "LSb;.i:()V" 3 (1.0 1.0))
        (const v1 1)
        (goto :iend)
        (:ileft)
        (.src_block "LSb;.i:()V" 2 (1.0 1.0))
        (const v1 2)
        (:iend)
        (.src_block "LSb;.i:()V" 4 (1.0 1.0))
        (return-void)
      )
    )
  )"));
  return cc.create();
}

// Three looping shapes plus a straight-line method:
//  - nested: an outer counted loop around an inner one;
//  - retry: returns to its header only through a catch handler, so the cycle
//    exists only via a throw edge;
//  - irreducible: a two-block cycle entered at both blocks;
//  - straight: no loop at all.
DexClass* create_loops_class() {
  ClassCreator cc(DexType::make_type("LLoops;"));
  cc.set_super(type::java_lang_Object());
  cc.add_method(assembler::method_from_string(R"(
    (method (public static) "LLoops;.nested:(I)V"
      (
        (load-param v2)
        (const v0 0)
        (:outer)
        (if-ge v0 v2 :done)
        (const v1 0)
        (:inner)
        (if-ge v1 v2 :inner_done)
        (add-int/lit v1 v1 1)
        (goto :inner)
        (:inner_done)
        (add-int/lit v0 v0 1)
        (goto :outer)
        (:done)
        (return-void)
      )
    )
  )"));
  cc.add_method(assembler::method_from_string(R"(
    (method (public static) "LLoops;.retry:()V"
      (
        (const v0 0)
        (:again)
        (.try_start t)
        (invoke-static () "LLoops;.straight:()V")
        (.try_end t)
        (return-void)
        (.catch (t))
        (add-int/lit v0 v0 1)
        (goto :again)
      )
    )
  )"));
  cc.add_method(assembler::method_from_string(R"(
    (method (public static) "LLoops;.irreducible:(I)V"
      (
        (load-param v2)
        (if-eqz v2 :b)
        (:a)
        (add-int/lit v2 v2 1)
        (if-eqz v2 :end)
        (:b)
        (add-int/lit v2 v2 -1)
        (if-nez v2 :a)
        (:end)
        (return-void)
      )
    )
  )"));
  cc.add_method(assembler::method_from_string(R"(
    (method (public static) "LLoops;.straight:()V"
      (
        (return-void)
      )
    )
  )"));
  return cc.create();
}

// Blocks per loop index, from a record's innermost-loop pairs.
std::map<uint32_t, size_t> blocks_per_loop(const dexvt::MethodRecord& rec) {
  std::map<uint32_t, size_t> out;
  for (const auto& [blk, loop] : rec.block_loop) {
    ++out[loop];
  }
  return out;
}

const DexMethod* find_method(DexClass* cls, const std::string& needle) {
  for (auto* m : cls->get_dmethods()) {
    if (show(m).find(needle) != std::string::npos) {
      return m;
    }
  }
  for (auto* m : cls->get_vmethods()) {
    if (show(m).find(needle) != std::string::npos) {
      return m;
    }
  }
  return nullptr;
}

// A try region whose last throwing instruction falls through into code that
// cannot throw. Building a CFG and linearizing it moves that code behind the
// catch handler, and doing it again moves it back, so the layout depends on how
// many round trips the method went through.
DexClass* create_round_trip_class() {
  ClassCreator cc(DexType::make_type("LFlip;"));
  cc.set_super(type::java_lang_Object());
  cc.add_method(assembler::method_from_string(R"(
    (method (public static) "LFlip;.m:(I)V"
      (
        (load-param v1)
        (invoke-static (v1) "LFoo;.f0:(I)V")
        (.try_start c0)
        (invoke-static (v1) "LFoo;.f1:(I)V")
        (add-int/lit v1 v1 5)
        (return-void)
        (.try_end c0)
        (.catch (c0))
        (move-exception v2)
        (throw v2)
      )
    )
  )"));
  return cc.create();
}

} // namespace

class DexVtTest : public RedexTest {};

// The pre-lowering capture produces a record with non-empty disassembly for
// every concrete method (P0.M3).
TEST_F(DexVtTest, capturesRecordsWithDisasm) {
  auto* cls = create_foo_class();
  auto stores = make_stores(cls);
  auto conf = make_config();

  dexvt::Exporter exporter;
  exporter.capture_pre_lowering(stores, conf);

  EXPECT_EQ(exporter.num_captured(), 2u);

  UnorderedSet<uint32_t> ids;
  for (auto* m : cls->get_vmethods()) {
    const auto* rec = exporter.get_record(m);
    ASSERT_NE(rec, nullptr);
    EXPECT_FALSE(rec->disasm.empty());
    ids.insert(rec->id);
  }
  for (auto* m : cls->get_dmethods()) {
    const auto* rec = exporter.get_record(m);
    ASSERT_NE(rec, nullptr);
    EXPECT_FALSE(rec->disasm.empty());
    ids.insert(rec->id);
  }
  // Ids are unique across the captured methods.
  EXPECT_EQ(ids.size(), 2u);
}

TEST_F(DexVtTest, capturesForcedBaselineHot) {
  auto* cls = create_foo_class();
  auto stores = make_stores(cls);
  std::istringstream ss(R"({
    "redex": {"passes": []},
    "baseline_profile": {
      "default": {"use_final_redex_generated_profile": true}
    }
  })");
  Json::Value cfg;
  ss >> cfg;
  ConfigFiles conf(cfg);
  conf.parse_global_config();
  auto* method = cls->get_dmethods().front();
  method->rstate.set_force_hot_in_baseline_profile();
  method->rstate.set_force_startup_in_baseline_profile();

  dexvt::Exporter exporter;
  exporter.capture_pre_lowering(stores, conf);

  const auto* rec = exporter.get_record(method);
  ASSERT_NE(rec, nullptr);
  EXPECT_TRUE(rec->baseline_hot);
  EXPECT_TRUE(rec->baseline_startup);
  EXPECT_FALSE(rec->baseline_post_startup);
}

// The disassembly must be reproducible: byte-identical across independent
// captures and free of the live MethodItemEntry heap pointer that redex's
// show(cfg) embeds on every line ("[0x..]"), which would make the artifact
// non-deterministic and non-diffable. Guards render_disasm (P0).
TEST_F(DexVtTest, disasmIsDeterministicAndPointerFree) {
  auto* cls = create_foo_class();
  auto stores = make_stores(cls);

  auto conf1 = make_config();
  dexvt::Exporter e1;
  e1.capture_pre_lowering(stores, conf1);

  auto conf2 = make_config();
  dexvt::Exporter e2;
  e2.capture_pre_lowering(stores, conf2);

  for (auto* m : cls->get_vmethods()) {
    const auto* r1 = e1.get_record(m);
    const auto* r2 = e2.get_record(m);
    ASSERT_NE(r1, nullptr);
    ASSERT_NE(r2, nullptr);
    EXPECT_EQ(r1->disasm, r2->disasm); // reproducible across runs
    EXPECT_EQ(r1->disasm.find("0x"), std::string::npos); // no heap pointers
    EXPECT_NE(r1->disasm.find("B0"), std::string::npos); // block-structured
  }
}

// Fields are captured as their own records, in the id space after methods.
// create_foo_class has one static field.
TEST_F(DexVtTest, capturesFields) {
  auto* cls = create_foo_class();
  auto stores = make_stores(cls);
  auto conf = make_config();

  dexvt::Exporter exporter;
  exporter.capture_pre_lowering(stores, conf);

  EXPECT_EQ(exporter.num_captured(), 2u); // methods unaffected by the field
  EXPECT_EQ(exporter.num_fields(), 1u);
}

// enhanced_dex_stats_t::operator+= must merge method_size (not only
// class_size), otherwise the accumulated output_totals.method_size stays empty
// and the dexvt size join produces nothing. Guards the load-bearing merge.
TEST_F(DexVtTest, mergesMethodSizesInStats) {
  auto* cls = create_foo_class();
  auto vmethods = cls->get_vmethods();
  auto dmethods = cls->get_dmethods();
  ASSERT_FALSE(vmethods.empty());
  ASSERT_FALSE(dmethods.empty());

  enhanced_dex_stats_t a;
  a.method_size[vmethods[0]] = 10;
  enhanced_dex_stats_t b;
  b.method_size[dmethods[0]] = 20;

  a += b;

  EXPECT_EQ(a.method_size.size(), 2u);
  EXPECT_EQ(a.method_size.at(vmethods[0]), 10u);
  EXPECT_EQ(a.method_size.at(dmethods[0]), 20u);
}

// The override-resolved call graph populates MethodRecord::callers -- the data
// that feeds caller-set interning. `caller` must appear among `callee`'s
// callers.
TEST_F(DexVtTest, capturesCallGraphCallers) {
  auto* cls = create_caller_class();
  auto stores = make_stores(cls);
  auto conf = make_config();

  dexvt::Exporter exporter;
  exporter.capture_pre_lowering(stores, conf);

  const DexMethod* callee = find_method(cls, "callee");
  const DexMethod* caller = find_method(cls, "caller");
  ASSERT_NE(callee, nullptr);
  ASSERT_NE(caller, nullptr);
  const auto* callee_rec = exporter.get_record(callee);
  const auto* caller_rec = exporter.get_record(caller);
  ASSERT_NE(callee_rec, nullptr);
  ASSERT_NE(caller_rec, nullptr);
  ASSERT_NE(callee_rec->callers, nullptr);
  EXPECT_NE(std::find(callee_rec->callers->begin(), callee_rec->callers->end(),
                      caller_rec->id),
            callee_rec->callers->end());
}

// emit() writes schema_version 10, references caller-sets by a `caller_set`
// int, resolves each set through the redex-dexvt.callersets.tsv sidecar, emits
// kind:"class" inheritance records (v5), and omits the loop fields on
// methods without loops (v9).
// Methods with the same callers share one caller list.
TEST_F(DexVtTest, capturesSharedCallerListsOnce) {
  ClassCreator cc(DexType::make_type("LSharedCallers;"));
  cc.set_super(type::java_lang_Object());
  for (const char* callee : {"first", "second"}) {
    cc.add_method(assembler::method_from_string(
        std::string(R"((method (public static) "LSharedCallers;.)") + callee +
        R"(:()V" ((return-void))))"));
  }
  auto* caller = assembler::method_from_string(R"(
    (method (public static) "LSharedCallers;.caller:()V"
      (
        (invoke-static () "LSharedCallers;.first:()V")
        (invoke-static () "LSharedCallers;.second:()V")
        (return-void)
      )
    )
  )");
  caller->rstate.set_root();
  cc.add_method(caller);
  auto* cls = cc.create();
  auto stores = make_stores(cls);
  auto conf = make_config();

  dexvt::Exporter exporter;
  exporter.capture_pre_lowering(stores, conf);

  const auto* first = exporter.get_record(find_method(cls, "first"));
  const auto* second = exporter.get_record(find_method(cls, "second"));
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  ASSERT_NE(first->callers, nullptr);
  EXPECT_EQ(first->callers, second->callers);
  EXPECT_EQ(*first->callers,
            std::vector<uint32_t>{exporter.get_record(caller)->id});
}

TEST_F(DexVtTest, emitInternsCallerSets) {
  auto* cls = create_caller_class();
  auto stores = make_stores(cls);
  auto conf = make_config();

  namespace fs = std::filesystem;
  auto tmp = redex::make_tmp_dir("dexvt_emit_intern%%%%%%%%");
  fs::path dir(tmp.path);
  conf.set_outdir(tmp.path);

  dexvt::Exporter exporter;
  exporter.capture_pre_lowering(stores, conf);
  enhanced_dex_stats_t totals;
  exporter.emit(conf, totals);

  std::ifstream nd((dir / "meta" / "redex-dexvt.ndjson").string());
  ASSERT_TRUE(nd.is_open());
  std::string line;
  ASSERT_TRUE(static_cast<bool>(std::getline(nd, line)));
  Json::Value manifest;
  ASSERT_TRUE(Json::Reader().parse(line, manifest));
  EXPECT_EQ(manifest["schema_version"].asInt(), 10);
  // No method_to_id was passed, so there is no line map key to record.
  EXPECT_FALSE(manifest.isMember("dex_signatures"));
  EXPECT_GE(manifest["callerset_count"].asUInt(), 1u);
  EXPECT_GE(manifest["class_count"].asUInt(), 1u);

  int caller_set = -1;
  bool saw_class = false;
  while (std::getline(nd, line)) {
    Json::Value r;
    ASSERT_TRUE(Json::Reader().parse(line, r));
    EXPECT_FALSE(r.isMember("callers")); // callers are interned, not inlined
    EXPECT_FALSE(r.isMember("loops")); // no loops in this class
    EXPECT_FALSE(r.isMember("block_loop"));
    EXPECT_FALSE(r.isMember("dex_method_idx"));
    if (r.isMember("caller_set")) {
      caller_set = r["caller_set"].asInt();
    }
    if (r.isMember("kind") && r["kind"].asString() == "class") {
      saw_class = true; // v5 emits kind:"class" inheritance records
    }
  }
  ASSERT_GE(caller_set, 0);
  EXPECT_TRUE(saw_class);

  std::ifstream cs((dir / "meta" / "redex-dexvt.callersets.tsv").string());
  ASSERT_TRUE(cs.is_open());
  bool found = false;
  while (std::getline(cs, line)) {
    auto tab = line.find('\t');
    ASSERT_NE(tab, std::string::npos);
    if (std::stoi(line.substr(0, tab)) == caller_set) {
      EXPECT_FALSE(line.substr(tab + 1).empty()); // >=1 caller id
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

namespace {
// Reads the emitted NDJSON: the manifest, and every method record by its
// obfuscated name.
std::pair<Json::Value, std::map<std::string, Json::Value>> read_emitted(
    const std::string& outdir) {
  std::ifstream nd(
      (std::filesystem::path(outdir) / "meta" / "redex-dexvt.ndjson").string());
  std::string line;
  Json::Value manifest;
  std::map<std::string, Json::Value> methods;
  if (std::getline(nd, line)) {
    Json::Reader().parse(line, manifest);
  }
  while (std::getline(nd, line)) {
    Json::Value r;
    Json::Reader().parse(line, r);
    if (r["kind"].asString() == "method") {
      methods[r["obfuscated_name"].asString()] = r;
    }
  }
  return {manifest, methods};
}
} // namespace

// The line maps file a method under DexOutput's method_to_id key,
// (method index << 32) | dex signature. emit() splits it into a per-method
// `dex_method_idx` and one manifest signature per dex tag; methods absent from
// the map get no index.
TEST_F(DexVtTest, emitsLineMapKeyHalves) {
  auto* cls = create_caller_class();
  auto stores = make_stores(cls);
  auto conf = make_config();
  auto tmp = redex::make_tmp_dir("dexvt_emit_key%%%%%%%%");
  conf.set_outdir(tmp.path);

  dexvt::Exporter exporter;
  exporter.capture_pre_lowering(stores, conf);
  auto* callee = const_cast<DexMethod*>(find_method(cls, "LCallers;.callee"));
  ASSERT_NE(callee, nullptr);
  UnorderedMap<DexMethod*, uint64_t> method_to_id;
  method_to_id.emplace(callee, (uint64_t{7} << 32) | 0xfeedbeefu);
  enhanced_dex_stats_t totals;
  exporter.emit(conf, totals, &method_to_id);

  auto [manifest, methods] = read_emitted(tmp.path);
  const auto& dex = methods.at(show(callee))["dex"].asString();
  ASSERT_FALSE(dex.empty());
  EXPECT_EQ(manifest["dex_signatures"][dex].asUInt(), 0xfeedbeefu);
  EXPECT_EQ(manifest["dex_signatures"].size(), 1u);
  EXPECT_EQ(methods.at(show(callee))["dex_method_idx"].asUInt(), 7u);
  const auto* caller = find_method(cls, "LCallers;.caller");
  ASSERT_NE(caller, nullptr);
  EXPECT_FALSE(methods.at(show(caller)).isMember("dex_method_idx"));
}

// Every method of one dex has the same signature. If they disagree, emit()
// records no signature for that dex, so the read side builds no key for its
// methods rather than a wrong one; the indexes are still written.
TEST_F(DexVtTest, dropsSignatureOfDexWithConflictingKeys) {
  auto* cls = create_caller_class();
  auto stores = make_stores(cls);
  auto conf = make_config();
  auto tmp = redex::make_tmp_dir("dexvt_emit_key_conflict%%%%%%%%");
  conf.set_outdir(tmp.path);

  dexvt::Exporter exporter;
  exporter.capture_pre_lowering(stores, conf);
  auto* callee = const_cast<DexMethod*>(find_method(cls, "LCallers;.callee"));
  auto* caller = const_cast<DexMethod*>(find_method(cls, "LCallers;.caller"));
  ASSERT_NE(callee, nullptr);
  ASSERT_NE(caller, nullptr);
  UnorderedMap<DexMethod*, uint64_t> method_to_id;
  method_to_id.emplace(callee, (uint64_t{1} << 32) | 0x11111111u);
  method_to_id.emplace(caller, (uint64_t{2} << 32) | 0x22222222u);
  enhanced_dex_stats_t totals;
  exporter.emit(conf, totals, &method_to_id);

  auto [manifest, methods] = read_emitted(tmp.path);
  EXPECT_FALSE(manifest.isMember("dex_signatures"));
  EXPECT_EQ(methods.at(show(callee))["dex_method_idx"].asUInt(), 1u);
  EXPECT_EQ(methods.at(show(caller))["dex_method_idx"].asUInt(), 2u);
}

// Dex strings are MUTF-8: a supplementary char (here U+1F9D9) is a surrogate
// pair (CESU-8), which is invalid UTF-8 -- the raw bytes would be mangled to
// U+FFFD by the NDJSON writer. render_disasm must decode CONST_STRING operands
// to proper UTF-8.
TEST_F(DexVtTest, disasmDecodesMutf8Strings) {
  const std::string mutf8 = "\xED\xA0\xBE\xED\xB7\x99"; // CESU-8 of U+1F9D9
  const std::string utf8 = "\xF0\x9F\xA7\x99"; // proper UTF-8 of U+1F9D9

  ClassCreator cc(DexType::make_type("LEmoji;"));
  cc.set_super(type::java_lang_Object());
  cc.add_method(assembler::method_from_string(
      "(method (public static) \"LEmoji;.s:()V\" ("
      "(const-string \"" +
      mutf8 +
      "\") "
      "(move-result-pseudo-object v0) "
      "(return-void)))"));
  auto* cls = cc.create();
  auto stores = make_stores(cls);
  auto conf = make_config();

  dexvt::Exporter exporter;
  exporter.capture_pre_lowering(stores, conf);

  const DexMethod* m = find_method(cls, "LEmoji;.s");
  ASSERT_NE(m, nullptr);
  const auto* rec = exporter.get_record(m);
  ASSERT_NE(rec, nullptr);
  EXPECT_NE(rec->disasm.find(utf8), std::string::npos); // decoded to real UTF-8
  EXPECT_EQ(rec->disasm.find("\xED\xA0"),
            std::string::npos); // no raw surrogate bytes
  EXPECT_EQ(rec->disasm.find("\xEF\xBF\xBD"), std::string::npos); // no U+FFFD
}

// emit() places per-block shipped-DEX offsets by resolving each block's
// pre-lowering first-MethodItemEntry anchor against the code-unit offsets the
// BlockOffsetSink records during IRCode::sync -- for EVERY block, not only
// source-blocked ones. Drives the real capture -> lower -> sync -> emit order
// in-process (a plain capture+emit never syncs, so the sink stays empty),
// exercising the anchor's survival across lowering.
TEST_F(DexVtTest, emitsBlockOffsets) {
  block_offset_sink::clear();
  auto* cls = create_sb_class();
  auto stores = make_stores(cls);
  auto conf = make_config();

  namespace fs = std::filesystem;
  auto tmp = redex::make_tmp_dir("dexvt_block_offsets%%%%%%%%");
  fs::path dir(tmp.path);
  conf.set_outdir(tmp.path);

  dexvt::Exporter exporter;
  exporter.capture_pre_lowering(stores,
                                conf); // records anchors, enables the sink
  instruction_lowering::run(stores); // IR -> dex opcodes (SourceBlocks survive)
  // Drive sync so the sink records each SourceBlock's final code-unit offset
  // (the real backend does this inside DexOutput::generate_code_items).
  for (auto* m : cls->get_all_methods()) {
    if (m->get_code() != nullptr) {
      m->get_code()->sync(m);
    }
  }
  enhanced_dex_stats_t totals;
  exporter.emit(conf, totals);

  std::ifstream nd((dir / "meta" / "redex-dexvt.ndjson").string());
  ASSERT_TRUE(nd.is_open());
  std::string line;
  Json::Value method_rec;
  bool found = false;
  bool saw_instance_method = false;
  std::map<std::string, unsigned> min_cu_by_method;
  while (std::getline(nd, line)) {
    Json::Value r;
    ASSERT_TRUE(Json::Reader().parse(line, r));
    if (r["kind"] == "method" && r.isMember("block_offsets")) {
      method_rec = r;
      found = true;
      const std::string name = r["obfuscated_name"].asString();
      if (name.find("LSb;.i:") != std::string::npos) {
        saw_instance_method = true;
      }
      unsigned lo = UINT_MAX;
      for (const auto& pair : r["block_offsets"]) {
        lo = std::min(lo, pair[1u].asUInt());
      }
      min_cu_by_method[name] = lo;
    }
  }
  ASSERT_TRUE(found);

  const Json::Value& bo = method_rec["block_offsets"];
  ASSERT_TRUE(bo.isArray());
  ASSERT_GT(bo.size(), 0u);
  std::vector<unsigned> off_blks;
  unsigned prev_cu = 0;
  for (const auto& pair : bo) {
    ASSERT_EQ(pair.size(), 2u); // [blk, start_cu]
    off_blks.push_back(pair[0u].asUInt());
    // Emitted ascending by (start_cu, blk) to match the read side.
    EXPECT_GE(pair[1u].asUInt(), prev_cu);
    prev_cu = pair[1u].asUInt();
  }
  // Every block that carries hotness must be addressable via block_offsets --
  // and, since v8 anchors every block, so must non-source-blocked blocks, so
  // the offset set is a superset of the (source-blocked) hot set.
  ASSERT_TRUE(method_rec["blocks"].isMember("blk"));
  for (const auto& b : method_rec["blocks"]["blk"]) {
    EXPECT_NE(std::find(off_blks.begin(), off_blks.end(), b.asUInt()),
              off_blks.end())
        << "hot block " << b.asUInt() << " missing from block_offsets";
  }

  // The ENTRY block must be anchored at code-unit 0 for EVERY method that has
  // offsets at all -- static and instance alike. This DOES reproduce the
  // entry-block loss end to end: revert the load-param skip in DexVt.cpp and
  // `LSb;.i:()V` loses its blk-0 row.
  EXPECT_TRUE(saw_instance_method)
      << "fixture must cover an instance method (the regressing case)";
  for (const auto& [name, min_cu] : min_cu_by_method) {
    EXPECT_EQ(min_cu, 0u) << name << ": lowest block_offsets start_cu is "
                          << min_cu << ", so the entry block has no offset";
  }
  block_offset_sink::clear();
}

// Exports `method_body` the way redex_backend does -- optionally
// instruction_lowering::normalize_cfg (lower_with_cfg), the dexvt capture,
// instruction lowering, sync, emit -- and checks that every goto / if-* target
// in the emitted DEX is a recorded block start, which is what `dexvt
// check-anchors` gates publishing on. Returns the emitted instructions.
namespace {

struct EmittedInsn {
  DexOpcode op;
  int32_t offset; // branch offset in code units; 0 for a non-branch
};

std::vector<EmittedInsn> export_and_check_branch_targets(
    const std::string& cls_name,
    const std::string& method_body,
    bool normalize) {
  block_offset_sink::clear();
  ClassCreator cc(DexType::make_type(cls_name));
  cc.set_super(type::java_lang_Object());
  cc.add_method(assembler::method_from_string(method_body));
  auto* cls = cc.create();
  auto stores = make_stores(cls);
  auto conf = make_config();
  auto tmp = redex::make_tmp_dir("dexvt_branch_targets%%%%%%%%");
  conf.set_outdir(tmp.path);

  if (normalize) {
    instruction_lowering::normalize_cfg(stores);
  }
  dexvt::Exporter exporter;
  exporter.capture_pre_lowering(stores, conf);
  instruction_lowering::run(stores);
  std::unique_ptr<DexCode> dex;
  for (auto* m : cls->get_all_methods()) {
    dex = m->get_code()->sync(m);
  }
  enhanced_dex_stats_t totals;
  exporter.emit(conf, totals);

  std::set<unsigned> starts;
  std::ifstream nd(
      (std::filesystem::path(tmp.path) / "meta" / "redex-dexvt.ndjson")
          .string());
  EXPECT_TRUE(nd.is_open());
  std::string line;
  while (std::getline(nd, line)) {
    Json::Value r;
    EXPECT_TRUE(Json::Reader().parse(line, r));
    if (r["kind"] == "method" && r.isMember("block_offsets")) {
      for (const auto& pair : r["block_offsets"]) {
        starts.insert(pair[1u].asUInt());
      }
    }
  }

  std::vector<EmittedInsn> emitted;
  unsigned addr = 0;
  for (auto* insn : dex->get_instructions()) {
    const auto op = insn->opcode();
    const bool is_branch =
        dex_opcode::is_goto(op) || dex_opcode::is_conditional_branch(op);
    if (is_branch) {
      const auto target =
          static_cast<unsigned>(static_cast<int32_t>(addr) + insn->offset());
      EXPECT_TRUE(starts.count(target) != 0)
          << "normalize_cfg=" << normalize << ": " << SHOW(insn) << " at "
          << addr << " targets " << target
          << ", which is no recorded block start";
    }
    emitted.push_back({op, is_branch ? insn->offset() : 0});
    addr += insn->size();
  }
  block_offset_sink::clear();
  return emitted;
}

} // namespace

// A block that branches to itself ships as `nop; if-nez -1`: DEX cannot encode
// a zero branch offset, so IRCode::sync inserts the nop in front of the branch.
// Both branches into the block land on the nop, so the block's start must be
// the nop, not the branch.
TEST_F(DexVtTest, selfBranchingBlockStartsAtTheNopSyncInserts) {
  for (bool normalize : {false, true}) {
    const std::string cls = normalize ? "LSelfCfg;" : "LSelf;";
    auto insns = export_and_check_branch_targets(
        cls,
        "(method (public static) \"" + cls +
            R"(.m:(Ljava/lang/Object;Ljava/lang/Object;)V"
              (
                (load-param-object v1)
                (load-param-object v2)
                (if-eqz v1 :spin)
                (return-void)
                (:spin)
                (if-nez v2 :spin)
                (return-void)
              )
            ))",
        normalize);
    bool saw_nop_before_self_branch = false;
    for (size_t i = 0; i + 1 < insns.size(); ++i) {
      saw_nop_before_self_branch |= insns[i].op == DOPCODE_NOP &&
                                    insns[i + 1].op == DOPCODE_IF_NEZ &&
                                    insns[i + 1].offset == -1;
    }
    EXPECT_TRUE(saw_nop_before_self_branch)
        << "normalize_cfg=" << normalize
        << ": fixture did not produce `nop; if-nez -1`";
  }
}

// An empty loop (`while (true) {}`) is a block with no IR instruction: the CFG
// turns its goto into an edge. It still ships as code -- `nop; goto -1`, the
// nop because DEX cannot encode a zero branch offset -- so it must be a block
// start, and branches into it land on the nop.
TEST_F(DexVtTest, emptyLoopBlockStartsAtTheNopSyncInserts) {
  for (bool normalize : {false, true}) {
    const std::string cls = normalize ? "LSpinCfg;" : "LSpin;";
    auto insns =
        export_and_check_branch_targets(cls,
                                        "(method (public static) \"" + cls +
                                            R"(.m:(Ljava/lang/Object;)V"
              (
                (load-param-object v1)
                (if-eqz v1 :spin)
                (return-void)
                (:spin)
                (goto :spin)
              )
            ))",
                                        normalize);
    bool saw_nop_before_self_goto = false;
    for (size_t i = 0; i + 1 < insns.size(); ++i) {
      saw_nop_before_self_goto |= insns[i].op == DOPCODE_NOP &&
                                  insns[i + 1].op == DOPCODE_GOTO &&
                                  insns[i + 1].offset == -1;
    }
    EXPECT_TRUE(saw_nop_before_self_goto)
        << "normalize_cfg=" << normalize
        << ": fixture did not produce `nop; goto -1`";
  }
}

// An if-* whose target is out of 16-bit range ships as
// `if-<inverted> skip; goto/32 target`, with the inverted if-* inserted in
// front. When that if-* leads a block something branches to, the block starts
// at the inverted if-*.
TEST_F(DexVtTest, blockLedByALongConditionalBranchStartsAtItsFirstInstruction) {
  for (bool normalize : {false, true}) {
    const std::string cls = normalize ? "LLongCfg;" : "LLong;";
    std::string body = "(method (public static) \"" + cls + R"(.m:(I)V"
      (
        (load-param v1)
        (const v0 1)
        (:back)
        (if-eqz v0 :far)
    )";
    // Each `const v0 <32-bit literal>` is 3 code units; 12000 of them put
    // `:far` beyond the 32767 code units an if-* can reach.
    for (int i = 0; i < 12000; ++i) {
      body += "(const v0 305419896)\n";
    }
    body += R"(
        (return-void)
        (:far)
        (if-nez v1 :back)
        (return-void)
      )
    ))";
    auto insns = export_and_check_branch_targets(cls, body, normalize);
    EXPECT_TRUE(std::any_of(
        insns.begin(), insns.end(),
        [](const auto& insn) { return insn.op == DOPCODE_GOTO_32; }))
        << "normalize_cfg=" << normalize << ": fixture did not need a goto/32";
  }
}

// Capturing must not touch the code it describes: one more CFG round trip
// would ship the other layout of a method like this one, and only in builds
// that emit dexvt.
TEST_F(DexVtTest, captureLeavesCodeUntouched) {
  auto* cls = create_round_trip_class();
  auto* code = cls->get_dmethods().front()->get_code();
  const auto before = assembler::to_string(code);

  // The fixture is armed: a bare round trip does change its layout.
  {
    IRCode probe(*code);
    probe.build_cfg();
    probe.clear_cfg();
    ASSERT_NE(assembler::to_string(&probe), before);
  }

  auto stores = make_stores(cls);
  auto conf = make_config();
  dexvt::Exporter exporter;
  exporter.capture_pre_lowering(stores, conf);

  EXPECT_EQ(assembler::to_string(code), before);
  EXPECT_FALSE(code->cfg_built());
  block_offset_sink::clear();
}

// The outer loop encloses the inner one: the outer is listed first with no
// parent, the inner names it as parent, and each looping block maps to its
// INNERMOST loop -- the two inner blocks to the inner loop, the outer header,
// the inner loop's preheader and the outer latch to the outer loop.
TEST_F(DexVtTest, capturesNestedLoops) {
  auto* cls = create_loops_class();
  auto stores = make_stores(cls);
  auto conf = make_config();

  dexvt::Exporter exporter;
  exporter.capture_pre_lowering(stores, conf);

  const auto* rec = exporter.get_record(find_method(cls, "LLoops;.nested"));
  ASSERT_NE(rec, nullptr);
  ASSERT_EQ(rec->loops.size(), 2u) << rec->disasm;
  EXPECT_EQ(rec->loops[0].parent, -1);
  EXPECT_EQ(rec->loops[1].parent, 0);
  EXPECT_NE(rec->loops[0].header_blk, rec->loops[1].header_blk);
  auto per_loop = blocks_per_loop(*rec);
  EXPECT_EQ(per_loop[0], 3u) << rec->disasm;
  EXPECT_EQ(per_loop[1], 2u) << rec->disasm;
  // Each header is a block of its own loop, not of a deeper one.
  for (uint32_t i = 0; i < rec->loops.size(); ++i) {
    auto it = std::find_if(
        rec->block_loop.begin(), rec->block_loop.end(),
        [&](const auto& p) { return p.first == rec->loops[i].header_blk; });
    ASSERT_NE(it, rec->block_loop.end());
    EXPECT_EQ(it->second, i);
  }
  EXPECT_TRUE(std::is_sorted(rec->block_loop.begin(), rec->block_loop.end()));
}

// A retry loop cycles only through the throw edge into its catch handler. It
// re-executes code, so it is a loop -- the same answer SyntheticBlockCountsPass
// gets from LoopInfo.
TEST_F(DexVtTest, capturesLoopThroughThrowEdge) {
  auto* cls = create_loops_class();
  auto stores = make_stores(cls);
  auto conf = make_config();

  dexvt::Exporter exporter;
  exporter.capture_pre_lowering(stores, conf);

  const auto* rec = exporter.get_record(find_method(cls, "LLoops;.retry"));
  ASSERT_NE(rec, nullptr);
  ASSERT_EQ(rec->loops.size(), 1u) << rec->disasm;
  EXPECT_EQ(rec->loops[0].parent, -1);
  EXPECT_NE(rec->disasm.find("throw"), std::string::npos) << rec->disasm;
}

// A cycle entered at two blocks has no dominating header. LoopInfo still
// reports it as one loop, so dexvt does too.
TEST_F(DexVtTest, capturesIrreducibleCycleAsOneLoop) {
  auto* cls = create_loops_class();
  auto stores = make_stores(cls);
  auto conf = make_config();

  dexvt::Exporter exporter;
  exporter.capture_pre_lowering(stores, conf);

  const auto* rec =
      exporter.get_record(find_method(cls, "LLoops;.irreducible"));
  ASSERT_NE(rec, nullptr);
  ASSERT_EQ(rec->loops.size(), 1u) << rec->disasm;
  EXPECT_EQ(blocks_per_loop(*rec)[0], 2u) << rec->disasm;
}

TEST_F(DexVtTest, straightLineMethodHasNoLoops) {
  auto* cls = create_loops_class();
  auto stores = make_stores(cls);
  auto conf = make_config();

  dexvt::Exporter exporter;
  exporter.capture_pre_lowering(stores, conf);

  const auto* rec = exporter.get_record(find_method(cls, "LLoops;.straight"));
  ASSERT_NE(rec, nullptr);
  EXPECT_TRUE(rec->loops.empty());
  EXPECT_TRUE(rec->block_loop.empty());
}

// Two independent captures record identical loops, and emit() writes them in
// the columnar shape: `loops.header` / `loops.parent` (null for an outermost
// loop) and `block_loop` pairs, matching the record.
TEST_F(DexVtTest, emitsLoopsDeterministically) {
  auto* cls = create_loops_class();
  auto stores = make_stores(cls);

  auto conf1 = make_config();
  dexvt::Exporter e1;
  e1.capture_pre_lowering(stores, conf1);
  auto conf2 = make_config();
  dexvt::Exporter e2;
  e2.capture_pre_lowering(stores, conf2);
  for (auto* m : cls->get_all_methods()) {
    const auto* r1 = e1.get_record(m);
    const auto* r2 = e2.get_record(m);
    ASSERT_NE(r1, nullptr);
    ASSERT_NE(r2, nullptr);
    ASSERT_EQ(r1->loops.size(), r2->loops.size());
    for (size_t i = 0; i < r1->loops.size(); ++i) {
      EXPECT_EQ(r1->loops[i].header_blk, r2->loops[i].header_blk);
      EXPECT_EQ(r1->loops[i].parent, r2->loops[i].parent);
    }
    EXPECT_EQ(r1->block_loop, r2->block_loop);
  }

  namespace fs = std::filesystem;
  auto tmp = redex::make_tmp_dir("dexvt_emit_loops%%%%%%%%");
  fs::path dir(tmp.path);
  conf1.set_outdir(tmp.path);
  enhanced_dex_stats_t totals;
  e1.emit(conf1, totals);

  const auto* nested = e1.get_record(find_method(cls, "LLoops;.nested"));
  ASSERT_NE(nested, nullptr);
  std::ifstream nd((dir / "meta" / "redex-dexvt.ndjson").string());
  ASSERT_TRUE(nd.is_open());
  std::string line;
  bool found = false;
  while (std::getline(nd, line)) {
    Json::Value r;
    ASSERT_TRUE(Json::Reader().parse(line, r));
    if (r["obfuscated_name"].asString().find("LLoops;.nested:") ==
        std::string::npos) {
      continue;
    }
    found = true;
    const Json::Value& header = r["loops"]["header"];
    const Json::Value& parent = r["loops"]["parent"];
    ASSERT_EQ(header.size(), nested->loops.size());
    ASSERT_EQ(parent.size(), nested->loops.size());
    EXPECT_TRUE(parent[0u].isNull());
    EXPECT_EQ(parent[1u].asInt(), 0);
    for (Json::ArrayIndex i = 0; i < header.size(); ++i) {
      EXPECT_EQ(header[i].asUInt(), nested->loops[i].header_blk);
    }
    const Json::Value& bl = r["block_loop"];
    ASSERT_EQ(bl.size(), nested->block_loop.size());
    for (Json::ArrayIndex i = 0; i < bl.size(); ++i) {
      EXPECT_EQ(bl[i][0u].asUInt(), nested->block_loop[i].first);
      EXPECT_EQ(bl[i][1u].asUInt(), nested->block_loop[i].second);
    }
  }
  EXPECT_TRUE(found);
}

namespace {
// `(:H<l>) if-ge -> exit; <body>; inc; goto H<l>; (:X<l>)` with counter v<reg>.
std::string counted_loop(const std::string& label,
                         int reg,
                         const std::string& body) {
  const std::string v = "v" + std::to_string(reg);
  return "(const " + v + " 0)(:H" + label + ")(if-ge " + v + " v15 :X" + label +
         ")" + body + "(add-int/lit " + v + " " + v + " 1)(goto :H" + label +
         ")(:X" + label + ")";
}
} // namespace

// A root loop holding two loops that each hold two loops: seven loops, depths
// 1/2/2/3/3/3/3, each depth-3 loop parented by its own depth-2 loop, and every
// parent listed before its children. Many identical methods give hash order
// every chance to differ (as it does under -c redex.perturb_unordered=true).
TEST_F(DexVtTest, nestsSiblingLoopsUnderTheirOwnParent) {
  ClassCreator cc(DexType::make_type("LSiblings;"));
  cc.set_super(type::java_lang_Object());
  const std::string a = counted_loop(
      "A", 1, counted_loop("a1", 2, "") + counted_loop("a2", 2, ""));
  const std::string b = counted_loop(
      "B", 1, counted_loop("b1", 2, "") + counted_loop("b2", 2, ""));
  constexpr int kMethods = 200;
  for (int i = 0; i < kMethods; ++i) {
    cc.add_method(assembler::method_from_string(
        "(method (public static) \"LSiblings;.m" + std::to_string(i) +
        ":(I)V\" ((load-param v15)" + counted_loop("R", 0, a + b) +
        "(return-void)))"));
  }
  auto* cls = cc.create();
  auto stores = make_stores(cls);
  auto conf = make_config();

  dexvt::Exporter exporter;
  exporter.capture_pre_lowering(stores, conf);

  for (auto* m : cls->get_all_methods()) {
    const auto* rec = exporter.get_record(m);
    ASSERT_NE(rec, nullptr);
    ASSERT_EQ(rec->loops.size(), 7u) << rec->disasm;
    std::vector<int> depth(rec->loops.size());
    std::map<int, int> per_depth;
    for (size_t i = 0; i < rec->loops.size(); ++i) {
      const int parent = rec->loops[i].parent;
      ASSERT_LT(parent, static_cast<int>(i)) << "parent must precede child";
      depth[i] = parent < 0 ? 1 : depth[parent] + 1;
      ++per_depth[depth[i]];
    }
    EXPECT_EQ(per_depth, (std::map<int, int>{{1, 1}, {2, 2}, {3, 4}}))
        << show(m);
    // The root and each depth-2 loop have exactly two children; leaves none.
    std::map<int, int> children;
    for (const auto& loop : rec->loops) {
      if (loop.parent >= 0) {
        ++children[loop.parent];
      }
    }
    for (size_t i = 0; i < rec->loops.size(); ++i) {
      EXPECT_EQ(children[static_cast<int>(i)], depth[i] == 3 ? 0 : 2)
          << show(m) << " loop " << i;
    }
  }
}

// The inner loop's header comes first in the code (lower block id) but is
// still nested inside the outer loop, which is entered by a forward goto.
// Ordering must follow depth, not header id.
TEST_F(DexVtTest, ordersLoopsByDepthNotHeaderId) {
  ClassCreator cc(DexType::make_type("LBackwards;"));
  cc.set_super(type::java_lang_Object());
  cc.add_method(assembler::method_from_string(R"(
    (method (public static) "LBackwards;.m:(I)V"
      (
        (load-param v2)
        (const v0 0)
        (goto :outer)
        (:inner)
        (if-ge v1 v2 :inner_done)
        (add-int/lit v1 v1 1)
        (goto :inner)
        (:inner_done)
        (add-int/lit v0 v0 1)
        (:outer)
        (if-ge v0 v2 :done)
        (const v1 0)
        (goto :inner)
        (:done)
        (return-void)
      )
    )
  )"));
  auto* cls = cc.create();
  auto stores = make_stores(cls);
  auto conf = make_config();

  dexvt::Exporter exporter;
  exporter.capture_pre_lowering(stores, conf);

  const auto* rec = exporter.get_record(find_method(cls, "LBackwards;.m"));
  ASSERT_NE(rec, nullptr);
  ASSERT_EQ(rec->loops.size(), 2u) << rec->disasm;
  EXPECT_EQ(rec->loops[0].parent, -1);
  EXPECT_EQ(rec->loops[1].parent, 0);
  EXPECT_LT(rec->loops[1].header_blk, rec->loops[0].header_blk)
      << "fixture must put the inner header first\n"
      << rec->disasm;
}

namespace {

// Dex strings are MUTF-8: U+1F600 and U+1F601 are surrogate pairs there,
// four-byte sequences in UTF-8.
const std::string kMutfA = "\xed\xa0\xbd\xed\xb8\x80";
const std::string kMutfB = "\xed\xa0\xbd\xed\xb8\x81";
const std::string kUtfA = "\xf0\x9f\x98\x80";
const std::string kUtfB = "\xf0\x9f\x98\x81";

// Emits a class whose method kMutfA calls kMutfB inside a try block caught by
// type L<kMutfA>;, and returns the exported method records.
std::vector<Json::Value> emit_unicode_methods(bool facts) {
  ClassCreator cc(DexType::make_type("LUnicode;"));
  cc.set_super(type::java_lang_Object());
  cc.add_method(assembler::method_from_string(
      "(method (public static) \"LUnicode;." + kMutfA +
      ":()V\" ("
      "(.try_start a) (invoke-static () \"LUnicode;." +
      kMutfB +
      ":()V\")"
      "(.try_end a) (return-void) (.catch (a) \"L" +
      kMutfA +
      ";\")"
      "(move-exception v0) (throw v0)))"));
  cc.add_method(
      assembler::method_from_string("(method (public static) \"LUnicode;." +
                                    kMutfB + ":()V\" ((return-void)))"));
  auto* cls = cc.create();
  auto stores = make_stores(cls);
  Json::Value config;
  config["emit_dexvt_facts"] = facts;
  ConfigFiles conf(config);
  auto tmp = redex::make_tmp_dir("dexvt_unicode%%%%%%%%");
  conf.set_outdir(tmp.path);
  dexvt::Exporter exporter;
  exporter.capture_pre_lowering(stores, conf);
  enhanced_dex_stats_t sizes;
  exporter.emit(conf, sizes);
  std::ifstream input(conf.metafile("redex-dexvt.ndjson"));
  std::string line;
  std::vector<Json::Value> methods;
  while (std::getline(input, line)) {
    Json::Value r;
    EXPECT_TRUE(Json::Reader().parse(line, r));
    if (r["kind"].asString() == "method") {
      methods.push_back(r);
    }
  }
  return methods;
}

} // namespace

TEST_F(DexVtTest, unicodeNamesAreUtf8InTheExport) {
  std::set<std::string> names;
  bool call_found = false;
  for (const auto& r : emit_unicode_methods(/* facts */ false)) {
    names.insert(r["obfuscated_name"].asString());
    call_found |= r["disasm"].asString().find("LUnicode;." + kUtfB + ":()V") !=
                  std::string::npos;
    EXPECT_FALSE(r.isMember("facts"));
  }
  EXPECT_EQ(names, (std::set<std::string>{"LUnicode;." + kUtfA + ":()V",
                                          "LUnicode;." + kUtfB + ":()V"}));
  EXPECT_TRUE(call_found);
}
