/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RemoveRecursiveLocks.h"

#include <bit>
#include <bitset>
#include <iostream>
#include <variant>

#include <sparta/ConstantAbstractDomain.h>
#include <sparta/PatriciaTreeMapAbstractEnvironment.h>

#include "BaseIRAnalyzer.h"
#include "CFGMutation.h"
#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexUtil.h"
#include "IRInstruction.h"
#include "MethodProfiles.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "ReachingDefinitions.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"

namespace {

using namespace cfg;

constexpr bool kDebugPass = false;

// The pass attempts to remove recursive locks which may for example be exposed
// by inlining of synchronized methods.
//
// For simple and safe removal, a method needs to be correct wrt/ structured
// locking, i.e., locks need to come in pairs and need to be correctly nested.
// In that case, tracking the lock depth allows a simple decision on whether to
// remove the lock operations.
//
// The datastructures are similar to the Android verifier: locking is tracked as
// a virtual stack, where each "source" has a "stack" of bits defining whether
// it is locked at that level. A key difference is that no alias tracking is
// done. Instead, a reaching-definitions analysis is run beforehand to derive
// the (single) "source" for each monitor instruction.
//
//   Program-State: Lock-Object(as Instruction*) x Lock-State
//   Lock-State:    Bit-Stack(as int)
//   Sample meaning:
//    0=unlocked,
//    1=0b01 = locked first
//    2=0b10 = locked second
//    3=0b11 = locked first and second = recursively locked

namespace analysis {

// At what levels of the virtual stack is the corresponding
// object locked? This limits the analysis to a nesting depth,
// but this is normally enough, and corresponds to Android's
// verifier.
using LockType = uint32_t;
using LockDepths = sparta::ConstantAbstractDomain<LockType>;
constexpr size_t kMaxLockDepth = sizeof(LockType) * 8;

// It would be nice to have an environment that is automatically TOP
// if any element is. However, wiring that up seems nontrivial. So
// this is another test in the `check` function.
using LockEnvironment =
    sparta::PatriciaTreeMapAbstractEnvironment<const IRInstruction*,
                                               LockDepths>;

size_t clz(LockType val) {
  static_assert(sizeof(val) == 4 || sizeof(val) == 8, "Unsupported type");
  return std::countl_zero(val);
}

size_t get_max_depth(LockType val) {
  if (val != 0) {
    return kMaxLockDepth - clz(val);
  }
  return 0;
}

size_t get_max_depth(const LockEnvironment& env) {
  if (env.is_top() || env.is_bottom()) {
    return 0;
  }
  size_t max = 0;
  for (const auto& p : env.bindings()) {
    if (p.second.is_value()) {
      max = std::max(max, get_max_depth(*p.second.get_constant()));
    }
  }
  return max;
}

// Computes the number of recursive locks.
size_t get_per(LockType val) {
  // Use bitset. It should generate the optimal architectural instruction.
  return std::bitset<kMaxLockDepth>(val).count();
}

// Computes the maximum number of recursive locks.
size_t get_max_depth_per(const LockEnvironment& env) {
  if (env.is_top() || env.is_bottom()) {
    return 0;
  }
  size_t max = 0;
  for (const auto& p : env.bindings()) {
    if (p.second.is_value()) {
      max = std::max(max, get_per(*p.second.get_constant()));
    }
  }
  return max;
}

// Very simplistic check.
// We could do more integrity checks, e.g., no two instructions are locked at
// the same depth, there are no holes, ...
bool is_valid(const LockEnvironment& env, size_t expected_count) {
  return env.bindings().size() == expected_count;
}

// Map a lock operation to the instruction defining the object to be locked on.
using RDefs = UnorderedMap<const IRInstruction*, const IRInstruction*>;

struct LocksIterator : public ir_analyzer::BaseIRAnalyzer<LockEnvironment> {
  LocksIterator(const cfg::ControlFlowGraph& cfg, const RDefs& rdefs)
      : ir_analyzer::BaseIRAnalyzer<LockEnvironment>(cfg), rdefs(rdefs) {}

  // Edges are complicated. For MONITOR_ENTER, they indicate the operation
  // did not actually succeed, so the counted lock must be undone. For
  // MONITOR_EXIT, however, Android handles this as not-throwing at all,
  // so the edge needs to be overwritten completely.
  LockEnvironment analyze_edge(
      const cfg::GraphInterface::EdgeId& e,
      const LockEnvironment& exit_state_at_source) const override {
    if (!exit_state_at_source.is_value()) {
      return exit_state_at_source;
    }
    if (e->type() != EDGE_THROW) {
      return exit_state_at_source;
    }
    // Check whether this is a throw with a MONITOR_ENTER. We'd need
    // to undo the modification then.
    const IRInstruction* monitor_insn;
    {
      auto* src = e->src();
      auto last_it = src->get_last_insn();
      if (last_it == src->end()) {
        return exit_state_at_source;
      }

      if (!opcode::is_a_monitor(last_it->insn->opcode())) {
        return exit_state_at_source;
      }
      monitor_insn = last_it->insn;
    }

    auto it = rdefs.find(monitor_insn);
    if (it == rdefs.end()) {
      // Uh-oh. Something is wrong, maybe was non-singleton reachable.
      return LockEnvironment(sparta::AbstractValueKind::Top);
    }

    const auto* def = it->second;
    const auto& def_state = exit_state_at_source.get(def);
    if (def_state.is_top() || def_state.is_bottom()) {
      // Uh-oh. Something is wrong.
      return LockEnvironment(sparta::AbstractValueKind::Top);
    }

    LockType locks = *def_state.get_constant();
    size_t max_all_d = get_max_depth(exit_state_at_source);

    if (monitor_insn->opcode() == OPCODE_MONITOR_EXIT) {
      // A monitor exit is not actually handled as throwing. See
      // https://cs.android.com/android/platform/superproject/+/android-4.0.4_r2.1:dalvik/vm/analysis/CodeVerify.cpp;l=4146
      //
      // As such, pretend this edge isn't there.
      return LockEnvironment(sparta::AbstractValueKind::Bottom);
    }

    size_t max_d = get_max_depth(locks);
    if (max_d == 0 || max_all_d != max_d) {
      // Uh-oh. Something is wrong.
      return LockEnvironment(sparta::AbstractValueKind::Top);
    }

    // OK, undo and return.
    LockType new_locks = locks ^ (1 << (max_d - 1));
    always_assert_log(
        new_locks < locks, "%u x %zu -> %u", locks, max_d, new_locks);
    auto ret = exit_state_at_source;
    ret.set(def, LockDepths(new_locks));
    return ret;
  }

  void analyze_instruction(const IRInstruction* insn,
                           LockEnvironment* current_state) const override {
    if (!opcode::is_a_monitor(insn->opcode())) {
      return;
    }
    if (!current_state->is_value()) {
      return;
    }

    auto it = rdefs.find(insn);
    if (it == rdefs.end()) {
      // Something's bad.
      current_state->set_to_top();
      return;
    }
    const auto* def = it->second;
    auto def_state = current_state->get(def);
    size_t max_d = get_max_depth(*current_state);

    if (insn->opcode() == OPCODE_MONITOR_ENTER) {
      if (max_d == kMaxLockDepth) {
        // Oh well...
        current_state->set_to_top();
        return;
      }
      LockType base = def_state.is_value() ? *def_state.get_constant() : 0;
      current_state->set(def, LockDepths(base | (1 << max_d)));
      return;
    }

    if (!def_state.is_value()) {
      // Uh-oh.
      current_state->set_to_top();
      return;
    }
    LockType old = *def_state.get_constant();
    size_t max_old_d = get_max_depth(old);
    if (old == 0 || max_old_d != max_d) {
      // Uh-oh.
      current_state->set_to_top();
      return;
    }

    LockType new_locks = old ^ (1 << (max_old_d - 1));
    always_assert_log(new_locks < old, "%u x %zu -> %u", old, max_d, new_locks);
    current_state->set(def, LockDepths(new_locks));
  }

  const RDefs& rdefs;
};

struct ComputeRDefsResult {
  RDefs rdefs;
  bool has_locks;
  bool failure;

  ComputeRDefsResult(bool has_locks, bool failure)
      : has_locks(has_locks), failure(failure) {}

  operator bool() const { // NOLINT(google-explicit-constructor)
    return has_locks && !failure;
  }
};

ComputeRDefsResult compute_rdefs(ControlFlowGraph& cfg) {
  std::unique_ptr<reaching_defs::MoveAwareFixpointIterator> rdefs;
  auto get_defs = [&](Block* b, const IRInstruction* i) {
    if (!rdefs) {
      rdefs.reset(new reaching_defs::MoveAwareFixpointIterator(cfg));
      rdefs->run(reaching_defs::Environment());
    }
    auto defs_in = rdefs->get_entry_state_at(b);
    for (const auto& it : ir_list::InstructionIterable{b}) {
      if (it.insn == i) {
        break;
      }
      rdefs->analyze_instruction(it.insn, &defs_in);
    }
    return defs_in;
  };
  auto get_singleton = [](auto& defs, reg_t reg) -> IRInstruction* {
    const auto& defs0 = defs.get(reg);
    if (defs0.is_top() || defs0.is_bottom()) {
      return nullptr;
    }
    if (defs0.elements().size() != 1) {
      return nullptr;
    }
    return *defs0.elements().begin();
  };

  UnorderedMap<const IRInstruction*, Block*> block_map;
  auto get_rdef = [&](IRInstruction* insn, reg_t reg) -> IRInstruction* {
    auto it = block_map.find(insn);
    redex_assert(it != block_map.cend());
    auto defs = get_defs(it->second, insn);
    return get_singleton(defs, reg);
  };

  auto print_rdefs = [&](IRInstruction* insn, reg_t reg) -> std::string {
    auto it = block_map.find(insn);
    redex_assert(it != block_map.cend());
    auto defs = get_defs(it->second, insn);
    const auto& defs0 = defs.get(reg);
    if (defs0.is_top()) {
      return "top";
    }
    if (defs0.is_bottom()) {
      return "bottom";
    }
    std::ostringstream oss;
    oss << "{";
    for (auto* i : defs0.elements()) {
      oss << ", " << show(i);
    }
    oss << "}";
    return oss.str();
  };

  std::vector<IRInstruction*> monitor_insns;
  for (auto* b : cfg.blocks()) {
    for (auto& mie : *b) {
      if (mie.type != MFLOW_OPCODE) {
        continue;
      }
      block_map.emplace(mie.insn, b);
      if (opcode::is_a_monitor(mie.insn->opcode())) {
        monitor_insns.push_back(mie.insn);
      }
    }
  }

  if (monitor_insns.empty()) {
    // This is possible if the IRCode check found instructions in
    // unreachable code.
    return ComputeRDefsResult(/*has_locks=*/false, /*failure=*/false);
  }

  ComputeRDefsResult ret(/*has_locks=*/true, /*failure=*/false);

  // Check that there is at most one monitor instruction per block.
  // We use that simplification later to not have to walk through
  // blocks.
  {
    UnorderedSet<Block*> seen_blocks;
    for (auto* monitor_insn : monitor_insns) {
      auto* b = block_map.at(monitor_insn);
      if (seen_blocks.count(b) > 0) {
        ret.failure = true;
        return ret;
      }
      seen_blocks.insert(b);
    }
  }

  for (auto* monitor_insn : monitor_insns) {
    auto find_root_def = [&](IRInstruction* cur) -> IRInstruction* {
      for (;;) {
        IRInstruction* next;
        switch (cur->opcode()) {
        case OPCODE_MONITOR_ENTER:
        case OPCODE_MONITOR_EXIT:
        // Ignore check-cast, go further.
        case OPCODE_CHECK_CAST:
          next = get_rdef(cur, cur->src(0));
          break;

        default:
          return cur;
        }
        if (next == nullptr) {
          if (kDebugPass || traceEnabled(LOCKS, 4)) {
            std::cerr << show(cur) << " has non-singleton rdefs "
                      << print_rdefs(cur, cur->src(0)) << '\n';
          }
          return nullptr;
        }
        cur = next;
      }
    };

    auto* root_rdef = find_root_def(monitor_insn);
    if (root_rdef == nullptr) {
      ret.failure = true;
      return ret;
    }
    ret.rdefs.emplace(monitor_insn, root_rdef);
  }

  return ret;
}

LockEnvironment create_start(const RDefs& rdefs) {
  redex_assert(!rdefs.empty());
  LockEnvironment env;
  for (const auto& p : UnorderedIterable(rdefs)) {
    env.set(p.second, LockDepths(0));
  }
  return env;
}

} // namespace analysis

// Return `true` if this is an interesting method.
std::variant<bool, std::pair<size_t, size_t>> check(
    analysis::LocksIterator& iter,
    ControlFlowGraph& cfg,
    size_t sources_count) {
  size_t max_d = 0;
  size_t max_same = 0;
  for (auto* b : cfg.blocks()) {
    const auto& state = iter.get_entry_state_at(b);
    if (state.is_top()) {
      return false;
    }
    if (state.is_value()) {
      if (!analysis::is_valid(state, sources_count)) {
        return false;
      }
    }
    max_d = std::max(max_d, analysis::get_max_depth(state));
    max_same = std::max(max_same, analysis::get_max_depth_per(state));
  }
  return std::make_pair(max_d, max_same);
}

// Debug helper. Print CFG and after it a list of states.
void print(std::ostream& os,
           const analysis::RDefs& rdefs,
           analysis::LocksIterator& iter,
           ControlFlowGraph& cfg) {
  os << show(cfg) << '\n';
  for (const auto& p : UnorderedIterable(rdefs)) {
    os << " # " << p.first << " -> " << p.second << '\n';
  }
  os << '\n';
  for (auto* b : cfg.blocks()) {
    os << " * B" << b->id() << ": ";

    auto print_state = [&os](const auto& state) {
      if (state.is_bottom()) {
        os << "bot";
      } else if (state.is_top()) {
        os << "top";
      } else {
        for (const auto& p : state.bindings()) {
          os << " " << p.first << "=";
          if (p.second.is_bottom()) {
            os << "bot";
          } else if (p.second.is_top()) {
            os << "top";
          } else {
            os << *p.second.get_constant();
          }
        }
      }
    };

    auto entry_state = iter.get_entry_state_at(b);
    print_state(entry_state);
    os << " ===> ";

    for (const auto& it : ir_list::InstructionIterable{b}) {
      iter.analyze_instruction(it.insn, &entry_state);
    }
    print_state(entry_state);
    os << " (";
    print_state(iter.get_exit_state_at(b));
    os << ")\n    ";
    {
      analysis::LockEnvironment env(sparta::AbstractValueKind::Bottom);
      print_state(env);
      for (auto* edge : GraphInterface::predecessors(cfg, b)) {
        const auto& prev_exit =
            iter.get_exit_state_at(GraphInterface::source(cfg, edge));
        auto analyzed = iter.analyze_edge(edge, prev_exit);
        env.join_with(analyzed);
        os << " =(" << edge->src()->id() << "=";
        print_state(prev_exit);
        os << "->";
        print_state(analyzed);
        os << ")=> ";
        print_state(env);
      }
    }
    os << '\n';
  }
}

struct AnalysisResult {
  AnalysisResult() = default;
  AnalysisResult(AnalysisResult&& other) noexcept
      : rdefs(std::move(other.rdefs)),
        iter(std::move(other.iter)),
        method_with_locks(other.method_with_locks),
        non_singleton_rdefs(other.non_singleton_rdefs),
        method_with_issues(other.method_with_issues),
        max_d(other.max_d),
        max_same(other.max_same) {}

  AnalysisResult& operator=(AnalysisResult&& rhs) noexcept {
    rdefs = std::move(rhs.rdefs);
    iter = std::move(rhs.iter);
    method_with_locks = rhs.method_with_locks;
    non_singleton_rdefs = rhs.non_singleton_rdefs;
    method_with_issues = rhs.method_with_issues;
    max_d = rhs.max_d;
    max_same = rhs.max_same;
    return *this;
  }

  analysis::RDefs rdefs;
  std::unique_ptr<analysis::LocksIterator> iter;

  bool method_with_locks{false};
  bool non_singleton_rdefs{false};
  bool method_with_issues{false};

  size_t max_d{0};
  size_t max_same{0};
};

AnalysisResult analyze(ControlFlowGraph& cfg) {
  AnalysisResult ret;
  // 2) Run ReachingDefs.
  auto rdefs_res = analysis::compute_rdefs(cfg);
  if (!rdefs_res) {
    if (rdefs_res.failure) {
      ret.method_with_locks = true;
      ret.non_singleton_rdefs = true;
    }
    return ret;
  }

  ret.method_with_locks = true;
  ret.rdefs = std::move(rdefs_res.rdefs);
  // Possible with unreachable code.
  if (ret.rdefs.empty()) {
    ret.method_with_locks = false;
    return ret;
  }

  // 3) Run our iterator.
  ret.iter = std::make_unique<analysis::LocksIterator>(cfg, ret.rdefs);
  size_t sources_count;
  {
    auto env = analysis::create_start(ret.rdefs);
    redex_assert(env.is_value());
    sources_count = env.bindings().size();
    ret.iter->run(env);
  }

  // 4) Go over and see.
  auto check_res = check(*ret.iter, cfg, sources_count);

  if (check_res.index() == 0) {
    ret.method_with_issues = true;
    if (std::get<bool>(check_res)) {
      // Diagnostics.
      print(std::cerr, ret.rdefs, *ret.iter, cfg);
    };
    return ret;
  }

  const auto& p = std::get<std::pair<size_t, size_t>>(check_res);
  ret.max_d = p.first;
  ret.max_same = p.second;

  return ret;
}

size_t remove(ControlFlowGraph& cfg, AnalysisResult& analysis) {
  CFGMutation mutation(cfg);
  size_t removed = 0;
  for (auto* b : cfg.blocks()) {
    auto state = analysis.iter->get_entry_state_at(b);
    redex_assert(!state.is_top());
    if (state.is_bottom()) {
      continue;
    }

    for (const auto& insn_it : ir_list::InstructionIterable{b}) {
      if (opcode::is_a_monitor(insn_it.insn->opcode())) {
        auto it = analysis.rdefs.find(insn_it.insn);
        redex_assert(it != analysis.rdefs.cend());
        const auto* def = it->second;

        const auto& bindings = state.bindings();
        const auto& def_state = bindings.at(def);
        if (def_state.is_value()) {
          size_t times = analysis::get_per(*def_state.get_constant());
          if (times >=
              (insn_it.insn->opcode() == OPCODE_MONITOR_ENTER ? 1 : 2)) {
            mutation.remove(cfg.find_insn(insn_it.insn, b));
            ++removed;
          }
        }
      }
      analysis.iter->analyze_instruction(insn_it.insn, &state);
    }
  }
  mutation.flush();
  return removed;
}

// Verification computes the "cover" (set of all locked objects)
// for all blocks and compares.
std::optional<std::string> verify(cfg::ControlFlowGraph& cfg,
                                  const AnalysisResult& orig,
                                  const AnalysisResult& removed) {
  std::ostringstream oss;
  for (auto* b : cfg.blocks()) {
    auto new_state = removed.iter->get_entry_state_at(b);
    redex_assert(!new_state.is_top());
    auto old_state = orig.iter->get_entry_state_at(b);
    redex_assert(!old_state.is_top());
    redex_assert(new_state.is_bottom() || !old_state.is_bottom());
    if (new_state.is_bottom()) {
      continue;
    }

    auto cover = [](const auto& s) {
      UnorderedSet<const IRInstruction*> res;
      for (const auto& p : s.bindings()) {
        if (p.second.is_value() && *p.second.get_constant() != 0) {
          res.insert(p.first);
        }
      }
      return res;
    };
    auto old_cover = cover(old_state);
    auto new_cover = cover(new_state);
    if (old_cover != new_cover) {
      oss << "Cover difference in block B" << b->id() << ": ";
      auto add_cover = [&oss](const auto& c) {
        auto add = [&oss](auto* i) {
          oss << " " << i << "(" << show(i) << ")";
        };
        oss << "[";
        for (auto* i : UnorderedIterable(c)) {
          add(i);
        }
        oss << "]";
      };
      add_cover(old_cover);
      oss << " vs ";
      add_cover(new_cover);
      oss << '\n';
    }
  }
  std::string res = oss.str();
  if (!res.empty()) {
    return std::move(res);
  }
  return std::nullopt;
}

struct Stats {
  static constexpr size_t kArraySize = analysis::kMaxLockDepth + 1;
  std::array<UnorderedSet<DexMethod*>, kArraySize> counts;
  std::array<UnorderedSet<DexMethod*>, kArraySize> counts_per;
  size_t all_methods{0};
  size_t methods_with_locks{0};
  size_t removed{0};
  UnorderedSet<DexMethod*> methods_with_issues;
  UnorderedSet<DexMethod*> non_singleton_rdefs;

  Stats& operator+=(const Stats& rhs) {
    for (size_t i = 0; i < counts.size(); ++i) {
      insert_unordered_iterable(counts[i], rhs.counts[i]);
    }
    for (size_t i = 0; i < counts_per.size(); ++i) {
      insert_unordered_iterable(counts_per[i], rhs.counts_per[i]);
    }
    all_methods += rhs.all_methods;
    methods_with_locks += rhs.methods_with_locks;
    removed += rhs.removed;
    insert_unordered_iterable(methods_with_issues, rhs.methods_with_issues);
    insert_unordered_iterable(non_singleton_rdefs, rhs.non_singleton_rdefs);
    return *this;
  }
};

bool has_monitor_ops(cfg::ControlFlowGraph& cfg) {
  for (const auto& mie : cfg::InstructionIterable(cfg)) {
    if (opcode::is_a_monitor(mie.insn->opcode())) {
      return true;
    }
  }
  return false;
}

Stats run_locks_removal(DexMethod* m, IRCode* code) {
  // 1) Check whether there are MONITOR_ENTER instructions.
  always_assert(code->cfg_built());
  auto& cfg = code->cfg();
  if (!has_monitor_ops(cfg)) {
    return Stats{};
  }

  Stats stats{};
  auto analysis = analyze(cfg);

  stats.methods_with_locks = analysis.method_with_locks ? 1 : 0;
  if (analysis.non_singleton_rdefs) {
    stats.non_singleton_rdefs.insert(m);
    return stats;
  }
  if (analysis.method_with_issues) {
    stats.methods_with_issues.insert(m);
    return stats;
  }
  if (!analysis.method_with_locks) {
    return stats;
  }

  stats.counts[analysis.max_d].insert(m);
  stats.counts_per[analysis.max_same].insert(m);

  if (analysis.max_same > 1) {
    size_t removed = remove(cfg, analysis);
    redex_assert(removed > 0);
    cfg.simplify(); // Remove dead blocks.

    // Run analysis again just to check.
    auto analysis2 = analyze(cfg);
    always_assert_log(!analysis2.non_singleton_rdefs, "%s", SHOW(cfg));
    always_assert_log(!analysis2.method_with_issues, "%s", SHOW(cfg));
    auto verify_res = verify(cfg, analysis, analysis2);
    auto print_err = [&m, &verify_res, &analysis2, &cfg]() {
      std::ostringstream oss;
      oss << show(m) << ": " << *verify_res << '\n';
      print(oss, analysis2.rdefs, *analysis2.iter, cfg);
      return oss.str();
    };
    always_assert_log(!verify_res, "%s", print_err().c_str());

    stats.removed += removed;
  }

  return stats;
}

void run_impl(DexStoresVector& stores,
              ConfigFiles& conf,
              PassManager& mgr,
              const char* stats_prefix = nullptr) {
  auto scope = build_class_scope(stores);

  Stats stats =
      walk::parallel::methods<Stats>(scope, [](DexMethod* method) -> Stats {
        auto* code = method->get_code();
        // `Stats{}` is the identity of the walker's reduction, and the walker
        // default-constructs one per thread, so only the value returned for a
        // method may carry a count.
        Stats method_stats = method::is_optimizable(method)
                                 ? run_locks_removal(method, code)
                                 : Stats{};
        method_stats.all_methods = 1;
        return method_stats;
      });

  auto print = [&mgr, &stats_prefix](const std::string& name, size_t stat) {
    mgr.set_metric(stats_prefix == nullptr ? name : stats_prefix + name, stat);
    if (kDebugPass || traceEnabled(LOCKS, 1)) {
      std::cerr << (stats_prefix == nullptr ? "" : stats_prefix) << name
                << " = " << stat << '\n';
    }
  };
  const auto& prof = conf.get_method_profiles();
  if (!prof.has_stats()) {
    TRACE(LOCKS, 2, "No profiles available!");
  }
  auto sorted = [&prof](const UnorderedSet<DexMethod*>& in) {
    return unordered_to_ordered(
        in, [&prof](const DexMethod* lhs, const DexMethod* rhs) {
          auto lhs_prof =
              prof.get_method_stat(method_profiles::COLD_START, lhs);
          auto rhs_prof =
              prof.get_method_stat(method_profiles::COLD_START, rhs);
          if (lhs_prof) {
            if (rhs_prof) {
              return lhs_prof->call_count > rhs_prof->call_count;
            }
            return true;
          }
          if (rhs_prof) {
            return false;
          }

          return compare_dexmethods(lhs, rhs);
        });
  };

  print("all_methods", stats.all_methods);
  print("methods_with_locks", stats.methods_with_locks);
  print("methods_with_issues", stats.methods_with_issues.size());
  if ((kDebugPass || traceEnabled(LOCKS, 2)) &&
      !stats.methods_with_issues.empty()) {
    std::cerr << "Lock analysis failed for:\n";
    for (auto* m : sorted(stats.methods_with_issues)) {
      std::cerr << " * " << show(m) << '\n';
    }
  }
  print("non_singleton_rdefs", stats.non_singleton_rdefs.size());
  if (kDebugPass || traceEnabled(LOCKS, 2)) {
    for (auto* m : sorted(stats.non_singleton_rdefs)) {
      std::cerr << " * " << show(m) << '\n';
    }
  }
  print("removed", stats.removed);

  auto print_counts = [&print](const auto& counts, const std::string& prefix) {
    size_t last = counts.size() - 1;
    while (last != 0 && counts[last].empty()) {
      --last;
    }
    for (size_t i = 0; i <= last; ++i) {
      std::string name = prefix;
      name += std::to_string(i);
      print(name, counts[i].size());
    }
  };
  print_counts(stats.counts, "counts");
  print_counts(stats.counts_per, "counts_per");

  if (kDebugPass || traceEnabled(LOCKS, 3)) {
    for (size_t i = 3; i < stats.counts_per.size(); ++i) {
      if (!stats.counts_per[i].empty()) {
        std::cerr << "=== " << i << " ===\n";
        for (auto* m : sorted(stats.counts_per[i])) {
          std::cerr << " * " << show(m);
          auto prof_stats =
              prof.get_method_stat(method_profiles::COLD_START, m);
          if (prof_stats) {
            std::cerr << " " << prof_stats->call_count << " / "
                      << prof_stats->appear_percent;
          }
          std::cerr << '\n';
        }
      }
    }
  }
}

} // namespace

bool RemoveRecursiveLocksPass::run(DexMethod* method, IRCode* code) {
  auto stats = run_locks_removal(method, code);
  return stats.methods_with_locks > 0 && stats.methods_with_issues.empty() &&
         stats.non_singleton_rdefs.empty();
}

void RemoveRecursiveLocksPass::run_pass(DexStoresVector& stores,
                                        ConfigFiles& conf,
                                        PassManager& mgr) {
  run_impl(stores, conf, mgr);
  if (kDebugPass) {
    run_impl(stores, conf, mgr, "debug_2nd_");
  }
}

static RemoveRecursiveLocksPass s_pass;
