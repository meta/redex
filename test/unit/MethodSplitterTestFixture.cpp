/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MethodSplitterTestFixture.h"

#include <algorithm>
#include <array>
#include <atomic>
#include <set>
#include <sstream>
#include <utility>

#include "ControlFlow.h"
#include "Creators.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexAccess.h"
#include "DexStore.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "MethodSplitter.h"
#include "Show.h"
#include "SplitNetSaving.h"

namespace method_splitting_test {

namespace {

std::atomic<size_t> g_class_counter{0};

std::pair<DexClass*, DexMethod*> make_test_class(std::string_view sig,
                                                 std::string_view code_str,
                                                 std::string_view name_prefix) {
  size_t c = g_class_counter.fetch_add(1);
  std::string name = std::string(name_prefix) + std::to_string(c) + ";";
  ClassCreator cc{DexType::make_type(name)};
  cc.set_super(type::java_lang_Object());
  auto code = assembler::ircode_from_string(std::string(code_str));
  redex_assert(code != nullptr);
  auto* m = DexMethod::make_method(name + ".bar:" + std::string(sig))
                ->make_concrete(ACC_PUBLIC | ACC_STATIC, std::move(code),
                                /* is_virtual */ false);
  m->set_deobfuscated_name(show(m));
  m->get_code()->build_cfg();
  cc.add_method(m);
  return {cc.create(), m};
}

} // namespace

std::string nonMergeableRejoin() {
  // A rejoin block whose only instruction is a `return` is absorbed into its
  // sole cold predecessor by `normalize_cfg_for_splitting`, which silently
  // destroys the shape these fixtures are built to exercise. Any non-terminator
  // instruction in the block prevents that; `add-int v0 v0 v0` is two code
  // units and has no operands beyond v0, so it perturbs nothing else.
  return "(add-int v0 v0 v0)";
}

std::string sputChain(size_t n_instrs, std::string_view field_prefix) {
  std::ostringstream oss;
  for (size_t i = 0; i < n_instrs; ++i) {
    oss << "(sput v0 \"LFoo;." << field_prefix << "_" << i << ":I\")\n";
  }
  return oss.str();
}

std::string hotColdHotCfg(std::string_view cold_body, std::string_view sig) {
  std::ostringstream oss;
  oss << "(\n"
      << "  (load-param v0)\n"
      << "  (.src_block \"LFoo;.bar:" << sig << "\" 0 " << kHotWeights << ")\n"
      << "  (if-eqz v0 :rejoin)\n"
      << "  (.src_block \"LFoo;.bar:" << sig << "\" 1 " << kColdWeights << ")\n"
      << cold_body << "  (:rejoin)\n"
      << "  (.src_block \"LFoo;.bar:" << sig << "\" 2 " << kHotWeights << ")\n"
      << "  " << nonMergeableRejoin() << "\n"
      << "  (return-void)\n"
      << ")\n";
  return oss.str();
}

std::string multiBlockHammockCfg(std::string_view body_a,
                                 std::string_view body_b,
                                 std::string_view body_c) {
  // hot -> cold_a -> branch -> (cold_b | cold_c) -> rejoin
  std::ostringstream oss;
  oss << "(\n"
      << "  (load-param v0)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 0 " << kHotWeights << ")\n"
      << "  (if-eqz v0 :rejoin)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 1 " << kColdWeights << ")\n"
      << body_a << "  (if-eqz v0 :cold_c)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 2 " << kColdWeights << ")\n"
      << body_b << "  (goto :rejoin)\n"
      << "  (:cold_c)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 3 " << kColdWeights << ")\n"
      << body_c << "  (goto :rejoin)\n"
      << "  (:rejoin)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 4 " << kHotWeights << ")\n"
      << "  " << nonMergeableRejoin() << "\n"
      << "  (return-void)\n"
      << ")\n";
  return oss.str();
}

// See the header: only instructions reachable from the entry count, and the
// marker must be a chain's whole prefix.
size_t countFieldRefs(DexMethod* m, std::string_view marker) {
  auto* code = m->get_code();
  if (code == nullptr) {
    return 0;
  }
  always_assert(code->cfg_built());
  auto& cfg = code->cfg();
  UnorderedSet<cfg::Block*> seen;
  std::vector<cfg::Block*> work{cfg.entry_block()};
  seen.insert(cfg.entry_block());
  size_t n = 0;
  while (!work.empty()) {
    auto* b = work.back();
    work.pop_back();
    for (auto& mie : ir_list::InstructionIterable(b)) {
      auto* insn = mie.insn;
      if (!insn->has_field()) {
        continue;
      }
      // The name must continue with `_` after the marker: `starts_with` alone
      // would let `bd` count `bd1_*` through `bd4_*`.
      const auto& name = insn->get_field()->get_name()->str();
      if (name.size() > marker.size() && name.starts_with(marker) &&
          name[marker.size()] == '_') {
        n++;
      }
    }
    for (auto* e : b->succs()) {
      if (seen.insert(e->target()).second) {
        work.push_back(e->target());
      }
    }
  }
  return n;
}

method_splitting_impl::Config splitterTestConfig() {
  method_splitting_impl::Config c;
  c.min_original_size = 1;
  c.min_original_size_hot_method = 1;
  c.min_original_size_too_large_for_inlining = 1;
  c.min_hot_cold_split_size = 4;
  c.min_hot_split_size = 4;
  c.min_cold_split_size = 4;
  c.min_suffix_sub_floor_split_size = 4;
  c.split_block_size = 100000;
  c.max_overhead_ratio = 0.5;
  c.max_hot_overhead_ratio = 0.5;
  c.max_huge_overhead_ratio = 0.5;
  c.max_iteration = 1;
  c.cost_split_method = 1;
  return c;
}

method_splitting_impl::Config regionTestConfig() {
  auto c = splitterTestConfig();
  c.enable_region_splitting = true;
  return c;
}

namespace {

SplitResult run_splitter(std::string_view sig,
                         std::string_view code_sexpr,
                         const method_splitting_impl::Config& cfg,
                         std::string_view class_prefix,
                         bool host_compiled) {
  cfg.validate();
  auto [cls, m] = make_test_class(sig, code_sexpr, class_prefix);
  DexStoresVector stores;
  stores.emplace_back("test_store");
  stores.front().get_dexen().push_back({cls});
  method_splitting_impl::Stats stats;
  method_splitting_impl::EvaluationLog evaluations;
  stats.evaluations = &evaluations;
  // Mark the host as compiled from the baseline profile (production reads
  // this from the profile), so that the net saving counts the cold code a
  // split takes out of it. Splitting shrinks the OAT only by taking cold code
  // out of an ahead-of-time-compiled method, and on an uncompiled host no
  // suffix is net-evaluated. A test can ask for an uncompiled host instead.
  InsertOnlyConcurrentSet<const DexMethod*> hot_methods;
  if (host_compiled) {
    hot_methods.insert(m);
  }
  // A null `min_sdk_api` leaves every EXTERNAL type failing the loadability
  // check, which is the conservative default the harness wants.
  method_splitting_impl::StoreRefCheckers store_ref_checkers(
      stores, /* normal_primary_dex */ false, /* min_sdk_api */ nullptr);
  method_splitting_impl::split_methods_in_stores(
      stores, /* min_sdk */ 0, cfg, store_ref_checkers,
      /* create_init_class_insns */ false,
      /* reserved_mrefs */ 0, /* reserved_trefs */ 0, &stats,
      /* name_infix */ "", &hot_methods);
  SplitResult res;
  res.main_method = m;
  for (const auto& [out, kind] : stats.added_methods) {
    if (kind == method_splitting_impl::SplitKind::Region) {
      res.region_splits.push_back(out);
    } else {
      res.suffix_splits.push_back(out);
    }
  }
  res.stats = stats.snapshot();
  res.evaluations = evaluations.records();
  expectEveryCandidateHasOneFate(res.stats, res.evaluations,
                                 /* one_host */ true);
  return res;
}

} // namespace

SplitResult runSplitter(std::string_view sig,
                        std::string_view code_sexpr,
                        const method_splitting_impl::Config& cfg,
                        std::string_view class_prefix) {
  return run_splitter(sig, code_sexpr, cfg, class_prefix,
                      /*host_compiled=*/true);
}

SplitResult runSplitterOnUncompiledHost(
    std::string_view sig,
    std::string_view code_sexpr,
    const method_splitting_impl::Config& cfg) {
  return run_splitter(sig, code_sexpr, cfg, "LFoo", /*host_compiled=*/false);
}

std::string describeSelection(const SplitResult& res) {
  std::ostringstream oss;
  auto fates = [&](std::string_view kind,
                   const method_splitting_impl::FateSnapshot& f) {
    oss << "\n" << kind << " candidates=" << f.candidates << ":";
    for (size_t i = 0; i < method_splitting_impl::kCandidateFateCount; ++i) {
      if (f.n[i] != 0) {
        oss << " " << method_splitting_impl::kCandidateFateNames[i].name << "="
            << f.n[i];
      }
    }
  };
  fates("suffix", res.stats.suffix_fates);
  oss << "\nall_splits=" << res.stats.split_count
      << " dex_limits_hit=" << res.stats.dex_limits_hit;
  return oss.str();
}

std::vector<method_splitting_impl::CandidateEvaluation> evaluationsOf(
    const SplitResult& res,
    method_splitting_impl::SplitKind kind,
    std::optional<method_splitting_impl::CandidateFate> fate) {
  std::vector<method_splitting_impl::CandidateEvaluation> out;
  for (const auto& e : res.evaluations) {
    if (e.kind == kind && (!fate || e.fate == *fate)) {
      out.push_back(e);
    }
  }
  return out;
}

void expectEveryCandidateHasOneFate(
    const method_splitting_impl::StatsSnapshot& stats,
    const std::vector<method_splitting_impl::CandidateEvaluation>& records,
    bool one_host) {
  using method_splitting_impl::SplitKind;
  auto check = [&](SplitKind kind,
                   const method_splitting_impl::FateSnapshot& fates,
                   const char* name) {
    always_assert_log(fates.recorded() == fates.candidates,
                      "%zu %s candidates, %zu fates", fates.candidates, name,
                      fates.recorded());
    std::array<size_t, method_splitting_impl::kCandidateFateCount> per_fate{};
    for (const auto& e : records) {
      if (e.kind == kind) {
        per_fate[static_cast<size_t>(e.fate)]++;
      }
    }
    for (size_t i = 0; i < per_fate.size(); ++i) {
      always_assert_log(
          per_fate[i] == fates.n[i], "%zu %s records at %s, %zu counted",
          per_fate[i], name,
          std::string(method_splitting_impl::kCandidateFateNames[i].name)
              .c_str(),
          fates.n[i]);
    }
  };
  check(SplitKind::Suffix, stats.suffix_fates, "suffix");
  if (!one_host) {
    return;
  }
  // Only the first iteration is checked. It scans the host alone; later
  // iterations also scan the splits, whose block ids repeat the host's.
  std::set<std::pair<SplitKind, std::vector<cfg::BlockId>>> seen;
  for (const auto& e : records) {
    if (e.iteration == 0) {
      always_assert_log(seen.emplace(e.kind, e.heads).second,
                        "a candidate headed at B%zu has two records",
                        (size_t)e.heads.front());
    }
  }
}

std::vector<std::string> reachableFieldNames(DexMethod* m) {
  std::vector<std::string> names;
  auto* code = m->get_code();
  if (code == nullptr) {
    return names;
  }
  always_assert(code->cfg_built());
  auto& cfg = code->cfg();
  UnorderedSet<cfg::Block*> seen;
  std::vector<cfg::Block*> work{cfg.entry_block()};
  seen.insert(cfg.entry_block());
  while (!work.empty()) {
    auto* b = work.back();
    work.pop_back();
    for (auto& mie : ir_list::InstructionIterable(b)) {
      if (mie.insn->has_field()) {
        names.push_back(mie.insn->get_field()->get_name()->str_copy());
      }
    }
    for (auto* e : b->succs()) {
      if (seen.insert(e->target()).second) {
        work.push_back(e->target());
      }
    }
  }
  return names;
}

size_t countFieldRefsIn(const SplitResult& res,
                        std::string_view marker,
                        Where where) {
  size_t n = 0;
  if (where != Where::SuffixSplits) {
    for (auto* m : res.region_splits) {
      n += countFieldRefs(m, marker);
    }
  }
  if (where != Where::RegionSplits) {
    for (auto* m : res.suffix_splits) {
      n += countFieldRefs(m, marker);
    }
  }
  return n;
}

// A structural fingerprint of the outcome: which markers ended up in which
// split. Comparing split NAMES alone would miss a splitter that picks the same
// number of regions in a different place from run to run, because the name is
// `base$split$<kind>$region<index>` -- a function of kind and an emission
// counter only, so a permutation of the closures produces an identical
// multiset.
std::string splitSignature(const SplitResult& res) {
  std::vector<std::string> per_split;
  auto add = [&](DexMethod* m, std::string_view kind) {
    auto names = reachableFieldNames(m);
    std::sort(names.begin(), names.end());
    std::ostringstream oss;
    oss << kind << " " << m->get_name()->str() << " {";
    for (const auto& n : names) {
      oss << n << ",";
    }
    oss << "}";
    per_split.push_back(oss.str());
  };
  for (auto* m : res.region_splits) {
    add(m, "region");
  }
  for (auto* m : res.suffix_splits) {
    add(m, "suffix");
  }
  std::sort(per_split.begin(), per_split.end());
  std::ostringstream oss;
  for (const auto& s : per_split) {
    oss << s << "\n";
  }
  return oss.str();
}

std::pair<std::string, std::string> runTwiceAndSignatures(
    const std::function<SplitResult(std::string_view class_prefix)>&
        builder_fn) {
  return {splitSignature(builder_fn("LDetA")),
          splitSignature(builder_fn("LDetB"))};
}

bool runTwiceAndCompare(
    const std::function<SplitResult(std::string_view class_prefix)>&
        builder_fn) {
  auto [a, b] = runTwiceAndSignatures(builder_fn);
  return a == b;
}

} // namespace method_splitting_test
