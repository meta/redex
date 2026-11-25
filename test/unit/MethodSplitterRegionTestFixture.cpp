/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MethodSplitterRegionTestFixture.h"

#include <algorithm>
#include <atomic>
#include <sstream>

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

namespace method_splitting_region_test {

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

std::string coldBodySputs(size_t n_instrs) {
  static const char* kFieldChars = "abcdefghijklmnopqrstuvwxyz";
  std::ostringstream oss;
  for (size_t i = 0; i < n_instrs; ++i) {
    char ch = kFieldChars[i % 26];
    oss << "(sput v0 \"LFoo;." << ch << "_" << i << ":I\")\n";
  }
  return oss.str();
}

std::string coldBodyOfSize(size_t n_instrs, ColdBodyKind kind) {
  switch (kind) {
  case ColdBodyKind::kSputChain:
    return coldBodySputs(n_instrs);
  }
  redex_assert(false);
  return "";
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

std::string make_k_body(std::string_view producer_sexpr, size_t count) {
  std::ostringstream oss;
  for (size_t i = 0; i < count; ++i) {
    oss << "  " << producer_sexpr << "\n";
  }
  return oss.str();
}

method_splitting_impl::Config regionTestConfig() {
  method_splitting_impl::Config c;
  c.enable_region_splitting = true;
  c.min_original_size = 1;
  c.min_original_size_hot_method = 1;
  c.min_original_size_too_large_for_inlining = 1;
  c.min_hot_cold_split_size = 4;
  c.min_hot_split_size = 4;
  c.min_cold_split_size = 4;
  c.split_block_size = 100000;
  c.max_overhead_ratio = 0.5;
  c.max_hot_overhead_ratio = 0.5;
  c.max_huge_overhead_ratio = 0.5;
  c.max_iteration = 1;
  c.cost_split_method = 1;
  return c;
}

RegionResult runRegionSplitter(std::string_view sig,
                               std::string_view code_sexpr,
                               const method_splitting_impl::Config& cfg,
                               std::string_view class_prefix) {
  auto [cls, m] = make_test_class(sig, code_sexpr, class_prefix);
  DexStoresVector stores;
  stores.emplace_back("test_store");
  stores.front().get_dexen().push_back({cls});
  method_splitting_impl::Stats stats;
  // A null `min_sdk_api` leaves every EXTERNAL type failing the loadability
  // check, which is the conservative default the harness wants.
  method_splitting_impl::StoreRefCheckers store_ref_checkers(
      stores, /* normal_primary_dex */ false, /* min_sdk_api */ nullptr);
  method_splitting_impl::split_methods_in_stores(
      stores, /* min_sdk */ 0, cfg, store_ref_checkers,
      /* create_init_class_insns */ false,
      /* reserved_mrefs */ 0, /* reserved_trefs */ 0, &stats);
  RegionResult res;
  for (const auto& [out, kind] : stats.added_methods) {
    if (kind == method_splitting_impl::SplitKind::Region) {
      res.region_splits.push_back(out);
    } else {
      res.suffix_splits.push_back(out);
    }
  }
  res.stats = stats.snapshot();
  return res;
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

// A structural fingerprint of the outcome: which markers ended up in which
// split. Comparing split NAMES alone would miss a splitter that picks the same
// number of regions in a different place from run to run, because the name is
// `base$split$<kind>$region<index>` -- a function of kind and an emission
// counter only, so a permutation of the closures produces an identical
// multiset.
std::string splitSignature(const RegionResult& res) {
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
    const std::function<RegionResult(std::string_view class_prefix)>&
        builder_fn) {
  return {splitSignature(builder_fn("LDetA")),
          splitSignature(builder_fn("LDetB"))};
}

bool runTwiceAndCompare(
    const std::function<RegionResult(std::string_view class_prefix)>&
        builder_fn) {
  auto [a, b] = runTwiceAndSignatures(builder_fn);
  return a == b;
}

} // namespace method_splitting_region_test
