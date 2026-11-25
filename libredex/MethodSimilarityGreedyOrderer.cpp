/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MethodSimilarityGreedyOrderer.h"

#include "Debug.h"
#include "DexInstruction.h"
#include "Show.h"
#include "Timer.h"
#include "Trace.h"
#include "WorkQueue.h"

namespace {
// Similarity score for each candidate method, based on the number of
// shared, missing and additional hash ids when compared to the previously
// chosen method.
struct Score {
  uint32_t shared{0};
  uint32_t missing{0};
  uint32_t additional{0};
  int32_t value() const { return 2 * shared - missing - 2 * additional; }
};

template <typename T>
struct CountingFakeOutputIterator {
  uint32_t& counter;
  T fake;
  explicit CountingFakeOutputIterator(uint32_t& c) : counter(c) {}
  CountingFakeOutputIterator& operator++() {
    counter++;
    return *this;
  }
  T& operator*() { return fake; }
};
}; // namespace

void MethodSimilarityGreedyOrderer::gather_code_hash_ids(
    const std::vector<DexInstruction*>& instructions,
    std::vector<CodeHashId>& code_hash_ids) {

  UnorderedSet<StableHash> stable_hashes;

  // For any instruction, we can compute a (stable) hash representing it.
  for (size_t i = 0; i < instructions.size(); i++) {
    uint64_t code_hash{0};
    auto* insn = instructions.at(i);
    auto op = insn->opcode();
    code_hash = code_hash * 23 + op;
    if (insn->has_range()) {
      code_hash =
          (code_hash * 11 + insn->range_base()) * 11 + insn->range_size();
    }
    if (insn->has_dest()) {
      code_hash = code_hash * 13 + insn->dest();
    }
    for (unsigned j = 0; j < insn->srcs_size(); j++) {
      code_hash = code_hash * 17 + insn->src(j);
    }
    if (insn->has_method()) {
      auto* callee = (dynamic_cast<DexOpcodeMethod*>(insn))->get_method();
      stable_hashes.insert(std::hash<std::string>{}(show(callee)));
    }
    stable_hashes.insert(code_hash);
  };

  // Initialize the vector for code hash.
  // Publish code hash ids from stable hashes.
  code_hash_ids.reserve(stable_hashes.size());
  for (StableHash stable_hash : UnorderedIterable(stable_hashes)) {
    if (m_stable_hash_to_code_hash_id.count(stable_hash) == 0) {
      // Assign a unique code hash id if it appears for the first time.
      auto code_hash_id = m_stable_hash_to_code_hash_id.size();
      m_stable_hash_to_code_hash_id[stable_hash] = code_hash_id;
    }
    code_hash_ids.push_back(m_stable_hash_to_code_hash_id[stable_hash]);
  }
  // Sort the code hash Ids to check the overlaps in the linear time.
  std::sort(code_hash_ids.begin(), code_hash_ids.end());
}

// For the given code hash ids (i) and code hash ids (j), get score for j
// against i.
static inline Score get_score(
    const std::vector<MethodSimilarityGreedyOrderer::CodeHashId>&
        code_hash_ids_i,
    const std::vector<MethodSimilarityGreedyOrderer::CodeHashId>&
        code_hash_ids_j) {
  uint32_t i_size = code_hash_ids_i.size();
  uint32_t j_size = code_hash_ids_j.size();

  Score score;
  std::set_intersection(
      code_hash_ids_i.begin(), code_hash_ids_i.end(), code_hash_ids_j.begin(),
      code_hash_ids_j.end(),
      CountingFakeOutputIterator<MethodSimilarityGreedyOrderer::CodeHashId>(
          score.shared));

  score.missing = i_size - score.shared;
  score.additional = j_size - score.shared;

  return score;
}

void MethodSimilarityGreedyOrderer::compute_score() {
  m_score_map.clear();
  m_score_map.resize(m_id_to_method.size());

  // Maximum number of code items can be 65536.
  redex_assert(m_id_to_method.size() <= (1 << 16));

  std::vector<MethodId> indices(m_id_to_method.size());
  std::iota(indices.begin(), indices.end(), 0);
  workqueue_run<MethodId>(
      [&](MethodId i_id) {
        const auto& code_hash_ids_i = m_method_id_to_code_hash_ids[i_id];
        UnorderedMap<ScoreValue, boost::dynamic_bitset<>> score_map;

        for (uint32_t j_id = 0; j_id < (uint32_t)m_id_to_method.size();
             j_id++) {
          if (i_id == j_id) {
            continue;
          }

          const auto& code_hash_ids_j = m_method_id_to_code_hash_ids[j_id];
          auto score = get_score(code_hash_ids_i, code_hash_ids_j);
          if (score.value() >= 0) {
            auto& method_id_bitset = score_map[score.value()];
            if (method_id_bitset.size() <= j_id) {
              method_id_bitset.resize(j_id + 1);
            }
            method_id_bitset.set(static_cast<size_t>(j_id));
          }
        }

        if (!score_map.empty()) {
          std::map<ScoreValue, boost::dynamic_bitset<>,
                   std::greater<ScoreValue>>
              map;
          // Mapping from score value (key) to Method Ids. The key is in a
          // decreasing score order. Because it iterates Method Id in order,
          // the vector is already sorted by Method index (source order).
          for (auto&& [score_value, method_ids] :
               UnorderedIterable(score_map)) {
            map[score_value] = std::move(method_ids);
          }
          m_score_map[i_id] = std::move(map);
        }
      },
      indices);
}

void MethodSimilarityGreedyOrderer::insert(DexMethod* method) {
  always_assert(m_method_to_id.count(method) == 0);
  // While the number of methods can reach 65536 (2^16), at
  // this stage not all methods have been added, so we assert that
  // the number can fit on 16 bits and safely be assigned to a MethodId index.
  redex_assert(m_id_to_method.size() < (1 << 16));
  MethodId index = m_id_to_method.size();
  m_id_to_method.emplace(index, method);
  m_method_to_id.emplace(method, index);

  auto& code_hash_ids = m_method_id_to_code_hash_ids[index];
  auto* code = method->get_dex_code();
  if (code != nullptr) {
    gather_code_hash_ids(code->get_instructions(), code_hash_ids);
  }
}

std::optional<MethodSimilarityGreedyOrderer::MethodId>
MethodSimilarityGreedyOrderer::get_next() {
  // Clear best candidates.
  if (m_id_to_method.empty()) {
    return {};
  }

  if (m_last_method_id != std::nullopt) {
    // Iterate m_score_map from the highest score..
    for (const auto& [score, method_id_bitset] :
         m_score_map[*m_last_method_id]) {
      for (auto meth_id = method_id_bitset.find_first();
           meth_id != boost::dynamic_bitset<>::npos;
           meth_id = method_id_bitset.find_next(meth_id)) {
        // The first match is the one with the highest score
        // at the smallest index in the source order.
        if (m_id_to_method.count(static_cast<MethodId>(meth_id)) != 0u) {
          TRACE(OPUT, 3,
                "[method-similarity-orderer] selected %s with score %d",
                SHOW(m_id_to_method[static_cast<MethodId>(meth_id)]), score);
          return meth_id;
        }
      }
    }
  }
  std::optional<MethodId> best_method_id = m_id_to_method.begin()->first;
  TRACE(OPUT,
        3,
        "[method-similarity-orderer] reverted to %s",
        SHOW(*best_method_id));
  return best_method_id;
}

void MethodSimilarityGreedyOrderer::remove_method(DexMethod* meth) {
  if (m_method_to_id.count(meth) == 0u) {
    return;
  }

  auto method_id = m_method_to_id[meth];
  m_id_to_method.erase(method_id);
  m_method_to_id.erase(meth);
}

void MethodSimilarityGreedyOrderer::order(std::vector<DexMethod*>& methods) {
  Timer t("Reordering " + std::to_string(methods.size()) +
              " methods by similarity using the greedy approach",
          /*indent=*/false);

  for (auto* method : methods) {
    insert(method);
  }

  methods.clear();

  // Compute scores among methods in parallel.
  compute_score();

  m_last_method_id = std::nullopt;
  for (std::optional<MethodId> best_method_id = get_next();
       best_method_id != std::nullopt;
       best_method_id = get_next()) {
    m_last_method_id = best_method_id;
    auto* meth = m_id_to_method[*m_last_method_id];
    methods.push_back(meth);
    remove_method(meth);
  }
}
