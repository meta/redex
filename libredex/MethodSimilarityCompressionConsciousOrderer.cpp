/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MethodSimilarityCompressionConsciousOrderer.h"

#include <algorithm>
#include <inttypes.h>
#include <limits>

#include "BalancedPartitioning.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "Show.h"

namespace {

// Keep a violated max_encoded_size() contract inside the allocation long enough
// for the post-encode assertion to report it.
constexpr size_t kEncodingSafetyMargin = size_t{512} * 1024;

/// Murmur-inspired hashing.
constexpr uint64_t hash_128_to_64(const uint64_t upper,
                                  const uint64_t lower) noexcept {
  const uint64_t k_mul = 0x9ddfea08eb382d69ULL;
  uint64_t A = (lower ^ upper) * k_mul;
  A ^= (A >> 47);
  uint64_t B = (upper ^ A) * k_mul;
  B ^= (B >> 47);
  B *= k_mul;
  return B;
}

/// A wrapper of a DexMethod with a hash value and corresponding k-mers.
struct BinaryFunction {
  explicit BinaryFunction(DexMethod* m) : method(m) {}

  // The method corresponding to the function.
  DexMethod* method;
  // The list of k-mers used for compression (instruction stable hashes).
  std::vector<uint64_t> kmers;
  // Corresponding document.
  Document* doc{nullptr};
  // Generated hash value.
  uint64_t hash = 0;
};

/// Get the function's hash code based on its content. It is used to identify
/// and merge duplicates.
uint64_t compute_hash_code(
    BinaryFunction& func,
    const UnorderedMap<uint64_t, uint32_t>& kmer_frequency) {
  const uint32_t k_min_kmer_frequency = 5;
  uint64_t hash = 0;
  for (uint64_t kmer : func.kmers) {
    always_assert_log(kmer_frequency.find(kmer)->second > 0,
                      "Incorrect kmer frequency");
    // Ignore rare k-mers so as we merge near-duplicate functions
    if (kmer_frequency.find(kmer)->second <= k_min_kmer_frequency) {
      continue;
    }

    hash = hash_128_to_64(hash, kmer);
  }
  return hash;
}

/// Initialize data structures for the reordering algorithm.
void init_bipartite_graph(std::vector<BinaryFunction>& functions,
                          std::vector<Document>& documents) {
  // Compute k-mer frequency
  UnorderedMap<uint64_t, uint32_t> kmer_frequency;
  for (uint32_t f = 0; f < functions.size(); f++) {
    BinaryFunction& func = functions[f];
    for (uint64_t kmer : func.kmers) {
      kmer_frequency[kmer]++;
    }
  }

  // Filter out unique and too frequent k-mers that do not affect compression;
  // for the remaining k-mers, assign an index from the range [0, |Kmers|)
  UnorderedMap<uint64_t, uint32_t> kmer_index;
  for (auto it : UnorderedIterable(kmer_frequency)) {
    uint64_t kmer = it.first;
    uint32_t freq = it.second;
    if (freq <= 1) {
      continue;
    }
    if (static_cast<size_t>(freq) * 2 >= functions.size()) {
      continue;
    }

    uint32_t new_idx = static_cast<uint32_t>(kmer_index.size());
    kmer_index[kmer] = new_idx;
  }

  // Computing function hashes and record the first one having a specific hash
  // value (in order to merge duplicates)
  UnorderedMap<uint64_t, uint32_t> first_func_with_hash;
  for (uint32_t f = 0; f < functions.size(); f++) {
    BinaryFunction& func = functions[f];
    func.hash = compute_hash_code(func, kmer_frequency);
    if (first_func_with_hash.find(func.hash) == first_func_with_hash.end()) {
      first_func_with_hash[func.hash] = f;
    }
  }

  // Initialize all documents corresponding to unique functions
  uint32_t num_docs = 0;
  documents.resize(first_func_with_hash.size());
  for (uint32_t f = 0; f < functions.size(); f++) {
    uint64_t hash = functions[f].hash;
    always_assert_log(first_func_with_hash.find(hash) !=
                          first_func_with_hash.end(),
                      "Function with hash %" PRIu64 " not found", hash);
    if (first_func_with_hash[hash] == f) {
      // Found a new function instance
      Document& doc = documents.at(num_docs);
      doc.init(f);
      functions[f].doc = &doc;
      for (uint64_t kmer : functions[f].kmers) {
        auto it = kmer_index.find(kmer);
        if (it != kmer_index.end()) {
          doc.add(it->second);
        }
      }
      doc.shrink_to_fit();
      num_docs++;
    } else {
      // A function with this hash already exists
      BinaryFunction& first_func = functions[first_func_with_hash[hash]];
      always_assert_log(first_func.doc != nullptr,
                        "Incorrect document for method %s",
                        SHOW(first_func.method));
      Document* doc = first_func.doc;
      doc->init(f);
      functions[f].doc = doc;
    }
  }
}

/// Apply compression-conscious reordering function reordering using
/// Balanced Graph Partitioning for a given set of functions.
void apply_bpc(std::vector<BinaryFunction>& functions) {
  // Creating and initializing a bipartite graph in which one part is a given
  // set of documents (functions) and another part is the corresponding k-mers
  std::vector<Document> documents;
  init_bipartite_graph(functions, documents);

  // Copying the list of documents as it will be modified during the execution
  std::vector<Document*> documents_ptr;
  documents_ptr.reserve(documents.size());
  for (Document& doc : documents) {
    documents_ptr.push_back(&doc);
  }

  // Run the reordering algorithm
  BalancedPartitioning alg(documents_ptr);
  alg.run();

  // Verify that every document gets a correct bucket
  for (Document& doc : documents) {
    always_assert(0 <= doc.bucket && doc.bucket < functions.size());
  }

  // Sort functions by the resulting buckets
  std::stable_sort(
      functions.begin(), functions.end(),
      [&](const BinaryFunction& left, const BinaryFunction& right) {
        return left.doc->bucket < right.doc->bucket;
      });
}

/// Generate k-mers (uint64_t hashes) from a given method content.
std::vector<uint64_t> create_kmers(const std::vector<uint8_t>& content) {
  always_assert_log(!content.empty(), "Constructing kmers for empty code.");
  std::vector<uint64_t> kmers;

  // Compute k-mers from the given content by iterating over the data. Shorter
  // (overlapping) k-mers force method with similar instructions to stay
  // together, while longer (non-overlapping) k-mers bring together methods
  // containing identical sequences (e.g., basic blocks) of instructions.
  const size_t k_window_1 = 5;
  const size_t k_window_2 = 10;
  for (size_t i = 0; i + k_window_1 <= content.size(); i++) {
    // Collect overlapping k-mers of a smaller size
    uint64_t hash = 0;
    for (size_t j = 0; j < k_window_1; j++) {
      hash = hash_128_to_64(hash, static_cast<uint64_t>(content[i + j]));
    }
    kmers.push_back(hash);
    // Collect non-overlapping k-mers of a larger size
    if (i % k_window_2 == 0 && i + k_window_2 <= content.size()) {
      hash = 0;
      for (size_t j = 0; j < k_window_2; j++) {
        hash = hash_128_to_64(hash, static_cast<uint64_t>(content[i + j]));
      }
      kmers.push_back(hash);
    }
  }

  // Sort the k-mers and get rid of duplicates
  std::sort(kmers.begin(), kmers.end());
  kmers.erase(std::unique(kmers.begin(), kmers.end()), kmers.end());

  return kmers;
}

}; // namespace

std::vector<uint8_t>
MethodSimilarityCompressionConsciousOrderer::get_encoded_method_content(
    DexMethod* meth, DexOutputIdx& dodx, EncodingScratch& scratch) {
  DexCode* code = meth->get_dex_code();
  always_assert_log(code != nullptr, "Empty code for method %s", SHOW(meth));

  const size_t bound = code->max_encoded_size();
  always_assert_log(
      bound <= std::numeric_limits<size_t>::max() - kEncodingSafetyMargin,
      "Encoded-code bound %zu leaves no room for the safety margin for %s",
      bound, SHOW(meth));
  const size_t capacity = bound + kEncodingSafetyMargin;
  const size_t words = capacity / sizeof(uint32_t) +
                       static_cast<size_t>(capacity % sizeof(uint32_t) != 0);
  if (scratch.words.size() < words) {
    scratch.words.resize(words, 0);
  }

  auto* bytes = reinterpret_cast<uint8_t*>(scratch.words.data());
  std::fill_n(bytes, scratch.dirty_bytes, uint8_t{0});

  const int encoded_size = code->encode(&dodx, scratch.words.data());
  always_assert_log(encoded_size >= 0,
                    "DexCode::encode returned a negative size for %s",
                    SHOW(meth));
  const size_t size = static_cast<size_t>(encoded_size);
  always_assert_log(size <= bound,
                    "DexCode::encode wrote %zu bytes despite a %zu-byte bound "
                    "for %s (scratch capacity %zu)",
                    size, bound, SHOW(meth),
                    scratch.words.size() * sizeof(uint32_t));
  scratch.dirty_bytes = std::max(scratch.dirty_bytes, size);

  return std::vector<uint8_t>(bytes, bytes + size);
}

void MethodSimilarityCompressionConsciousOrderer::order(
    std::vector<DexMethod*>& methods, GatheredTypes* m_gtypes) {
  Timer t("Reordering " + std::to_string(methods.size()) +
              " methods by similarity using BPC",
          /*indent=*/false);
  if (methods.empty()) {
    return;
  }

  EncodingScratch scratch;
  auto dodx = m_gtypes->get_dodx();

  // Collect binary functions in the original order
  std::vector<BinaryFunction> functions;
  functions.reserve(methods.size());
  std::vector<DexMethod*> empty_methods;
  for (DexMethod* method : methods) {
    auto* code = method->get_dex_code();
    if (code == nullptr) {
      empty_methods.push_back(method);
      continue;
    }
    functions.emplace_back(method);
    auto& func = functions.back();
    auto content = get_encoded_method_content(method, dodx, scratch);
    func.kmers = create_kmers(content);
  }

  // Apply the reordering
  if (!functions.empty()) {
    apply_bpc(functions);
  }
  methods.clear();

  // Record the reordered methods
  for (BinaryFunction& func : functions) {
    methods.push_back(func.method);
  }
  // Record the result for the empty methods
  methods.insert(methods.end(), empty_methods.begin(), empty_methods.end());
}
