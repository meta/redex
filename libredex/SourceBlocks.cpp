/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "SourceBlocks.h"

#include <limits>
#include <memory>
#include <optional>
#include <sstream>
#include <string>

#include <sparta/S_Expression.h>

#include "ConcurrentContainers.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DexClass.h"
#include "Dominators.h"
#include "IRList.h"
#include "IROpcode.h"
#include "RedexContext.h"
#include "ScopedCFG.h"
#include "Show.h"
#include "SourceBlockConsistencyCheck.h"
#include "Trace.h"
#include "Walkers.h"

namespace source_blocks {

using namespace cfg;
using namespace sparta;

namespace {

constexpr SourceBlock::Val kFailVal = SourceBlock::Val::none();
constexpr SourceBlock::Val kXVal = SourceBlock::Val::none();

static SourceBlockConsistencyCheck s_sbcc;

const SourceBlock::Val global_default_val = SourceBlock::Val(1, 1);

// Helper function to insert source blocks after throwing instructions
template <typename ProfileFn>
void insert_after_exceptions_impl(Block* cur,
                                  const DexString* method,
                                  uint32_t& id,
                                  bool serialize,
                                  std::ostringstream& oss,
                                  ProfileFn profile_fn) {
  if (cur->cfg().get_succ_edge_of_type(cur, EdgeType::EDGE_THROW) != nullptr) {
    // Nothing to do.
    return;
  }
  for (auto it = cur->begin(); it != cur->end(); ++it) {
    if (it->type != MFLOW_OPCODE) {
      continue;
    }
    if (!opcode::can_throw(it->insn->opcode())) {
      continue;
    }
    // Exclude throws (explicitly).
    if (it->insn->opcode() == OPCODE_THROW) {
      continue;
    }
    // Get to the next instruction.
    auto next_it = std::next(it);
    while (next_it != cur->end() && next_it->type != MFLOW_OPCODE) {
      ++next_it;
    }
    if (next_it == cur->end()) {
      break;
    }

    auto insert_after =
        opcode::is_move_result_any(next_it->insn->opcode()) ? next_it : it;

    // This is not really what the structure looks like, but easy to
    // parse and write. Otherwise, we would need to remember that
    // we had a nesting.

    if (serialize) {
      oss << "(" << id << ")";
    }

    auto nested_val = profile_fn();
    it = source_blocks::impl::BlockAccessor::insert_source_block_after(
        cur, insert_after,
        std::make_unique<SourceBlock>(method, id, nested_val));

    ++id;
  }
}

static char get_edge_char(const Edge* e) {
  switch (e->type()) {
  case EDGE_BRANCH:
    return 'b';
  case EDGE_GOTO:
    return 'g';
  case EDGE_THROW:
    return 't';
  case EDGE_GHOST:
  case EDGE_TYPE_SIZE:
    not_reached();
  }
  not_reached(); // For GCC.
}

struct InsertHelper {
  std::ostringstream oss;
  const DexString* method;
  uint32_t id{0};
  bool serialize;
  bool insert_after_excs;

  struct ProfileParserState {
    std::vector<s_expr> expr_stack;
    bool had_profile_failure{false};
    bool root_expr_is_nil;
    const SourceBlock::Val* default_val;
    const SourceBlock::Val* error_val;
    ProfileParserState(std::vector<s_expr> expr_stack,
                       bool root_expr_is_nil,
                       const SourceBlock::Val* default_val,
                       const SourceBlock::Val* error_val)
        : expr_stack(std::move(expr_stack)),
          root_expr_is_nil(root_expr_is_nil),
          default_val(default_val),
          error_val(error_val) {}
  };
  std::vector<ProfileParserState> parser_state;
  struct MatcherState {
    const std::string* val_str_ptr;
    s_expr tail;
    s_expr inner_tail;
    s_patn val_str_inner_tail_tail_pattern;
    s_patn val_str_tail_pattern;
    MatcherState()
        : val_str_inner_tail_tail_pattern(
              {s_patn({s_patn(&val_str_ptr)}, inner_tail)}, tail),
          val_str_tail_pattern({s_patn(&val_str_ptr)}, tail) {}
  };
  MatcherState matcher_state;

  InsertHelper(const DexString* method,
               const std::vector<ProfileData>& profiles,
               bool serialize,
               bool insert_after_excs)
      : method(method),
        serialize(serialize),
        insert_after_excs(insert_after_excs) {
    parser_state.reserve(profiles.size());
    for (const auto& p : profiles) {
      switch (p.index()) {
      case 0:
        // Nothing.
        parser_state.emplace_back(std::vector<s_expr>(),
                                  /* root_expr_is_nil */ true,
                                  /* default_val */ nullptr,
                                  /* error_val */ nullptr);
        break;

      case 1:
        // Profile string.
        {
          const auto& [profile, error_val_opt] = std::get<1>(p);
          std::istringstream iss{profile};
          s_expr_istream s_expr_input(iss);
          s_expr root_expr;
          s_expr_input >> root_expr;
          always_assert_log(!s_expr_input.fail(),
                            "Failed parsing profile %s for %s: %s",
                            profile.c_str(),
                            SHOW(method),
                            s_expr_input.what().c_str());
          bool root_expr_is_nil = root_expr.is_nil();
          std::vector<s_expr> expr_stack{s_expr({std::move(root_expr)})};
          const auto* error_val = error_val_opt ? &*error_val_opt : nullptr;
          parser_state.emplace_back(std::move(expr_stack), root_expr_is_nil,
                                    /* default_val */ nullptr, error_val);
          break;
        }

      case 2: {
        // A default Val.
        const auto* default_val = &std::get<2>(p);
        parser_state.emplace_back(std::vector<s_expr>(),
                                  /* root_expr_is_nil */ true, default_val,
                                  /* error_val */ nullptr);
        break;
      }

      default:
        not_reached();
      }
    }
  }

  static SourceBlock::Val parse_val(const std::string& val_str) {
    if (val_str == "x") {
      return kXVal;
    }
    size_t after_idx;
    float nested_val = std::stof(val_str, &after_idx); // May throw.
    always_assert_log(after_idx > 0,
                      "Could not parse first part of %s as float",
                      val_str.c_str());
    always_assert_log(after_idx + 1 < val_str.size(),
                      "Could not find separator of %s",
                      val_str.c_str());
    always_assert_log(val_str[after_idx] == ':',
                      "Did not find separating ':' in %s",
                      val_str.c_str());
    // This isn't efficient, but let's not play with low-level char* view.
    // Small-string optimization is likely enough.
    auto appear_part = val_str.substr(after_idx + 1);
    float appear100 = std::stof(appear_part, &after_idx);
    always_assert_log(after_idx == appear_part.size(),
                      "Could not parse second part of %s as float",
                      val_str.c_str());

    return SourceBlock::Val{nested_val, appear100};
  }

  void start(Block* cur) {
    if (serialize) {
      oss << "(" << id;
    }

    auto val = start_profile(cur, false);

    source_blocks::impl::BlockAccessor::push_source_block(
        cur, std::make_unique<SourceBlock>(method, id, val));
    ++id;

    if (insert_after_excs) {
      insert_after_exceptions_impl(
          cur, method, id, serialize, oss, [this, cur]() {
            return start_profile(cur, /*empty_inner_tail=*/true);
          });
    }
  }

  std::vector<SourceBlock::Val> start_profile(Block* cur,
                                              bool empty_inner_tail = false) {
    std::vector<SourceBlock::Val> ret;
    ret.reserve(parser_state.size());
    for (auto& p_state : parser_state) {
      ret.emplace_back(start_profile_one(cur, empty_inner_tail, p_state));
    }
    return ret;
  }

  SourceBlock::Val start_profile_one(Block* cur,
                                     bool empty_inner_tail,
                                     ProfileParserState& p_state) {
    if (p_state.had_profile_failure) {
      return kFailVal;
    }
    if (p_state.root_expr_is_nil) {
      if (p_state.default_val != nullptr) {
        return *p_state.default_val;
      }
      return kFailVal;
    }
    if (p_state.expr_stack.empty()) {
      p_state.had_profile_failure = true;
      TRACE(MMINL, 3,
            "Failed profile matching for %s: missing element for block %zu",
            SHOW(method), cur->id());
      return kFailVal;
    }
    s_expr& top_expr = p_state.expr_stack.back();
    if (!matcher_state.val_str_inner_tail_tail_pattern.match_with(top_expr)) {
      p_state.had_profile_failure = true;
      TRACE(MMINL, 3,
            "Failed profile matching for %s: cannot match string for %s",
            SHOW(method), top_expr.str().c_str());
      return kFailVal;
    }
    if (empty_inner_tail) {
      redex_assert(matcher_state.inner_tail.is_nil());
    }
    auto val = parse_val(*matcher_state.val_str_ptr);
    TRACE(MMINL,
          5,
          "Started block with val=%f/%f. Popping %s, pushing %s + %s",
          val ? val->val : std::numeric_limits<float>::quiet_NaN(),
          val ? val->appear100 : std::numeric_limits<float>::quiet_NaN(),
          top_expr.str().c_str(),
          matcher_state.tail.str().c_str(),
          matcher_state.inner_tail.str().c_str());
    top_expr = std::move(matcher_state.tail);
    if (!empty_inner_tail) {
      p_state.expr_stack.push_back(std::move(matcher_state.inner_tail));
    }
    return val;
  }

  void edge(Block* cur, const Edge* e) {
    if (serialize) {
      oss << " " << get_edge_char(e);
    }
    edge_profile(cur, e);
  }

  void edge_profile(Block* cur, const Edge* e) {
    for (auto& p_state : parser_state) {
      edge_profile_one(cur, e, p_state);
    }
  }

  void edge_profile_one(Block* /*cur*/,
                        const Edge* e,
                        ProfileParserState& p_state) {
    // If running with profile, there should be at least a nil on.
    if (p_state.had_profile_failure || p_state.expr_stack.empty()) {
      return;
    }
    s_expr& top_expr = p_state.expr_stack.back();
    if (!matcher_state.val_str_tail_pattern.match_with(top_expr)) {
      p_state.had_profile_failure = true;
      TRACE(MMINL, 3,
            "Failed profile matching for %s: cannot match string for %s",
            SHOW(method), top_expr.str().c_str());
      return;
    }
    char edge_char = get_edge_char(e);
    std::string_view expected(&edge_char, 1);
    if (expected != *matcher_state.val_str_ptr) {
      p_state.had_profile_failure = true;
      TRACE(MMINL, 3,
            "Failed profile matching for %s: edge type \"%s\" did not match "
            "expectation \"%s\"",
            SHOW(method), matcher_state.val_str_ptr->c_str(),
            str_copy(expected).c_str());
      return;
    }
    TRACE(MMINL,
          5,
          "Matched edge %s. Popping %s, pushing %s",
          matcher_state.val_str_ptr->c_str(),
          top_expr.str().c_str(),
          matcher_state.tail.str().c_str());
    top_expr = std::move(matcher_state.tail);
  }

  void end(Block* cur) {
    if (serialize) {
      oss << ")";
    }
    end_profile(cur);
  }

  void end_profile(Block* cur) {
    for (auto& p_state : parser_state) {
      end_profile_one(cur, p_state);
    }
  }

  void end_profile_one(Block* /*cur*/, ProfileParserState& p_state) {
    if (p_state.had_profile_failure) {
      return;
    }
    if (p_state.root_expr_is_nil) {
      return;
    }
    if (p_state.expr_stack.empty()) {
      TRACE(MMINL,
            3,
            "Failed profile matching for %s: empty stack on close",
            SHOW(method));
      p_state.had_profile_failure = true;
      return;
    }
    s_expr& top_expr = p_state.expr_stack.back();
    if (!top_expr.is_nil()) {
      TRACE(MMINL,
            3,
            "Failed profile matching for %s: edge sentinel not NIL",
            SHOW(method));
      p_state.had_profile_failure = true;
      return;
    }
    TRACE(MMINL, 5, "Popping %s", top_expr.str().c_str());
    p_state.expr_stack.pop_back(); // Remove sentinel nil.
  }

  bool wipe_profile_failures(ControlFlowGraph& cfg) {
    bool ret = false;
    for (size_t i = 0; i != parser_state.size(); ++i) {
      auto& p_state = parser_state[i];
      if (p_state.root_expr_is_nil) {
        continue;
      }
      if (!p_state.had_profile_failure) {
        continue;
      }
      ret = true;
      if (traceEnabled(MMINL, 3) && serialize) {
        TRACE(MMINL, 3, "For %s, expected profile of the form %s", SHOW(method),
              oss.str().c_str());
      }
      auto val = p_state.error_val != nullptr ? *p_state.error_val
                                              : SourceBlock::Val::none();
      for (auto* b : cfg.blocks()) {
        auto vec = gather_source_blocks(b);
        for (auto* sb : vec) {
          const_cast<SourceBlock*>(sb)->set_at(i, val);
        }
      }
    }
    return ret;
  }
};

struct CustomValueInsertHelper {
  enum class CustomInsertionType { DEFAULT_VALUES = 0, FUZZING_VALUES = 1 };

  std::ostringstream oss;
  const DexString* method;
  uint32_t id{0};
  bool serialize;
  bool insert_after_excs;
  CustomInsertionType insertion_type;
  size_t interaction_size;
  float cold_to_hot_generation_ratio{0.2f};
  float hot_throw_cold_generation_ratio{0.01f};

  CustomValueInsertHelper(const DexString* method,
                          const std::vector<ProfileData>& profiles,
                          bool serialize,
                          bool insert_after_excs,
                          CustomInsertionType insertion_type)
      : method(method),
        serialize(serialize),
        insert_after_excs(insert_after_excs),
        insertion_type(insertion_type),
        interaction_size(profiles.size()) {}

  struct FuzzingMetadata {
    uint32_t indegrees{0};
    uint32_t insertion_id{0};
    bool has_values{false}; // to check if a block has had its values filled in
    bool should_be_hot{false}; // to check if a block should be set as hot, used
                               // if a pred is hot and wants to set at least one
                               // succ to hot. If this false, the source block
                               // can be either hot or cold

    [[maybe_unused]] FuzzingMetadata() = default;

    FuzzingMetadata(uint32_t indegrees, uint32_t insertion_id)
        : indegrees(indegrees), insertion_id(insertion_id) {}

    bool operator<(const FuzzingMetadata& r) const {
      if (indegrees == r.indegrees) {
        return insertion_id < r.insertion_id;
      }
      return indegrees < r.indegrees;
    }
  };

  UnorderedMap<Block*, FuzzingMetadata> fuzzing_metadata_map;

  std::vector<SourceBlock::Val> generate_default_data_for_fuzzing(
      Block* /*b*/) {
    // sets all blocks' values to (-1|-1)
    std::vector<SourceBlock::Val> interaction_pairs;
    interaction_pairs.reserve(interaction_size);

    for (size_t i = 0; i < interaction_size; ++i) {
      float hit = -1;
      float appear100 = -1;
      interaction_pairs.emplace_back(hit, appear100);
    }

    return interaction_pairs;
  }

  std::vector<SourceBlock::Val> start_profile(Block* cur) {
    std::vector<SourceBlock::Val> ret;
    bool use_fuzzing = (insertion_type == CustomInsertionType::FUZZING_VALUES);
    std::vector<SourceBlock::Val> fuzzing_values;
    if (use_fuzzing) {
      fuzzing_values = generate_default_data_for_fuzzing(cur);
    }
    ret.reserve(interaction_size);

    for (size_t i = 0; i < interaction_size; ++i) {
      const auto& value_to_insert =
          use_fuzzing ? fuzzing_values.at(i) : global_default_val;
      ret.emplace_back(value_to_insert);
    }
    return ret;
  }

  void start(Block* cur) {
    if (serialize) {
      oss << "(" << id;
    }

    if (fuzzing_metadata_map.find(cur) == fuzzing_metadata_map.end()) {
      fuzzing_metadata_map.insert({cur, FuzzingMetadata(0, 0)});
    }

    auto val = start_profile(cur);

    source_blocks::impl::BlockAccessor::push_source_block(
        cur, std::make_unique<SourceBlock>(method, id, val));
    ++id;

    if (insert_after_excs) {
      insert_after_exceptions_impl(
          cur, method, id, serialize, oss,
          [this, cur]() { return start_profile(cur); });
    }
  }

  void edge(Block* /*cur*/, const Edge* e) {
    if (serialize) {
      oss << " " << get_edge_char(e);
    }
    Block* target = e->target();
    fuzzing_metadata_map.try_emplace(target, 0, 0).first->second.indegrees++;
  }

  void end(Block* /*cur*/) {
    if (serialize) {
      oss << ")";
    }
  }
};

struct RandomGenerator {
  std::random_device dev;
  std::mt19937 random_number_generator;
  std::uniform_real_distribution<> uniform_distribution;
  float cold_to_hot_generation_ratio{0.5f};
  float hot_throw_cold_generation_ratio{0.01f};

  RandomGenerator() = delete;

  explicit RandomGenerator(float cold_to_hot_generation_ratio,
                           float hot_throw_cold_generation_ratio = 0.05f)
      : random_number_generator(dev()),
        uniform_distribution(0.0, 1.0),
        cold_to_hot_generation_ratio(cold_to_hot_generation_ratio),
        hot_throw_cold_generation_ratio(hot_throw_cold_generation_ratio) {}

  explicit RandomGenerator(int seed,
                           const std::string& method_name,
                           float cold_to_hot_generation_ratio,
                           float hot_throw_cold_generation_ratio = 0.05f)
      : random_number_generator(seed ^ std::hash<std::string>{}(method_name)),
        uniform_distribution(0.0, 1.0),
        cold_to_hot_generation_ratio(cold_to_hot_generation_ratio),
        hot_throw_cold_generation_ratio(hot_throw_cold_generation_ratio) {}

  float generate_appear100() {
    return static_cast<float>(uniform_distribution(random_number_generator));
  }

  float generate_block_hit() {
    float hit_percent =
        static_cast<float>(uniform_distribution(random_number_generator));
    if (hit_percent <= cold_to_hot_generation_ratio) {
      return 0.0;
    } else {
      return 1.0;
    }
  }

  // This generates if a block should be converted from hot -> throw -> hot to
  // hot -> throw -> cold
  bool generate_if_convert_hot_throw_cold() {
    float convert_percent =
        static_cast<float>(uniform_distribution(random_number_generator));
    return (convert_percent <= hot_throw_cold_generation_ratio);
  }

  // generates a random size_t between [start, end] inclusive
  size_t generate_random_number_in_range(int start, int end) {
    return start + (size_t)((uniform_distribution(random_number_generator)) *
                            ((end - start) + 1));
  }
};

bool is_hot_block(const Block* block) {
  return has_source_block_positive_val(get_last_source_block(block));
}

void set_block_appear100(Block* block, float appear100) {
  std::vector<SourceBlock*> source_blocks = gather_source_blocks(block);
  for (auto* source_block : source_blocks) {
    source_block->foreach_val([&](auto& val) {
      if (val) {
        val->appear100 = appear100;
      }
    });
  }
}

void set_block_value(Block* block, float hit) {
  std::vector<SourceBlock*> source_blocks = gather_source_blocks(block);
  for (auto* source_block : source_blocks) {

    source_block->foreach_val([&](auto& val) {
      if (val) {
        val->val = hit;
      }
    });
  }
}

int get_number_of_throws_in_block(Block* curr) {
  int count{0};
  for (auto& mie : *curr) {
    if (mie.type == MFLOW_OPCODE && opcode::can_throw(mie.insn->opcode())) {
      count++;
    }
  }
  return count;
}

void set_source_block_value(SourceBlock* source_block, float hit) {
  for (auto* sb = source_block; sb != nullptr; sb = sb->next.get()) {
    sb->foreach_val([&](auto& val) {
      if (val) {
        val->val = hit;
      }
    });
  }
}

struct TopoTraversalHelper {
  CustomValueInsertHelper* value_insert_helper;
  RandomGenerator* generator;
  dominators::SimpleFastDominators<cfg::GraphInterface>* doms;
  ControlFlowGraph* cfg;

  float appear100{0.0f};
  float entry_hit{0.0f};

  explicit TopoTraversalHelper(
      CustomValueInsertHelper* value_insert_helper,
      RandomGenerator* generator,
      dominators::SimpleFastDominators<cfg::GraphInterface>* doms,
      ControlFlowGraph* cfg)
      : value_insert_helper(value_insert_helper),
        generator(generator),
        doms(doms),
        cfg(cfg) {}

  bool all_preds_are_cold(const Block* block) {
    auto& metadata = value_insert_helper->fuzzing_metadata_map;
    for (const auto& edge : block->preds()) {
      auto* pred = edge->src();
      if (!metadata.at(pred).has_values) {
        // If there are no values in this predecessor (cause of cycles) then
        // ignore it
        continue;
      }
      if (is_hot_block(pred)) {
        return false;
      }
    }
    return true;
  }

  // This function takes a block that has already been chosen to be set as hot
  // -> throw -> cold. Since there may be more than 1 throw instruction in a
  // block, this will chose a random throw, and all source blocks from that
  // throw onwards will be cold
  void set_block_as_hot_throw_cold(Block* block, int throw_count) {
    size_t throw_to_convert =
        generator->generate_random_number_in_range(0, throw_count - 1);
    size_t current_throw = 0;
    bool set_hot = true;

    for (auto& mie : *block) {
      if (mie.type == MFLOW_OPCODE && opcode::can_throw(mie.insn->opcode())) {
        if (current_throw >= throw_to_convert) {
          set_hot = false;
        }
        current_throw++;
      }

      if (mie.type == MFLOW_SOURCE_BLOCK) {
        if (set_hot) {
          set_source_block_value(mie.src_block.get(), 1);
        } else {
          set_source_block_value(mie.src_block.get(), 0);
        }
      }
    }
  }

  void set_block_random_value(Block* block) {
    int next_hit = static_cast<int>(generator->generate_block_hit());
    int throw_count = get_number_of_throws_in_block(block);

    if (next_hit == 0 || throw_count == 0) {
      set_block_value(block, static_cast<float>(next_hit));
    } else {
      bool should_convert_to_hot_throw_cold =
          generator->generate_if_convert_hot_throw_cold();
      if (should_convert_to_hot_throw_cold) {
        set_block_as_hot_throw_cold(block, throw_count);
      } else {
        set_block_value(block, static_cast<float>(next_hit));
      }
    }
  }

  // This assumes the last source block is HOT (and has no throws after it), and
  // sets a random child to be HOT
  void set_succ_randomly_hot(Block* block) {
    auto& metadata = value_insert_helper->fuzzing_metadata_map;
    const auto& successors = block->succs();
    size_t successor_size = successors.size();
    size_t next_hot_block_idx = generator->generate_random_number_in_range(
        0, static_cast<int>(successor_size - 1));

    for (size_t i = 0; i < successor_size; ++i) {
      auto* succ_block = successors.at(i)->target();

      if (next_hot_block_idx == i) {
        metadata.at(succ_block).should_be_hot = true;
      }
    }
  }

  void process_block(Block* cur, bool must_be_cold) {
    auto& metadata = value_insert_helper->fuzzing_metadata_map;
    if (cur == cfg->entry_block()) {
      entry_hit = generator->generate_block_hit();
      if (must_be_cold) {
        entry_hit = 0.0;
      }
      appear100 = 0.0;
      if (entry_hit > 0) { // entry_hit is HOT.
        appear100 = generator->generate_appear100();
      }
      set_block_appear100(cur, appear100);
      set_block_value(cur, entry_hit);
      metadata.at(cur).has_values = true;
    } else {
      if (!metadata.at(cur).has_values) {
        // if a block has values, don't need to deal with it again
        // (for example, the entry block).
        if (entry_hit == 0.0f || !is_hot_block(doms->get_idom(cur)) ||
            all_preds_are_cold(cur)) {
          // This block must be listed as COLD now.
          set_block_value(cur, 0);
        } else {
          if (metadata.at(cur).should_be_hot) {
            // This block must be set to HOT now
            set_block_value(cur, 1);
          } else {
            // This block can be either HOT or COLD.
            set_block_random_value(cur);
          }
        }
        set_block_appear100(cur, appear100);
        metadata.at(cur).has_values = true;
      }
    }

    auto* last_source_block_or_throw =
        get_last_source_block_if_after_throw(cur);
    // This is to check if there is a throw after a source block, if there is a
    // throw, last_source_block_or_throw is null, and therefore the successors
    // can be COLD. Otherwise, if there exists a source block at the end of this
    // block and it is hot, then the hot path must continue into at least one
    // successor
    if ((last_source_block_or_throw != nullptr) &&
        has_source_block_positive_val(last_source_block_or_throw)) {
      set_succ_randomly_hot(cur);
    }
  }
};

using InsertionType = CustomValueInsertHelper::CustomInsertionType;

} // namespace

SourceBlockConsistencyCheck& get_sbcc() { return s_sbcc; }

InsertResult insert_source_blocks(DexMethod* method,
                                  ControlFlowGraph* cfg,
                                  const std::vector<ProfileData>& profiles,
                                  bool serialize,
                                  bool insert_after_excs) {
  return insert_source_blocks(&method->get_deobfuscated_name(), cfg, profiles,
                              serialize, insert_after_excs);
}

static std::string get_serialized_idom_map(ControlFlowGraph* cfg) {
  auto doms = dominators::SimpleFastDominators<cfg::GraphInterface>(*cfg);
  std::stringstream ss_idom_map;
  auto cfg_blocks = cfg->blocks();
  bool wrote_first_idom_map_elem = false;
  auto write_idom_map_elem = [&wrote_first_idom_map_elem,
                              &ss_idom_map](uint32_t sb_id, uint32_t idom_id) {
    if (wrote_first_idom_map_elem) {
      ss_idom_map << ";";
    }
    wrote_first_idom_map_elem = true;

    ss_idom_map << sb_id << "->" << idom_id;
  };

  for (cfg::Block* block : cfg->blocks()) {
    if (block == cfg->exit_block() &&
        (cfg->get_pred_edge_of_type(block, EDGE_GHOST) != nullptr)) {
      continue;
    }

    auto* first_sb_in_block = source_blocks::get_first_source_block(block);
    if (first_sb_in_block == nullptr) {
      continue;
    }

    auto* curr_idom = doms.get_idom(block);
    if ((curr_idom != nullptr) && curr_idom != block) {
      if (curr_idom != cfg->exit_block() ||
          (cfg->get_pred_edge_of_type(curr_idom, EDGE_GHOST) == nullptr)) {
        auto* sb_in_idom = source_blocks::get_last_source_block(curr_idom);
        always_assert(sb_in_idom);
        write_idom_map_elem(first_sb_in_block->id, sb_in_idom->id);
      }
    }

    SourceBlock* prev = nullptr;
    source_blocks::foreach_source_block(block, [&](const auto& sb) {
      if (sb != first_sb_in_block) {
        always_assert(prev);
        write_idom_map_elem(sb->id, prev->id);
      }
      prev = sb;
    });
  }

  return ss_idom_map.str();
}

std::tuple<size_t, size_t, size_t, size_t> normalize_blocks(
    ControlFlowGraph* cfg) {
  size_t normalized_blocks = 0;
  size_t denormalized_blocks = 0;
  size_t elided_vals = 0;
  size_t unelided_vals = 0;
  for (auto* block : cfg->blocks()) {
    source_blocks::foreach_source_block(block, [&](const auto& sb) {
      if (sb->normalize(&elided_vals, &unelided_vals)) {
        normalized_blocks++;
      } else {
        denormalized_blocks++;
      }
    });
  }
  return std::make_tuple(normalized_blocks, denormalized_blocks, elided_vals,
                         unelided_vals);
}

InsertResult insert_source_blocks(const DexString* method,
                                  ControlFlowGraph* cfg,
                                  const std::vector<ProfileData>& profiles,
                                  bool serialize,
                                  bool insert_after_excs) {
  InsertHelper helper(method, profiles, serialize, insert_after_excs);

  impl::visit_in_order(
      cfg,
      [&](Block* cur) { helper.start(cur); },
      [&](Block* cur, const Edge* e) { helper.edge(cur, e); },
      [&](Block* cur) { helper.end(cur); });

  bool had_failures = helper.wipe_profile_failures(*cfg);

  auto idom_map = get_serialized_idom_map(cfg);

  auto [normalized_blocks, denormalized_blocks, elided_vals, unelided_vals] =
      normalize_blocks(cfg);
  return {helper.id,     helper.oss.str(),  std::move(idom_map),
          !had_failures, normalized_blocks, denormalized_blocks,
          elided_vals,   unelided_vals};
}

// This metric checks if there exists a block such that it starts out with hot
// source blocks, encounters a throw instruction somewhere, and then has cold
// source blocks. It does this by first checking the first source block is hot,
// and then checking if there has been a throw, then seeing if any subsequent
// source block is cold.
bool block_is_hot_throw_cold(Block* cur) {
  bool seen_src_block = false;
  bool seen_throw = false;
  for (auto& mie : *cur) {
    if (mie.type == MFLOW_OPCODE && opcode::can_throw(mie.insn->opcode())) {
      seen_throw = true;
    }

    if (mie.type == MFLOW_SOURCE_BLOCK) {
      if (!seen_src_block) {
        // Cold initial source blocks do not count here
        if (!has_source_block_positive_val(mie.src_block.get())) {
          return false;
        }
        // If a throw has been seen before the initial source block, this also
        // does not count
        if (seen_throw) {
          return false;
        }
        seen_src_block = true;
      } else {
        // This means a throw has been seen, and the current source block is
        // cold while the initial one is hot
        if (seen_throw && !has_source_block_positive_val(mie.src_block.get())) {
          return true;
        }
      }
    }
  }
  return false;
}

void update_source_block_metric(Block* cur, SourceBlockMetric& metrics) {
  auto source_blocks = gather_source_blocks(cur);
  for (const auto& source_block : source_blocks) {
    if (has_source_block_positive_val(source_block)) {
      metrics.hot_block_count++;
    } else {
      metrics.cold_block_count++;
    }
  }

  if (block_is_hot_throw_cold(cur)) {
    metrics.hot_throw_cold_count++;
  }
}

SourceBlockMetric gather_source_block_metrics(ControlFlowGraph* cfg) {
  SourceBlockMetric metrics = {0, 0, 0};

  impl::visit_in_order(
      cfg,
      [&](Block* cur) { update_source_block_metric(cur, metrics); },
      [&](Block* /*cur*/, const Edge* /*e*/) {},
      [&](Block* /*cur*/) {});

  return metrics;
}

// CustomValueInsertHelper must have the correct indegrees initialized to have
// this work as intended. Running this traversal will also modify the state of
// the CustomValueInsertHelper to have different indegrees
template <typename BlockFn>
void topo_traverse(CustomValueInsertHelper& helper,
                   Block* start_block,
                   const BlockFn& block_fn) {
  auto& metadata = helper.fuzzing_metadata_map;
  auto topo_comparator = [&metadata](Block* l, Block* r) {
    return metadata.at(l) < metadata.at(r);
  };

  // The traversal uses a multiset to be able to process the block with the
  // lowest number of indegrees, and allows updating the position of other nodes
  // in the multiset if their indegrees change during the traversal.
  std::multiset<Block*, decltype(topo_comparator)> process_queue(
      topo_comparator);
  UnorderedSet<Block*> visited;
  uint32_t insertion_order_id = 0;

  block_fn(start_block);
  metadata.at(start_block).insertion_id = insertion_order_id;
  visited.insert(start_block);
  process_queue.insert(start_block);
  ++insertion_order_id;

  while (!process_queue.empty()) {
    auto current = process_queue.begin();
    process_queue.erase(process_queue.begin());

    block_fn(*current);

    for (const auto& edge : (*current)->succs()) {
      auto* neighbor = edge->target();
      bool re_add_neighbor = false;

      if (process_queue.count(neighbor)) {
        // Erasing from the queue and readding allows reordering and updating of
        // the queue if the neighbor's new indegrees gives it more priority now
        process_queue.erase(neighbor);
        re_add_neighbor = true;
      }
      metadata.at(neighbor).indegrees--;
      if (re_add_neighbor) {
        process_queue.insert(neighbor);
      }

      if (!visited.count(neighbor)) {
        metadata.at(neighbor).insertion_id = insertion_order_id;
        ++insertion_order_id;
        visited.insert(neighbor);
        process_queue.insert(neighbor);
      }
    }
  }
}

/*
The follow method runs a topo-traversal of the method's CFG, filling out source
blocks as it goes.

Starting from the entry block, each block gets processed based on the number of
indegrees it has. The lower the number of indegrees, the more priority a block
has. Therefore, a multiset is used as the processing queue because it allows
easy retrieval of the block with the lowest indegrees (stored in the metadata),
and allows updating current blocks and modifying their processing order inside
the processing queue. There might be ties in indegrees, if so, the block that
was first inserted among the tied ones is processed first.

There are a few helpers generated, including a dominator tree to find the
immediate dominator quickly, and a Random Generator to generate fuzzing data.

There are in general a few cases while filling out source block values during
the traversal:

1) In order to determine a source block's values, its predecessor and immediate
dominator values must be known, therefore the traversal must visit and fill
their values out first. This is also why the traversal uses indegrees to
traverse, as it will traverse both the predecessors and immediate dominator of a
block before getting to it.

2) if the immediate dominator is cold OR if all predecessors are cold OR if the
entry block is cold, then the block must be cold, otherwise can be either hot or
cold.

3) all source blocks should have the same appear100 value in the method.
*/
void run_topotraversal_fuzzing(ControlFlowGraph* cfg,
                               CustomValueInsertHelper& helper,
                               const std::string& method_name,
                               bool use_seed,
                               int seed,
                               bool must_be_cold) {

  RandomGenerator generator =
      use_seed ? RandomGenerator(seed, method_name,
                                 helper.cold_to_hot_generation_ratio,
                                 helper.hot_throw_cold_generation_ratio)
               : RandomGenerator(helper.cold_to_hot_generation_ratio,
                                 helper.hot_throw_cold_generation_ratio);
  auto doms = dominators::SimpleFastDominators<cfg::GraphInterface>(*cfg);
  TopoTraversalHelper traversal_helper(&helper, &generator, &doms, cfg);

  topo_traverse(helper, cfg->entry_block(), [&](Block* cur) {
    traversal_helper.process_block(cur, must_be_cold);
  });
}

InsertResult insert_custom_source_blocks(
    const DexString* method,
    ControlFlowGraph* cfg,
    const std::vector<ProfileData>& profiles,
    bool serialize,
    bool insert_after_excs,
    bool enable_fuzzing,
    bool must_be_cold) {
  // If fuzzing is on and must_be_cold is true, then the method's entry hit
  // should be cold, otherwise it should be randomly generated by the
  // RandomGenerator

  InsertionType insertion_type = InsertionType::DEFAULT_VALUES;
  if (enable_fuzzing) {
    insertion_type = InsertionType::FUZZING_VALUES;
  }
  int seed = 5000;
  bool use_seed = true;
  CustomValueInsertHelper helper(method, profiles, serialize, insert_after_excs,
                                 insertion_type);
  impl::visit_in_order(
      cfg,
      [&](Block* cur) { helper.start(cur); },
      [&](Block* cur, const Edge* e) { helper.edge(cur, e); },
      [&](Block* cur) { helper.end(cur); });

  if (insertion_type == InsertionType::FUZZING_VALUES) {
    run_topotraversal_fuzzing(cfg, helper, std::string(method->str()), use_seed,
                              seed, must_be_cold);
  }

  auto idom_map = get_serialized_idom_map(cfg);

  auto [normalized_blocks, denormalized_blocks, elided_vals, unelided_vals] =
      normalize_blocks(cfg);

  return {helper.id,   helper.oss.str(),  std::move(idom_map),
          true,        normalized_blocks, denormalized_blocks,
          elided_vals, unelided_vals};
}

UnorderedMap<Block*, uint32_t> insert_custom_source_blocks_get_indegrees(
    const DexString* method,
    ControlFlowGraph* cfg,
    const std::vector<ProfileData>& profiles,
    bool serialize,
    bool insert_after_excs,
    bool enable_fuzzing) {

  InsertionType insertion_type = InsertionType::DEFAULT_VALUES;
  if (enable_fuzzing) {
    insertion_type = InsertionType::FUZZING_VALUES;
  }
  CustomValueInsertHelper helper(method, profiles, serialize, insert_after_excs,
                                 insertion_type);
  impl::visit_in_order(
      cfg,
      [&](Block* cur) { helper.start(cur); },
      [&](Block* cur, const Edge* e) { helper.edge(cur, e); },
      [&](Block* cur) { helper.end(cur); });

  UnorderedMap<Block*, uint32_t> indegrees;
  for (auto& entry : UnorderedIterable(helper.fuzzing_metadata_map)) {
    Block* cur = entry.first;
    CustomValueInsertHelper::FuzzingMetadata& metadata = entry.second;
    indegrees.emplace(cur, metadata.indegrees);
  }
  return indegrees;
}

void scale_source_blocks(cfg::Block* block) {
  // After duplicating hot successors, some originally hot blocks may no
  // longer be reachable from hot blocks. We'll mark them as cold here.

  // Note that while the currently implemented "scaling" approach via min/max
  // works well when we only consider binary hit-count state values (0 = cold,
  // >0 = hot), and that it doesn't do actual proper scaling yet. A practical
  // problem for that is that we don't know the hotness of edges, and thus
  // cannot correctly attribute hit-counts to the original or duplicated blocks
  // outside of the binary scenario.
  // TODO: Implement proper numeric scaling. This will be especially important
  // once we track (non-binary) block hit counts.

  // Note that we don't have to further deal with dependencies as we are
  // iterating from the front, and have filtered out back-edges.
  auto* template_sb = source_blocks::get_first_source_block(block);
  always_assert(template_sb);
  SourceBlock limit_sb(*template_sb);
  limit_sb.fill(SourceBlock::Val(0, 0));

  for (auto* pred : block->preds()) {
    if (pred->src() == nullptr) {
      continue;
    }

    auto* pred_sb = source_blocks::get_last_source_block(pred->src());
    if (pred_sb == nullptr) {
      // Missing information; give up
      return;
    }

    // `SourceBlock::max` is a bit dubious, as the appear100 values really
    // represent a set
    limit_sb.max(*pred_sb);
  }
  source_blocks::foreach_source_block(block,
                                      [&](auto* sb) { sb->min(limit_sb); });
}

bool has_source_block_positive_val(const SourceBlock* sb) {
  bool any_positive_val = false;
  if (sb != nullptr) {
    sb->foreach_val_early([&any_positive_val](const auto& val) {
      any_positive_val = val && val->val > 0.0f;
      return any_positive_val;
    });
  }
  return any_positive_val;
}

bool has_source_block_undefined_val(const SourceBlock* sb) {
  bool any_undefined_val = false;
  if (sb != nullptr) {
    sb->foreach_val_early([&any_undefined_val](const auto& val) {
      any_undefined_val = !val;
      return any_undefined_val;
    });
  }
  return any_undefined_val;
}

IRList::iterator find_first_block_insert_point(cfg::Block* b) {
  // Do not put source blocks before a (pseudo) move result or load-param-* at
  // the head of a block.
  auto can_insert_source_block_before = [](IROpcode op) {
    return !opcode::is_a_load_param(op) && !opcode::is_move_result_any(op) &&
           !opcode::is_move_exception(op);
  };
  auto it = b->begin();
  while (it != b->end() && it->type == MFLOW_OPCODE &&
         !can_insert_source_block_before(it->insn->opcode())) {
    ++it;
  }
  return it;
}

namespace normalize {

size_t num_interactions(const cfg::ControlFlowGraph& cfg,
                        const SourceBlock* sb) {
  if (g_redex != nullptr) {
    return g_redex->num_sb_interaction_indices();
  }

  auto nums = [](auto* sb) -> std::optional<size_t> {
    return (sb != nullptr) ? std::optional<size_t>(sb->vals_size)
                           : std::nullopt;
  };

  auto caller = nums(sb);
  if (caller) {
    return *caller;
  }
  auto callee = nums(source_blocks::get_first_source_block(cfg.entry_block()));
  if (callee) {
    return *callee;
  }

  return 0;
}

} // namespace normalize

namespace apportion {

std::vector<double> predecessor_totals(const cfg::Block* b, size_t n_slots) {
  std::vector<double> pred_total(n_slots, 0.0);
  for (const cfg::Edge* pe : b->preds()) {
    const auto* psb = source_blocks::get_last_source_block(pe->src());
    if (psb == nullptr) {
      continue;
    }
    for (size_t i = 0; i < n_slots; ++i) {
      pred_total[i] += psb->get_val(i).value_or(0.0f);
    }
  }
  return pred_total;
}

double share_of(const std::vector<double>& pred_total,
                const cfg::Block* src,
                size_t i) {
  const auto* psb = source_blocks::get_last_source_block(src);
  if (psb == nullptr || i >= pred_total.size() || pred_total[i] <= 0.0) {
    return -1.0;
  }
  return psb->get_val(i).value_or(0.0f) / pred_total[i];
}

void scale_val(SourceBlock* sb, size_t i, double f) {
  if (i >= sb->vals_size) {
    return;
  }
  sb->apply_at(i, [f](auto& val) {
    if (val) {
      val->val = static_cast<float>(val->val * f);
    }
  });
}

void shrink_by_departed(cfg::Block* b,
                        const std::vector<double>& leaving_share) {
  source_blocks::foreach_source_block(b, [&](auto* sb) {
    for (size_t i = 0; i < leaving_share.size() && i < sb->vals_size; ++i) {
      scale_val(sb, i, std::clamp(1.0 - leaving_share[i], 0.0, 1.0));
    }
  });
}

} // namespace apportion

SourceBlock* get_first_source_block_of_method(const DexMethod* m) {
  const auto* code = m->get_code();
  if (code->cfg_built()) {
    return get_first_source_block(code->cfg().entry_block());
  } else {
    for (const auto& mie : *code) {
      if (mie.type == MFLOW_SOURCE_BLOCK) {
        return mie.src_block.get();
      }
    };
  }
  return nullptr;
}

SourceBlock* get_any_first_source_block_of_methods(
    const std::vector<const DexMethod*>& methods) {
  for (const auto* m : methods) {
    auto* sb = get_first_source_block_of_method(m);
    if (sb != nullptr) {
      return sb;
    }
  }
  return nullptr;
}

void insert_synthetic_source_blocks_in_method(
    DexMethod* method,
    const std::function<std::unique_ptr<SourceBlock>()>& source_block_creator) {
  auto* code = method->get_code();
  cfg::ScopedCFG cfg(code);

  for (auto* block : cfg->blocks()) {
    if (block == cfg->entry_block()) {
      // Special handling.
      continue;
    }
    auto new_sb = source_block_creator();
    auto it = block->get_first_insn();
    if (it != block->end() && opcode::is_move_result_any(it->insn->opcode())) {
      block->insert_after(it, std::move(new_sb));
    } else {
      block->insert_before(it, std::move(new_sb));
    }
  }

  auto* block = cfg->entry_block();
  auto new_sb = source_block_creator();
  auto it = block->get_first_non_param_loading_insn();
  block->insert_before(it, std::move(new_sb));
}

bool have_same_source_block_counts(const cfg::Block* a, const cfg::Block* b) {
  return gather_source_blocks(a).size() == gather_source_blocks(b).size();
}

bool add_source_blocks_pairwise(cfg::Block* into, const cfg::Block* from) {
  auto into_sbs = gather_source_blocks(into);
  auto from_sbs = gather_source_blocks(from);
  if (into_sbs.size() != from_sbs.size()) {
    return false;
  }
  for (size_t i = 0; i < into_sbs.size(); i++) {
    into_sbs.at(i)->add(*from_sbs.at(i));
  }
  return true;
}

std::unique_ptr<SourceBlock> clone_as_synthetic(SourceBlock* sb,
                                                const DexMethod* ref,
                                                const SourceBlock::Val& val) {
  std::unique_ptr<SourceBlock> new_sb = std::make_unique<SourceBlock>(*sb);
  new_sb->next.reset();
  new_sb->id = SourceBlock::kSyntheticId;
  if (ref != nullptr) {
    new_sb->src = ref->get_deobfuscated_name_or_null();
  }
  new_sb->fill(val);
  return new_sb;
}

std::unique_ptr<SourceBlock> clone_as_synthetic(
    SourceBlock* sb,
    const DexMethod* ref,
    const std::optional<SourceBlock::Val>& opt_val) {
  std::unique_ptr<SourceBlock> new_sb = std::make_unique<SourceBlock>(*sb);
  new_sb->next.reset();
  new_sb->id = SourceBlock::kSyntheticId;
  if (ref != nullptr) {
    new_sb->src = ref->get_deobfuscated_name_or_null();
  }
  if (opt_val) {
    new_sb->fill(*opt_val);
  }
  return new_sb;
}

std::unique_ptr<SourceBlock> clone_as_synthetic(
    SourceBlock* sb,
    const DexMethod* ref,
    const std::vector<SourceBlock*>& many) {
  std::unique_ptr<SourceBlock> new_sb = std::make_unique<SourceBlock>(*sb);
  new_sb->next.reset();
  new_sb->id = SourceBlock::kSyntheticId;
  if (ref != nullptr) {
    new_sb->src = ref->get_deobfuscated_name_or_null();
  }
  new_sb->fill(SourceBlock::Val::none());
  for (const auto& other : many) {
    new_sb->max(*other);
  }
  return new_sb;
}

std::unique_ptr<SourceBlock> clone_as_synthetic_summing(
    SourceBlock* sb,
    const DexMethod* ref,
    const std::vector<SourceBlock*>& many) {
  std::unique_ptr<SourceBlock> new_sb = std::make_unique<SourceBlock>(*sb);
  new_sb->next.reset();
  new_sb->id = SourceBlock::kSyntheticId;
  if (ref != nullptr) {
    new_sb->src = ref->get_deobfuscated_name_or_null();
  }
  new_sb->fill(SourceBlock::Val::none());
  for (const auto& other : many) {
    // N:1 outline: the body runs about the sum of its call sites' counts, so
    // accumulate `val` (appear100 maxes, since it is a probability).
    new_sb->add(*other);
  }
  return new_sb;
}

void adjust_block_hits_with_appear100_threshold(
    ControlFlowGraph* cfg, int32_t block_appear100_threshold) {
  for (auto* block : cfg->blocks()) {
    for (auto& mie : *block) {
      if (mie.type == MFLOW_SOURCE_BLOCK) {
        for (auto* sb = mie.src_block.get(); sb != nullptr;
             sb = sb->next.get()) {
          sb->foreach_val([&](auto& val) {
            if (val && val->appear100 < block_appear100_threshold) {
              val->val = 0;
            }
          });
        }
      }
    }
  }
}

std::vector<float> gather_block_counts(
    const std::vector<DexClass*>& scope,
    const std::function<bool(DexMethod*, cfg::Block*)>& include) {
  InsertOnlyConcurrentMap<DexMethod*, std::vector<float>> per_method;
  walk::parallel::code(scope, [&](DexMethod* method, IRCode& code) {
    if (!code.cfg_built()) {
      return;
    }
    std::vector<float> counts;
    for (auto* b : code.cfg().blocks()) {
      if (include && !include(method, b)) {
        continue;
      }
      auto c = max_val_over_interactions(get_first_source_block(b));
      if (c && *c > 0.0f) {
        counts.push_back(*c);
      }
    }
    if (!counts.empty()) {
      per_method.emplace(method, std::move(counts));
    }
  });
  std::vector<float> all;
  for (auto&& p : UnorderedIterable(per_method)) {
    all.insert(all.end(), p.second.begin(), p.second.end());
  }
  return all;
}

} // namespace source_blocks
