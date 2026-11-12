/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DedupBlocksPass.h"

#include "Debug.h"
#include "DexUtil.h"
#include "PassManager.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"

namespace {
const char* METRIC_BLOCKS_REMOVED = "blocks_removed";
const char* METRIC_INSNS_REMOVED = "insns_removed";
const char* METRIC_BLOCKS_SPLIT = "blocks_split";
const char* METRIC_POSITIONS_INSERTED = "positions_inserted";
const char* METRIC_POSITIONS_MERGED_WITHOUT_CORRESPONDENCE =
    "positions_merged_without_correspondence";
const char* METRIC_ELIGIBLE_BLOCKS = "eligible_blocks";
} // namespace

void DedupBlocksPass::run_pass(DexStoresVector& stores,
                               ConfigFiles& /* unused */,
                               PassManager& mgr) {
  const auto& scope = build_class_scope(stores);

  const auto stats = walk::parallel::methods<dedup_blocks_impl::Stats>(
      scope,
      [&](DexMethod* method) {
        auto* const code = method->get_code();
        if (code == nullptr || m_config.method_blocklist.count(method) != 0 ||
            method->rstate.no_optimizations()) {
          return dedup_blocks_impl::Stats();
        }

        TRACE(DEDUP_BLOCKS, 3, "[dedup blocks] method %s", SHOW(method));
        always_assert(code->cfg_built());
        auto& cfg = code->cfg();

        TRACE(DEDUP_BLOCKS, 5, "[dedup blocks] method %s before:\n%s",
              SHOW(method), SHOW(cfg));

        dedup_blocks_impl::DedupBlocks impl(&m_config, method);
        impl.run();

        return impl.get_stats();
      },
      m_config.debug ? 1 : redex_parallel::default_num_threads());

  report_stats(mgr, stats);
}

void DedupBlocksPass::report_stats(PassManager& mgr,
                                   const dedup_blocks_impl::Stats& stats) {
  int eligible_blocks = stats.eligible_blocks;
  int removed = stats.blocks_removed;
  int insns_removed = stats.insns_removed;
  int split = stats.blocks_split;
  int positions_inserted = stats.positions_inserted;
  int positions_merged_without_correspondence =
      stats.positions_merged_without_correspondence;
  mgr.incr_metric(METRIC_ELIGIBLE_BLOCKS, eligible_blocks);
  mgr.incr_metric(METRIC_BLOCKS_REMOVED, removed);
  mgr.incr_metric(METRIC_INSNS_REMOVED, insns_removed);
  mgr.incr_metric(METRIC_BLOCKS_SPLIT, split);
  mgr.incr_metric(METRIC_POSITIONS_INSERTED, positions_inserted);
  mgr.incr_metric(positions::metrics::kMarkedUnreliable,
                  stats.join_stats.marked_unreliable);
  mgr.incr_metric(positions::metrics::kNotRecorded,
                  stats.join_stats.not_recorded);
  mgr.incr_metric(METRIC_POSITIONS_MERGED_WITHOUT_CORRESPONDENCE,
                  positions_merged_without_correspondence);
  TRACE(DEDUP_BLOCKS, 2, "%d eligible_blocks", eligible_blocks);

  for (const auto& entry : UnorderedIterable(stats.dup_sizes)) {
    TRACE(DEDUP_BLOCKS,
          2,
          "found %zu duplicate blocks with %zu instructions",
          entry.second,
          entry.first);
  }

  TRACE(DEDUP_BLOCKS, 1, "%d blocks split", split);
  TRACE(DEDUP_BLOCKS, 1, "%d blocks removed", removed);
}

static DedupBlocksPass s_pass;
