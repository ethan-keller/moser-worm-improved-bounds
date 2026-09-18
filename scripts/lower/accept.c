/* Untrusted LP proposals. Acceptance is rechecked by the ordinary exact guard. */
#include "simplex.h"
#include <stdint.h>
#include "accept.h"

static int simplex_budget;
static uint64_t mix_attempts, mix_pools, mix_solves, mix_successes, mix_pivot_count;

static int budgeted_simplex(int members, int axes, const double intercept[MIX_MEMBERS],
                            double gradient[MIX_MEMBERS][MIX_AXES],
                            const double penalty[MIX_AXES],
                            double weight[MIX_MEMBERS], unsigned *pivots) {
    if (simplex_budget == 0) return 0;
    --simplex_budget;
    ++mix_solves;
    int result = mix_simplex(members, axes, intercept, gradient, penalty, weight, pivots);
    mix_pivot_count += *pivots;
    return result;
}

#define mix_simplex budgeted_simplex
#define main search_cli_main
#include "search.c"
#undef main
#undef mix_simplex

static Context parent_context;
static Interval prepared_box[9];
static int prepared;

int lower_accept_prepare(const int64_t raw[18]) {
    prepared = 0;
    for (int i = 0; i < 9; ++i) {
        prepared_box[i] = (Interval){raw[2*i], raw[2*i+1]};
        if (prepared_box[i].lo > prepared_box[i].hi) return 0;
    }
    prepared = prepare(&parent_context, prepared_box);
    return prepared;
}

/* Return accepted weights and label orders, including any fan-anchor rotation. */
int lower_accept_try(int count, const int64_t *raw, int64_t accepted[361]) {
    if (count < 1 || count > MEMBERS) return 0;
    Leaf leaf = {.count = count};
    int at = 0;
    for (int k = 0; k < count; ++k) {
        leaf.weight[k] = raw[at++];
        int64_t n = raw[at++];
        if (n < 3 || n > 13) return 0;
        leaf.cycle[k].count = (int)n;
        for (int i = 0; i < n; ++i) {
            int64_t label = raw[at++];
            if (label < 0 || label >= 13) return 0;
            leaf.cycle[k].label[i] = (uint8_t)label;
        }
    }
    Polynomial polynomial;
    if (!weighted_polynomial(&parent_context, &leaf, &polynomial) ||
        (Wide)1000*lower_bound(&polynomial) < (Wide)239*ONE) return 0;
    at = 0;
    accepted[at++] = leaf.count;
    for (int k = 0; k < leaf.count; ++k) {
        accepted[at++] = leaf.weight[k];
        accepted[at++] = leaf.cycle[k].count;
        for (int i = 0; i < leaf.cycle[k].count; ++i)
            accepted[at++] = leaf.cycle[k].label[i];
    }
    return at;
}

/* Up to 16 descendant witnesses, each with <=24 members. The LP pool has <=24
   distinct members whose exact fan conditions hold on the prepared parent. */
int lower_accept_mix(int count, const int64_t *raw, int64_t accepted[361]) {
    if (!prepared || count < 1 || count > 16*MEMBERS) return 0;
    ++mix_attempts;
    MixturePool pool = {.count = 0};
    int at = 0;
    for (int k = 0; k < count; ++k) {
        int64_t n = raw[at++];
        if (n < 3 || n > 13) return 0;
        Cycle cycle = {.count = (int)n};
        unsigned used = 0;
        for (int j = 0; j < n; ++j) {
            int64_t label = raw[at++];
            if (label < 0 || label >= 13 || (used & (1u << label))) return 0;
            used |= 1u << label;
            cycle.label[j] = (uint8_t)label;
        }
        add_member(&parent_context, &pool, cycle);
    }
    if (pool.count < 2) return 0;
    ++mix_pools;
    simplex_budget = 1;
    Leaf leaf = {.count = 0};
    int axis = 0;
    int64_t best = INT64_MIN;
    /* Existing optimize_pool; budgeted_simplex permits at most one actual solve.
       depth=7 suppresses the unused split-axis hint on failed candidates. */
    if (!optimize_pool(&parent_context, prepared_box, &pool, &leaf, &axis, 7, &best))
        return 0;
    int64_t input[360];
    at = 0;
    for (int k = 0; k < leaf.count; ++k) {
        input[at++] = leaf.weight[k];
        input[at++] = leaf.cycle[k].count;
        for (int j = 0; j < leaf.cycle[k].count; ++j)
            input[at++] = leaf.cycle[k].label[j];
    }
    /* Recheck and serialize with the unmodified production adapter. */
    int result = lower_accept_try(leaf.count, input, accepted);
    if (result) ++mix_successes;
    return result;
}

void lower_mix_reset(void) {
    mix_attempts = mix_pools = mix_solves = mix_successes = mix_pivot_count = 0;
}

void lower_mix_stats(uint64_t out[5]) {
    out[0] = mix_attempts;
    out[1] = mix_pools;
    out[2] = mix_solves;
    out[3] = mix_successes;
    out[4] = mix_pivot_count;
}
