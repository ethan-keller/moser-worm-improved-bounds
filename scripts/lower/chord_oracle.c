/* Untrusted pruning oracle. Every emitted certificate still requires Lean.
   This translation unit reuses the original fixed-point arithmetic unchanged. */
#include "chord_oracle.h"
#define MOSER_ACCEPT_API
#define lower_accept_prepare chord_existing_prepare
#include "accept.c"
#undef lower_accept_prepare
#undef MOSER_ACCEPT_API

/* Same prepared context and angle guards, with finite translation bounds
   containing the normalized domain. Failure invalidates the previous box. */
int lower_accept_prepare(const int64_t raw[18]) {
    prepared = 0;
    if (!raw) return 0;
    for (int i = 0; i < 9; ++i) {
        Wide lo = raw[2*i], hi = raw[2*i+1];
        if (lo > hi) return 0;
        if (i < 3) {
            Wide mid = lo + (hi-lo)/2;
            Wide radius = hi-mid > mid-lo ? hi-mid : mid-lo;
            if (mid < -64*(Wide)ONE || mid > 64*(Wide)ONE || radius > PI2) return 0;
        } else if (lo < -ONE || hi > ONE) return 0;
    }
    return chord_existing_prepare(raw);
}

static int chord_label(int label) { return label >= 0 && label < 13; }

static void chord_position(int label, Interval out[2]) {
    Vertex v = parent_context.point[label];
    if (v.body < 0) { out[0] = v.x; out[1] = v.y; return; }
    const Interval *q = parent_context.variable + 4*v.body;
    out[0] = add(q[0], sub(mul(q[2], v.x), mul(q[3], v.y)));
    out[1] = add(q[1], add(mul(q[3], v.x), mul(q[2], v.y)));
}

/* Actual a-b: cancel the shared translation before interval evaluation. */
static void chord_difference(int a, int b, Interval out[2]) {
    Vertex v = parent_context.point[a], w = parent_context.point[b];
    if (v.body >= 0 && v.body == w.body) {
        Interval x = sub(v.x, w.x), y = sub(v.y, w.y);
        const Interval *q = parent_context.variable + 4*v.body;
        out[0] = sub(mul(q[2], x), mul(q[3], y));
        out[1] = add(mul(q[3], x), mul(q[2], y));
    } else {
        Interval x[2], y[2];
        chord_position(a, x); chord_position(b, y);
        out[0] = sub(x[0], y[0]); out[1] = sub(x[1], y[1]);
    }
}

int64_t lower_chord_fan(int a, int b, int c) {
    if (!prepared || !chord_label(a) || !chord_label(b) || !chord_label(c))
        return INT64_MIN;
    Interval x[2], y[2];
    chord_difference(b, a, x); chord_difference(c, a, y);
    int64_t direct = sub(mul(x[0], y[1]), mul(x[1], y[0])).lo;
    int64_t centered = fan_bound(&parent_context, a, b, c);
    return direct > centered ? direct : centered;
}

int lower_chord_nonzero(int a, int b) {
    if (!prepared || !chord_label(a) || !chord_label(b) || a == b) return 0;
    Interval d[2];
    chord_difference(b, a, d);
    return d[0].lo > 0 || d[0].hi < 0 || d[1].lo > 0 || d[1].hi < 0;
}

static int64_t chord_area(int count, const int64_t *raw, size_t words) {
    if (!prepared || !raw || count < 1 || count > MEMBERS || words > 360)
        return INT64_MIN;
    Polynomial p = {0};
    Wide total = 0;
    size_t at = 0;
    for (int k = 0; k < count; ++k) {
        if (words-at < 2) return INT64_MIN;
        int64_t weight = raw[at++], n = raw[at++];
        if (weight < 0 || weight > ONE || n < 3 || n > 13) return INT64_MIN;
        total += weight;
        if (total > ONE || (size_t)n > words-at) return INT64_MIN;
        Cycle cycle = {.count = (int)n};
        unsigned used = 0;
        for (int j = 0; j < n; ++j) {
            int64_t label = raw[at++];
            if (label < 0 || label >= 13 || (used & (1u << label))) return INT64_MIN;
            used |= 1u << label;
            cycle.label[j] = (uint8_t)label;
        }
        /* No fan test, rotation, renormalization, or post-centering weighting. */
        area_polynomial(&parent_context, &p, cycle, weight);
    }
    if (at != words) return INT64_MIN;
    return lower_bound(&p);
}

/* Exact packed length; rejects truncated and trailing data before reading it. */
int64_t lower_chord_area_sized(int count, const int64_t *raw, size_t words) {
    return chord_area(count, raw, words);
}
