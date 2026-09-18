/* Search placement boxes for weighted polygon-area bounds of at least 239/1000.
   Interval arithmetic checks candidates, LP proposes weights, and unresolved
   boxes are bisected. This untrusted generator emits trees for independent
   Lean kernel checking. */
#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <math.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "simplex.h"

typedef __int128 Wide;
typedef struct { int64_t lo, hi; } Interval;
typedef struct { Interval x, y; int body; } Vertex;
typedef struct { int count; uint8_t label[13]; } Cycle;
typedef struct { int count; Cycle cycle[24]; int64_t weight[24]; } Leaf;

#define ONE INT64_C(72057594037927936)
#define PI2 INT64_C(113187804032455044)
#define PI4 INT64_C(56593902016227522)
#define COEFFICIENTS 169
#define CONSTANT 168
#define EDGE_TERMS 32
#define MEMBERS MIX_MEMBERS
#ifndef MOSER_LP_FULL_FIRST
#define MOSER_LP_FULL_FIRST 0
#endif

#include "data.h"

static const Interval one = {ONE, ONE}, half = {ONE / 2, ONE / 2};
static uint64_t nodes, leaves, node_limit;
static uint64_t mixtures, lp_calls, lp_failures, lp_pivots, lp_limits;
static uint64_t hint_checks, hint_accepts;
static uint64_t radial_calls, radial_candidates, radial_accepts;
static int depth_limit;
static int reached_depth;
static const char *stop_reason = "complete";
static clock_t started;
static FILE *output;
static uint64_t holes;

static void fail(const char *message) {
    fprintf(stderr, "%s\n", message);
    exit(2);
}

static int64_t narrow(Wide x) {
    if (x < INT64_MIN || x > INT64_MAX) fail("generator integer overflow");
    return (int64_t)x;
}

static int64_t floor_div(Wide n, int64_t d) {
    return narrow(n >= 0 ? n / d : -((-n + d - 1) / d));
}

static int64_t ceil_div(Wide n, int64_t d) {
    return narrow(-(Wide)floor_div(-n, d));
}

static Interval point(int64_t n) { return (Interval){n, n}; }
static Interval add(Interval a, Interval b) {
    return (Interval){narrow((Wide)a.lo + b.lo), narrow((Wide)a.hi + b.hi)};
}
static Interval neg(Interval a) {
    return (Interval){narrow(-(Wide)a.hi), narrow(-(Wide)a.lo)};
}
static Interval sub(Interval a, Interval b) { return add(a, neg(b)); }

static Interval mul(Interval a, Interval b) {
    Wide products[4] = {(Wide)a.lo*b.lo, (Wide)a.lo*b.hi, (Wide)a.hi*b.lo, (Wide)a.hi*b.hi};
    Wide lo = products[0], hi = products[0];
    for (int i = 1; i < 4; ++i) {
        if (products[i] < lo) lo = products[i];
        if (products[i] > hi) hi = products[i];
    }
    return (Interval){floor_div(lo, ONE), ceil_div(hi, ONE)};
}

static int64_t magnitude(Interval a) {
    Wide lo = a.lo < 0 ? -(Wide)a.lo : a.lo;
    Wide hi = a.hi < 0 ? -(Wide)a.hi : a.hi;
    return narrow(lo > hi ? lo : hi);
}

static int64_t midpoint(Interval a) { return narrow((Wide)a.lo + ((Wide)a.hi-a.lo)/2); }
static int64_t radius(Interval a) {
    int64_t mid = midpoint(a);
    return narrow((Wide)a.hi-mid > (Wide)mid-a.lo ? (Wide)a.hi-mid : (Wide)mid-a.lo);
}

static Interval square(Interval a) {
    if (a.lo >= 0) return (Interval){floor_div((Wide)a.lo*a.lo, ONE), ceil_div((Wide)a.hi*a.hi, ONE)};
    if (a.hi <= 0) return square(neg(a));
    int64_t hi = magnitude(a);
    return (Interval){0, ceil_div((Wide)hi*hi, ONE)};
}

static Interval clamp(Interval a) {
    if (a.lo < -ONE) a.lo = -ONE;
    if (a.hi > ONE) a.hi = ONE;
    return a;
}

static Interval horner(Interval x, const int64_t *c, int n) {
    Interval result = {c[n-1], c[n-1]+1};
    for (int i = n-2; i >= 0; --i) result = sub((Interval){c[i], c[i]+1}, mul(x, result));
    return result;
}

static void sincos_interval(int64_t t, Interval *s, Interval *c) {
    static const int64_t sc[] = {
        12009599006321322, 600479950316066, 14297141674192, 198571412141,
        1805194655, 11571760, 55103, 202
    };
    static const int64_t cc[] = {
        36028797018963968, 3002399751580330, 100079991719344, 1787142709274,
        19857141214, 150432887, 826554, 3443, 11
    };
    if (t < -64*ONE || t > 64*ONE) fail("angle outside the proved range");
    int64_t k = floor_div((Wide)t+PI4, PI2);
    Interval residual = {0, 0};
    for (int iteration = 0; iteration <= 8; ++iteration) {
        residual = k >= 0
            ? (Interval){narrow((Wide)t-k*(Wide)(PI2+1)), narrow((Wide)t-k*(Wide)PI2)}
            : (Interval){narrow((Wide)t-k*(Wide)PI2), narrow((Wide)t-k*(Wide)(PI2+1))};
        if (iteration == 8) break;
        if (residual.hi > PI4+64) ++k;
        else if (residual.lo < -PI4-64) --k;
        else break;
    }
    Interval x2 = square(residual);
    Interval sine = mul(residual, sub(one, mul(x2, horner(x2, sc, 8))));
    Interval cosine = sub(one, mul(x2, horner(x2, cc, 9)));
    --sine.lo; ++sine.hi; --cosine.lo; ++cosine.hi;
    switch ((k % 4 + 4) % 4) {
        case 0: *s = sine; *c = cosine; break;
        case 1: *s = cosine; *c = neg(sine); break;
        case 2: *s = neg(sine); *c = neg(cosine); break;
        default: *s = neg(cosine); *c = sine;
    }
    *s = clamp(*s); *c = clamp(*c);
}

typedef struct { Interval coefficient[COEFFICIENTS]; } Polynomial;
typedef struct {
    uint8_t count, index[EDGE_TERMS];
    Interval coefficient[EDGE_TERMS];
} CachedEdge;
typedef struct {
    Vertex point[13];
    Interval variable[12], affine[24], products[576];
    uint8_t cached[576];
    int64_t fan[13*13*13];
    uint8_t fan_cached[13*13*13];
    double x[13], y[13];
    uint8_t edge_cached[2][13*13];
    CachedEdge edges[2][13*13];
} Context;

static int prepare(Context *ctx, const Interval box[9]) {
    memset(ctx, 0, offsetof(Context, edges));
    for (int i = 0; i < 9; ++i) if (box[i].lo > box[i].hi) return 0;
    memcpy(ctx->point, base_vertices, sizeof(base_vertices));
    for (int body = 0; body < 3; ++body) {
        int64_t mid = midpoint(box[body]), r = radius(box[body]);
        if (mid < -64*ONE || mid > 64*ONE || r < 0 || r > PI2) return 0;
        Interval s, c;
        sincos_interval(mid, &s, &c);
        for (int j = 0; j < 13; ++j) if (ctx->point[j].body == body) {
            Interval x = ctx->point[j].x, y = ctx->point[j].y;
            ctx->point[j].x = sub(mul(c, x), mul(s, y));
            ctx->point[j].y = add(mul(s, x), mul(c, y));
        }
        sincos_interval(r, &s, &c);
        ctx->variable[4*body] = box[3+2*body];
        ctx->variable[4*body+1] = box[4+2*body];
        ctx->variable[4*body+2] = (Interval){c.lo, ONE};
        ctx->variable[4*body+3] = (Interval){-s.hi, s.hi};
    }
    for (int i = 0; i < 12; ++i) {
        ctx->affine[2*i] = point(midpoint(ctx->variable[i]));
        ctx->affine[2*i+1] = point(radius(ctx->variable[i]));
    }
    for (int j = 0; j < 13; ++j) {
        ctx->x[j] = (double)midpoint(ctx->point[j].x)/ONE;
        ctx->y[j] = (double)midpoint(ctx->point[j].y)/ONE;
        int body = ctx->point[j].body;
        if (body >= 0) {
            ctx->x[j] += (double)midpoint(box[3+2*body])/ONE;
            ctx->y[j] += (double)midpoint(box[4+2*body])/ONE;
        }
    }
    return 1;
}

static int coefficient_index(int i, int j) {
    if (i > j) { int temporary = i; i = j; j = temporary; }
    return i*13+j;
}

static void add_coefficient(Polynomial *p, int i, int j, Interval a) {
    int index = coefficient_index(i, j);
    p->coefficient[index] = add(p->coefficient[index], a);
}

static Interval affine_product(Context *ctx, int i, int j) {
    int index = i*24+j;
    if (!ctx->cached[index]) {
        ctx->products[index] = mul(ctx->affine[i], ctx->affine[j]);
        ctx->cached[index] = 1;
    }
    return ctx->products[index];
}

static void term(Context *ctx, Polynomial *p, Interval a, int i, int j, int area, int64_t weight) {
    if (a.lo == 0 && a.hi == 0) return;
    if (area) a = mul(point(weight), mul(half, a));
    if (i == 12 && j == 12) {
        add_coefficient(p, 12, 12, a);
    } else if (i == 12 || j == 12) {
        int k = i == 12 ? j : i;
        add_coefficient(p, 12, 12, mul(a, ctx->affine[2*k]));
        add_coefficient(p, k, 12, mul(a, ctx->affine[2*k+1]));
    } else {
        add_coefficient(p, 12, 12, mul(a, affine_product(ctx, 2*i, 2*j)));
        add_coefficient(p, i, 12, mul(a, affine_product(ctx, 2*i+1, 2*j)));
        add_coefficient(p, j, 12, mul(a, affine_product(ctx, 2*i, 2*j+1)));
        add_coefficient(p, i, j, mul(a, affine_product(ctx, 2*i+1, 2*j+1)));
    }
}

typedef struct { int variable; Interval coefficient; } LinearTerm;

static void xy_terms(Vertex v, LinearTerm x[3], LinearTerm y[3]) {
    int k = 4*v.body;
    x[0] = (LinearTerm){k, one}; x[1] = (LinearTerm){k+2, v.x}; x[2] = (LinearTerm){k+3, neg(v.y)};
    y[0] = (LinearTerm){k+1, one}; y[1] = (LinearTerm){k+2, v.y}; y[2] = (LinearTerm){k+3, v.x};
}

static void edge(Context *ctx, Polynomial *p, int a, int b, int area, int64_t weight) {
    Vertex v = ctx->point[a], w = ctx->point[b];
    if (v.body < 0 && w.body < 0) {
        term(ctx, p, sub(mul(v.x, w.y), mul(v.y, w.x)), 12, 12, area, weight);
    } else if (v.body < 0 || w.body < 0) {
        LinearTerm x[3], y[3];
        Vertex fixed = v.body < 0 ? v : w, moving = v.body < 0 ? w : v;
        xy_terms(moving, x, y);
        for (int k = 0; k < 3; ++k) {
            Interval ax = v.body < 0 ? neg(fixed.y) : fixed.y;
            Interval ay = v.body < 0 ? fixed.x : neg(fixed.x);
            term(ctx, p, mul(ax, x[k].coefficient), x[k].variable, 12, area, weight);
            term(ctx, p, mul(ay, y[k].coefficient), y[k].variable, 12, area, weight);
        }
    } else if (v.body == w.body) {
        int k = 4*v.body;
        term(ctx, p, sub(mul(v.x, w.y), mul(v.y, w.x)), 12, 12, area, weight);
        term(ctx, p, sub(w.y, v.y), k, k+2, area, weight);
        term(ctx, p, sub(w.x, v.x), k, k+3, area, weight);
        term(ctx, p, sub(v.x, w.x), k+1, k+2, area, weight);
        term(ctx, p, sub(w.y, v.y), k+1, k+3, area, weight);
    } else {
        LinearTerm vx[3], vy[3], wx[3], wy[3];
        xy_terms(v, vx, vy); xy_terms(w, wx, wy);
        for (int i = 0; i < 3; ++i) for (int j = 0; j < 3; ++j) {
            term(ctx, p, mul(vx[i].coefficient, wy[j].coefficient),
                 vx[i].variable, wy[j].variable, area, weight);
            term(ctx, p, neg(mul(vy[i].coefficient, wx[j].coefficient)),
                 vy[i].variable, wx[j].variable, area, weight);
        }
    }
}

static int64_t lower_bound(const Polynomial *p) {
    Wide result = p->coefficient[CONSTANT].lo;
    /* coefficient_index stores every nonconstant term in the upper triangle. */
    for (int i = 0; i < 12; ++i)
        for (int j = i; j < 13; ++j)
            result -= magnitude(p->coefficient[i*13+j]);
    return narrow(result);
}

static void area_polynomial(Context *ctx, Polynomial *p, Cycle cycle, int64_t weight) {
    for (int i = 0; i < cycle.count; ++i)
        edge(ctx, p, cycle.label[i], cycle.label[(i+1)%cycle.count], 1, weight);
}

/* Keep determinant and half-area rounding separate. Weighted reconstruction
   uses edge directly; these caches only sum exact unweighted coefficients. */
static void cached_edge(Context *ctx, Polynomial *p, int a, int b, int area) {
    int index = a*13+b;
    CachedEdge *cached = &ctx->edges[area][index];
    if (!ctx->edge_cached[area][index]) {
        Polynomial edge_polynomial = {0};
        edge(ctx, &edge_polynomial, a, b, area, ONE);
        cached->count = 0;
        for (int j = 0; j < COEFFICIENTS; ++j) {
            Interval value = edge_polynomial.coefficient[j];
            if (value.lo == 0 && value.hi == 0) continue;
            if (cached->count >= EDGE_TERMS) fail("edge cache overflow");
            int k = cached->count++;
            cached->index[k] = (uint8_t)j;
            cached->coefficient[k] = value;
        }
        ctx->edge_cached[area][index] = 1;
    }
    for (int j = 0; j < cached->count; ++j) {
        int k = cached->index[j];
        p->coefficient[k] = add(p->coefficient[k], cached->coefficient[j]);
    }
}

static void cached_area_polynomial(Context *ctx, Polynomial *p, Cycle cycle) {
    for (int i = 0; i < cycle.count; ++i)
        cached_edge(ctx, p, cycle.label[i], cycle.label[(i+1)%cycle.count], 1);
}

static int64_t fan_bound(Context *ctx, int a, int b, int c) {
    /* Cyclic rotations have the same three exact edge contributions. */
    if (b < a && b < c) {
        int first = a; a = b; b = c; c = first;
    } else if (c < a && c < b) {
        int first = a; a = c; c = b; b = first;
    }
    int index = (a*13+b)*13+c;
    if (ctx->fan_cached[index]) return ctx->fan[index];
    Polynomial p = {0};
    cached_edge(ctx, &p, a, b, 0); cached_edge(ctx, &p, b, c, 0); cached_edge(ctx, &p, c, a, 0);
    int64_t bound = lower_bound(&p);
    ctx->fan[index] = bound;
    ctx->fan_cached[index] = 1;
    return bound;
}

static int fan_valid(Context *ctx, Cycle *cycle) {
    if (cycle->count == 3 || cycle->count == 4 || cycle->count == 5) return 1;
    for (int rotation = 0; rotation < cycle->count; ++rotation) {
        int valid = 1, a = cycle->label[0], b = cycle->label[1];
        for (int j = 2; j < cycle->count && valid; ++j)
            valid = fan_bound(ctx, a, b, cycle->label[j]) > 0;
        for (int j = 2; j+1 < cycle->count && valid; ++j)
            valid = fan_bound(ctx, a, cycle->label[j], cycle->label[j+1]) > 0;
        if (valid) return 1;
        uint8_t first = cycle->label[0];
        memmove(cycle->label, cycle->label+1, (size_t)(cycle->count-1));
        cycle->label[cycle->count-1] = first;
    }
    return 0;
}

static double cross(Context *ctx, int a, int b, int c) {
    return (ctx->x[b]-ctx->x[a])*(ctx->y[c]-ctx->y[a])
        - (ctx->y[b]-ctx->y[a])*(ctx->x[c]-ctx->x[a]);
}

/* Proposal filter only. Start at the strongest midpoint fan; the interval
   guard below still checks every emitted polygon on the whole box. */
static int midpoint_fan(Context *ctx, Cycle *cycle) {
    if (cycle->count <= 5) return 1;
    double best = 0;
    int start = -1, n = cycle->count;
    for (int r = 0; r < n; ++r) {
        int a = cycle->label[r], b = cycle->label[(r+1)%n];
        double margin = INFINITY;
        for (int j = 2; j < n && margin > best; ++j)
            margin = fmin(margin, cross(ctx, a, b, cycle->label[(r+j)%n]));
        for (int j = 2; j+1 < n && margin > best; ++j)
            margin = fmin(margin, cross(ctx, a, cycle->label[(r+j)%n],
                                        cycle->label[(r+j+1)%n]));
        if (margin > best) { best = margin; start = r; }
    }
    if (start < 0) return 0;
    Cycle original = *cycle;
    for (int i = 0; i < n; ++i) cycle->label[i] = original.label[(start+i)%n];
    return 1;
}

static Cycle convex_hull(Context *ctx) {
    int order[13], chain[26], count = 0;
    for (int i = 0; i < 13; ++i) {
        int j = i;
        while (j > 0 && (ctx->x[i] < ctx->x[order[j-1]] ||
               (ctx->x[i] == ctx->x[order[j-1]] && ctx->y[i] < ctx->y[order[j-1]]))) {
            order[j] = order[j-1]; --j;
        }
        order[j] = i;
    }
    for (int i = 0; i < 13; ++i) {
        while (count >= 2 && cross(ctx, chain[count-2], chain[count-1], order[i]) <= 0) --count;
        chain[count++] = order[i];
    }
    int lower = count;
    for (int i = 11; i >= 0; --i) {
        while (count > lower && cross(ctx, chain[count-2], chain[count-1], order[i]) <= 0) --count;
        chain[count++] = order[i];
    }
    Cycle result = {.count = count-1};
    for (int i = 0; i < result.count; ++i) result.label[i] = (uint8_t)chain[i];
    return result;
}

static double cycle_area(Context *ctx, Cycle cycle) {
    double area = 0;
    for (int i = 0; i < cycle.count; ++i) {
        int a = cycle.label[i], b = cycle.label[(i+1)%cycle.count];
        area += ctx->x[a]*ctx->y[b] - ctx->y[a]*ctx->x[b];
    }
    return area/2;
}

typedef struct { Cycle cycle; double area; } Candidate;

static int same_cycle(Cycle a, Cycle b) {
    if (a.count != b.count) return 0;
    for (int start = 0; start < b.count; ++start) {
        if (b.label[start] != a.label[0]) continue;
        int equal = 1;
        for (int j = 1; j < a.count; ++j)
            if (a.label[j] != b.label[(start+j)%b.count]) { equal = 0; break; }
        if (equal) return 1;
    }
    return 0;
}

static void keep_candidate(Context *ctx, Candidate list[MEMBERS], int *count, Cycle cycle) {
    double area = cycle_area(ctx, cycle);
    if (*count == MEMBERS && area <= list[*count-1].area) return;
    if (!midpoint_fan(ctx, &cycle)) return;
    for (int i = 0; i < *count; ++i) if (same_cycle(cycle, list[i].cycle)) return;
    int position = *count < MEMBERS ? (*count)++ : MEMBERS-1;
    while (position > 0 && area > list[position-1].area) {
        list[position] = list[position-1]; --position;
    }
    list[position] = (Candidate){cycle, area};
}

typedef struct {
    Cycle cycle;
    double area;
    int64_t bound, margin, score;
    int selected;
} RankedCandidate;

/* Encode cyclic order from its smallest label; reversal remains distinct. */
static uint64_t cycle_key(Cycle cycle) {
    int start = 0;
    for (int i = 1; i < cycle.count; ++i)
        if (cycle.label[i] < cycle.label[start]) start = i;
    uint64_t key = (unsigned)cycle.count;
    for (int i = 0; i < cycle.count; ++i)
        key |= (uint64_t)cycle.label[(start+i)%cycle.count] << (4*(i+1));
    return key;
}

/* Maximize the minimum EXACT interval fan output across cyclic anchors.
   Cached triangle bounds are shared across candidates in this box. */
static int64_t ranked_fan_margin(Context *ctx, Cycle *cycle) {
    if (cycle->count <= 5) return INT64_MAX;
    int n = cycle->count, start = 0;
    int64_t best = INT64_MIN;
    for (int r = 0; r < n; ++r) {
        int a = cycle->label[r], b = cycle->label[(r+1)%n];
        int64_t margin = INT64_MAX;
        for (int j = 2; j < n && margin > best; ++j) {
            int64_t m = fan_bound(ctx, a, b, cycle->label[(r+j)%n]);
            if (m < margin) margin = m;
        }
        for (int j = 2; j+1 < n && margin > best; ++j) {
            int64_t m = fan_bound(ctx, a, cycle->label[(r+j)%n],
                                 cycle->label[(r+j+1)%n]);
            if (m < margin) margin = m;
        }
        if (margin > best) { best = margin; start = r; }
    }
    Cycle original = *cycle;
    for (int i = 0; i < n; ++i) cycle->label[i] = original.label[(start+i)%n];
    return best;
}

static void rank_proposal(Context *ctx, RankedCandidate all[8192], uint64_t seen[16384],
                          int *count, Cycle cycle) {
    double area = cycle_area(ctx, cycle);
    if (!midpoint_fan(ctx, &cycle)) return;
    uint64_t key = cycle_key(cycle);
    unsigned slot = (unsigned)((key * UINT64_C(11400714819323198485)) >> 50);
    while (seen[slot]) {
        if (seen[slot] == key) return;
        slot = (slot+1) & 16383;
    }
    if (*count >= 8192) fail("candidate menu overflow");
    seen[slot] = key;
    Polynomial p = {0};
    cached_area_polynomial(ctx, &p, cycle);
    int64_t bound = lower_bound(&p);
    int64_t margin = ranked_fan_margin(ctx, &cycle);
    int64_t threshold = (int64_t)(((Wide)239*ONE+999)/1000);
    int64_t score = narrow((Wide)bound-threshold);
    if (cycle.count > 5 && floor_div(margin, 2) < score)
        score = floor_div(margin, 2);
    all[(*count)++] = (RankedCandidate){cycle, area, bound, margin, score, 0};
}

static int rank_compare(const void *pa, const void *pb) {
    const RankedCandidate *a = pa, *b = pb;
    if (a->score != b->score) return a->score > b->score ? -1 : 1;
    if (a->cycle.count != b->cycle.count)
        return a->cycle.count < b->cycle.count ? -1 : 1;
    if (a->bound != b->bound) return a->bound > b->bound ? -1 : 1;
    for (int i = 0; i < a->cycle.count; ++i)
        if (a->cycle.label[i] != b->cycle.label[i])
            return a->cycle.label[i] < b->cycle.label[i] ? -1 : 1;
    return 0;
}

static void rank_select(RankedCandidate *a, Candidate list[MEMBERS], int *count) {
    if (a->selected || *count == MEMBERS) return;
    list[(*count)++] = (Candidate){a->cycle, a->area};
    a->selected = 1;
}

static void candidates(Context *ctx, Cycle hull, Candidate list[MEMBERS],
                                int *count, Candidate short_list[MEMBERS],
                                int *short_count) {
    RankedCandidate all[8192];
    uint64_t seen[16384] = {0};
    int n = 0;
    for (unsigned mask = 1; mask < (1u << hull.count); ++mask) {
        int size = __builtin_popcount(mask);
        if (size < 3 || (size < hull.count-2 && size != 4 && size != 5 && size != 6))
            continue;
        Cycle cycle = {.count = 0};
        for (int i = 0; i < hull.count; ++i)
            if (mask & (1u << i)) cycle.label[cycle.count++] = hull.label[i];
        rank_proposal(ctx, all, seen, &n, cycle);
        if (size <= 4) keep_candidate(ctx, short_list, short_count, cycle);
    }
    unsigned used = 0;
    for (int i = 0; i < hull.count; ++i) used |= 1u << hull.label[i];
    for (int label = 0; label < 13; ++label) {
        if (used & (1u << label)) continue;
        for (int i = 0; i < hull.count; ++i) {
            Cycle replacement = hull;
            replacement.label[i] = (uint8_t)label;
            rank_proposal(ctx, all, seen, &n, replacement);
            if (hull.count < 13) {
                Cycle insertion = hull;
                for (int j = hull.count; j > i+1; --j)
                    insertion.label[j] = insertion.label[j-1];
                insertion.label[i+1] = (uint8_t)label;
                ++insertion.count;
                rank_proposal(ctx, all, seen, &n, insertion);
            }
        }
    }
    qsort(all, (size_t)n, sizeof(all[0]), rank_compare);
    *count = 0;
    /* Keep strong interval bounds, both small sizes, nominal-area mixing
       alternatives, and robust anchors. The final checker still decides. */
    for (int i = 0; i < n && *count < 12; ++i)
        rank_select(&all[i], list, count);
    for (int size = 5; size <= 6; ++size) {
        int added = 0;
        for (int i = 0; i < n && added < 2; ++i)
            if (!all[i].selected && all[i].cycle.count == size) {
                rank_select(&all[i], list, count); ++added;
            }
    }
    for (int k = 0; k < 4; ++k) {
        int best = -1;
        for (int i = 0; i < n; ++i)
            if (!all[i].selected &&
                (best < 0 || all[i].area > all[best].area)) best = i;
        if (best >= 0) rank_select(&all[best], list, count);
    }
    for (int k = 0; k < 2; ++k) {
        int best = -1;
        for (int i = 0; i < n; ++i)
            if (!all[i].selected && all[i].cycle.count > 5 &&
                (Wide)all[i].bound >= (Wide)all[0].bound - ONE/50 &&
                (best < 0 || all[i].margin > all[best].margin)) best = i;
        if (best >= 0) rank_select(&all[best], list, count);
    }

    for (int i = 0; i < n && *count < MEMBERS; ++i)
        rank_select(&all[i], list, count);
}


static int widest_axis(const Interval box[9]) {
    int best = 0;
    Wide score = -1;
    for (int i = 0; i < 9; ++i) {
        Wide value = ((Wide)box[i].hi-box[i].lo)*(i < 3 ? 45 : 100);
        if (value > score) { score = value; best = i; }
    }
    return best;
}

static int variable_axis(int i) { return i % 4 < 2 ? 3+2*(i/4)+i%4 : i/4; }

static int sensitive_axis(const Interval box[9], const Polynomial *p) {
    Wide scores[9] = {0};
    for (int i = 0; i < 12; ++i) for (int j = i+1; j < 13; ++j) {
        int64_t size = magnitude(p->coefficient[coefficient_index(i, j)]);
        scores[variable_axis(i)] += size;
        if (j < 12) scores[variable_axis(j)] += size;
    }
    int best = widest_axis(box);
    Wide largest = ((Wide)box[best].hi-box[best].lo)*(best < 3 ? 45 : 100);
    Wide score = 0;
    for (int i = 0; i < 9; ++i) {
        /* Do not chase a threshold surface in already tiny coordinates while
           other dimensions remain broad. The widest axis is the fallback. */
        Wide width = ((Wide)box[i].hi-box[i].lo)*(i < 3 ? 45 : 100);
        if (width*8 < largest) continue;
        if ((Wide)box[i].hi-box[i].lo > 1 && scores[i] > score) {
            score = scores[i]; best = i;
        }
    }
    return best;
}

/* Choose the best interval fan rotation, then split for its failing triangle.
   The area inequality has already passed; refining it again may do no good. */
static int failing_fan_axis(Context *ctx, const Interval box[9], Cycle cycle) {
    int selected[3] = {0, 0, 0};
    int64_t best = INT64_MIN;
    int n = cycle.count;
    for (int r = 0; r < n; ++r) {
        int a = cycle.label[r], b = cycle.label[(r+1)%n], worst[3] = {a, b, b};
        int64_t margin = INT64_MAX;
        for (int j = 2; j < n; ++j) {
            int c = cycle.label[(r+j)%n];
            int64_t bound = fan_bound(ctx, a, b, c);
            if (bound < margin) {
                margin = bound; worst[0] = a; worst[1] = b; worst[2] = c;
            }
        }
        for (int j = 2; j+1 < n; ++j) {
            int c = cycle.label[(r+j)%n], d = cycle.label[(r+j+1)%n];
            int64_t bound = fan_bound(ctx, a, c, d);
            if (bound < margin) {
                margin = bound; worst[0] = a; worst[1] = c; worst[2] = d;
            }
        }
        if (margin > best) { best = margin; memcpy(selected, worst, sizeof(selected)); }
    }
    Polynomial p = {0};
    cached_edge(ctx, &p, selected[0], selected[1], 0);
    cached_edge(ctx, &p, selected[1], selected[2], 0);
    cached_edge(ctx, &p, selected[2], selected[0], 0);
    return sensitive_axis(box, &p);
}

static int try_cycle(Context *ctx, const Interval box[9], Cycle cycle,
                     Leaf *leaf, int *axis, int depth, int64_t *best) {
    /* Candidate selection only: every accepted cycle still has an exact bound. */
    if (cycle_area(ctx, cycle) < .239-1e-12) return 0;
    Polynomial p = {0};
    cached_area_polynomial(ctx, &p, cycle);
    int64_t bound = lower_bound(&p);
    int improved = bound > *best && cycle_area(ctx, cycle) >= .239;
    if (improved) {
        *best = bound;
        leaf->count = 1; leaf->cycle[0] = cycle; leaf->weight[0] = ONE;
        if (depth % 8 != 7) *axis = sensitive_axis(box, &p);
    }
    if ((Wide)1000*bound >= (Wide)239*ONE) {
        if (fan_valid(ctx, &cycle)) {
            leaf->count = 1; leaf->cycle[0] = cycle; leaf->weight[0] = ONE;
            return 1;
        }
        if (improved && depth % 8 != 7) *axis = failing_fan_axis(ctx, box, cycle);
    }
    return 0;
}

typedef struct {
    int count;
    Cycle cycle[MEMBERS];
    Polynomial polynomial[MEMBERS];
} MixturePool;

static void add_member(Context *ctx, MixturePool *pool, Cycle cycle) {
    if (pool->count == MEMBERS) return;
    for (int i = 0; i < pool->count; ++i)
        if (same_cycle(cycle, pool->cycle[i])) return;
#if !defined(MOSER_CHORD_LP_PROPOSALS) || !MOSER_CHORD_LP_PROPOSALS
    if (!fan_valid(ctx, &cycle)) return;
#endif
    int i = pool->count++;
    pool->cycle[i] = cycle;
    memset(&pool->polynomial[i], 0, sizeof(Polynomial));
    cached_area_polynomial(ctx, &pool->polynomial[i], cycle);
}

static void dyadic_weights(const MixturePool *pool, const double weight[MEMBERS], Leaf *leaf) {
    const uint64_t units = UINT64_C(1) << 48;
    uint64_t part[MEMBERS] = {0}, remaining = units;
    int largest = 0;
    for (int i = 0; i < pool->count; ++i) {
        if (weight[i] > weight[largest]) largest = i;
        double w = fmin(1, fmax(0, weight[i]));
        part[i] = (uint64_t)floor(w * (double)units);
        if (part[i] > remaining) part[i] = remaining;
        remaining -= part[i];
    }
    part[largest] += remaining;
    leaf->count = 0;
    for (int i = 0; i < pool->count; ++i) {
        if (!part[i]) continue;
        int k = leaf->count++;
        leaf->cycle[k] = pool->cycle[i];
        leaf->weight[k] = (int64_t)(part[i] << 8);
    }
}

/* Rebuild with weights applied BEFORE centering, exactly as in Lean.
   Multiplying the stored unweighted coefficient intervals is not this check. */
static int weighted_polynomial(Context *ctx, Leaf *leaf, Polynomial *p) {
    if (leaf->count < 1 || leaf->count > MEMBERS) return 0;
    Wide total = 0;
    memset(p, 0, sizeof(*p));
    for (int k = 0; k < leaf->count; ++k) {
        Cycle *cycle = &leaf->cycle[k];
        if (leaf->weight[k] <= 0 || leaf->weight[k] > ONE) return 0;
        total += leaf->weight[k];
        if (total > ONE || cycle->count < 3 || cycle->count > 13) return 0;
        unsigned labels = 0;
        for (int i = 0; i < cycle->count; ++i) {
            unsigned label = cycle->label[i];
            if (label >= 13 || (labels & (1u << label))) return 0;
            labels |= 1u << label;
        }
#if !defined(MOSER_CHORD_LP_PROPOSALS) || !MOSER_CHORD_LP_PROPOSALS
        if (!fan_valid(ctx, cycle)) return 0;
#endif
        area_polynomial(ctx, p, *cycle, leaf->weight[k]);
    }
    return 1;
}

/* On larger accepted mixtures, try shorter prefixes by descending weight.
   Renormalization is integral, and every shortened result is checked again. */
static void compact_mixture(Context *ctx, Leaf *leaf) {
    if (leaf->count <= 4) return;
    Leaf sorted = *leaf;
    for (int i = 1; i < sorted.count; ++i) {
        int j = i;
        Cycle cycle = sorted.cycle[i];
        int64_t weight = sorted.weight[i];
        while (j > 0 && weight > sorted.weight[j-1]) {
            sorted.cycle[j] = sorted.cycle[j-1];
            sorted.weight[j] = sorted.weight[j-1];
            --j;
        }
        sorted.cycle[j] = cycle;
        sorted.weight[j] = weight;
    }
    for (int n = 2; n < sorted.count; ++n) {
        Leaf candidate = {.count = 0};
        int64_t total = 0;
        for (int k = 0; k < n; ++k) total += sorted.weight[k];
        uint64_t remaining = UINT64_C(1) << 48;
        for (int k = 0; k < n; ++k) {
            uint64_t units = (uint64_t)((Wide)sorted.weight[k]*(UINT64_C(1) << 48)/total);
            remaining -= units;
            if (!units) continue;
            int j = candidate.count++;
            candidate.cycle[j] = sorted.cycle[k];
            candidate.weight[j] = (int64_t)(units << 8);
        }
        candidate.weight[0] += (int64_t)(remaining << 8);
        Polynomial p;
        if (weighted_polynomial(ctx, &candidate, &p) &&
            (Wide)1000*lower_bound(&p) >= (Wide)239*ONE) {
            *leaf = candidate;
            return;
        }
    }
}

static int consider_mixture(Context *ctx, const Interval box[9], Leaf *candidate,
                            Leaf *leaf, int *axis, int depth, int64_t *best) {
    Polynomial p;
    if (!weighted_polynomial(ctx, candidate, &p)) return 0;
    int64_t bound = lower_bound(&p);
    if ((Wide)1000*bound >= (Wide)239*ONE) {
        compact_mixture(ctx, candidate);
        *leaf = *candidate;
        return 1;
    }
    double nominal = 0;
    for (int k = 0; k < candidate->count; ++k)
        nominal += ((double)candidate->weight[k] / ONE) * cycle_area(ctx, candidate->cycle[k]);
    if (bound > *best && nominal >= .239) {
        *best = bound;
        *leaf = *candidate;
        if (depth % 8 != 7) *axis = sensitive_axis(box, &p);
    }
    return 0;
}

static int optimize_pool(Context *ctx, const Interval box[9], const MixturePool *pool,
                         Leaf *leaf, int *axis, int depth, int64_t *best) {
    if (pool->count < 2) return 0;
    for (int pass = 0; pass < 2; ++pass) {
        int full = MOSER_LP_FULL_FIRST ? 1 - pass : pass;
        double intercept[MEMBERS], gradient[MEMBERS][MIX_AXES], weight[MEMBERS];
        double scale[CONSTANT], penalty[MIX_AXES];
        int active[CONSTANT], axes = 0;
        /* All other coefficient slots are identically zero. */
        for (int row = 0; row < 12; ++row) for (int column = row; column < 13; ++column) {
            int j = row*13+column;
            scale[j] = 0;
            double low = INFINITY, high = -INFINITY;
            for (int k = 0; k < pool->count; ++k) {
                Interval a = pool->polynomial[k].coefficient[j];
                double center = ((double)a.lo + (double)a.hi) * (.5 / ONE);
                scale[j] = fmax(scale[j], fabs(center));
                low = fmin(low, center);
                high = fmax(high, center);
            }
            /* A coefficient with a common sign cannot benefit from mixing.
               Fold its absolute value into each member's intercept. */
            active[j] = low < -1e-12 && high > 1e-12 && (full || j%13 == 12);
            axes += active[j];
        }
        if (axes > MIX_AXES) return 0;
        for (int k = 0; k < pool->count; ++k) {
            const Polynomial *p = &pool->polynomial[k];
            intercept[k] = (double)p->coefficient[CONSTANT].lo / ONE;
            int d = 0;
            for (int row = 0; row < 12; ++row) for (int column = row; column < 13; ++column) {
                int j = row*13+column;
                Interval a = p->coefficient[j];
                if (active[j]) {
                    penalty[d] = scale[j];
                    gradient[k][d++] = ((double)a.lo + (double)a.hi) * (.5 / ONE) / scale[j];
                    intercept[k] -= ((double)a.hi - (double)a.lo) * (.5 / ONE);
                } else {
                    intercept[k] -= (double)magnitude(a) / ONE;
                }
            }
        }
        double possible = -INFINITY;
        for (int k = 0; k < pool->count; ++k) possible = fmax(possible, intercept[k]);
        if (possible < .239-1e-12) continue;
        unsigned pivots = 0;
        ++lp_calls;
        int solved = mix_simplex(pool->count, axes, intercept, gradient, penalty, weight, &pivots);
        lp_pivots += pivots;
        if (pivots == MIX_PIVOTS) ++lp_limits;
        if (!solved) {
            ++lp_failures;
            continue;
        }
        Leaf candidate;
        dyadic_weights(pool, weight, &candidate);
        if (consider_mixture(ctx, box, &candidate, leaf, axis, depth, best)) return 1;
    }
    return 0;
}

static int try_mixtures(Context *ctx, const Interval box[9],
                        Candidate hull[MEMBERS], int hull_count,
                        Candidate short_list[MEMBERS], int short_count,
                        Leaf *leaf, int *axis, int depth, int64_t *best) {
    MixturePool pool;
    pool.count = 0;
    int next = 0;
    /* Reserve room for unconditional chord/triangle bounds. */
    while (next < hull_count && pool.count < MEMBERS-4)
        add_member(ctx, &pool, hull[next++].cycle);
    for (int i = 0; i < short_count && pool.count < MEMBERS; ++i)
        add_member(ctx, &pool, short_list[i].cycle);
    while (next < hull_count && pool.count < MEMBERS)
        add_member(ctx, &pool, hull[next++].cycle);
    return optimize_pool(ctx, box, &pool, leaf, axis, depth, best);
}

typedef struct { Cycle cycle; double gradient[9], weight; } RadialCandidate;

/* Derivative of midpoint shoelace area in the nine placement coordinates.
   These floats choose candidates only; none enters the emitted certificate. */
static void area_gradient(Context *ctx, const Interval box[9], Cycle cycle, double g[9]) {
    memset(g, 0, 9*sizeof(double));
    for (int j = 0; j < cycle.count; ++j) {
        int i = cycle.label[j], body = ctx->point[i].body;
        if (body < 0) continue;
        int prev = cycle.label[(j+cycle.count-1)%cycle.count];
        int next = cycle.label[(j+1)%cycle.count];
        double gx = .5*(ctx->y[next]-ctx->y[prev]);
        double gy = .5*(ctx->x[prev]-ctx->x[next]);
        double rx = (double)midpoint(ctx->point[i].x)/ONE;
        double ry = (double)midpoint(ctx->point[i].y)/ONE;
        g[body] += -gx*ry+gy*rx;
        g[3+2*body] += gx;
        g[4+2*body] += gy;
    }
    for (int j = 0; j < 9; ++j) g[j] *= (double)radius(box[j])/ONE;
}

/* Pairwise transfers on the probability simplex reduce the squared gradient.
   This bounded heuristic supplies a small support to the interval LP. */
static void balance_gradients(RadialCandidate *list, int count) {
    double g[9], best = INFINITY;
    int initial = 0;
    for (int i = 0; i < count; ++i) {
        list[i].weight = 0;
        double norm = 0;
        for (int j = 0; j < 9; ++j) norm += list[i].gradient[j]*list[i].gradient[j];
        if (norm < best) { best = norm; initial = i; }
    }
    list[initial].weight = 1;
    memcpy(g, list[initial].gradient, sizeof(g));
    for (int iteration = 0; iteration < 4096; ++iteration) {
        double low = INFINITY, high = -INFINITY, norm = 0;
        int to = -1, away = -1;
        for (int j = 0; j < 9; ++j) norm += g[j]*g[j];
        if (norm < 1e-24) break;
        for (int i = 0; i < count; ++i) {
            double dot = 0;
            for (int j = 0; j < 9; ++j) dot += g[j]*list[i].gradient[j];
            if (dot < low) { low = dot; to = i; }
            if (list[i].weight > 1e-15 && dot > high) { high = dot; away = i; }
        }
        if (away < 0 || high-low < 1e-18) break;
        double delta[9], dd = 0, gd = 0;
        for (int j = 0; j < 9; ++j) {
            delta[j] = list[to].gradient[j]-list[away].gradient[j];
            dd += delta[j]*delta[j];
            gd += g[j]*delta[j];
        }
        if (dd < 1e-30) break;
        double step = fmin(list[away].weight, fmax(0, -gd/dd));
        list[to].weight += step;
        list[away].weight -= step;
        for (int j = 0; j < 9; ++j) g[j] += step*delta[j];
    }
}

static int radial_mixture(Context *ctx, const Interval box[9], Leaf *leaf,
                           int *axis, int depth, int64_t *best) {
    double hull_area = cycle_area(ctx, convex_hull(ctx));
    /* Wide boxes benefit more from splitting or the cheap chord menu. */
    if (hull_area > .25 || hull_area < .239) return 0;
    for (int j = 0; j < 9; ++j)
        if ((double)radius(box[j])/ONE > (j < 3 ? .08 : .04)) return 0;
    ++radial_calls;
    double cx = 0, cy = 0, angle[13];
    int order[13];
    for (int i = 0; i < 13; ++i) { cx += ctx->x[i]/13; cy += ctx->y[i]/13; }
    for (int i = 0; i < 13; ++i) {
        angle[i] = atan2(ctx->y[i]-cy, ctx->x[i]-cx);
        int j = i;
        while (j > 0 && angle[i] < angle[order[j-1]]) {
            order[j] = order[j-1]; --j;
        }
        order[j] = i;
    }
    RadialCandidate list[1 << 13];
    int count = 0;
    double cutoff = hull_area-fmin(.001, (hull_area-.239)/4);
    for (unsigned mask = 0; mask < (1u << 13); ++mask) {
        if (__builtin_popcount(mask) < 3) continue;
        Cycle cycle = {.count = 0};
        for (int i = 0; i < 13; ++i) if (mask & (1u << i))
            cycle.label[cycle.count++] = (uint8_t)order[i];
        double area = cycle_area(ctx, cycle);
        if (area < cutoff || !midpoint_fan(ctx, &cycle) || !fan_valid(ctx, &cycle)) continue;
        RadialCandidate *candidate = &list[count++];
        candidate->cycle = cycle;
        area_gradient(ctx, box, cycle, candidate->gradient);
    }
    radial_candidates += (uint64_t)count;
    if (count < 2) return 0;
    balance_gradients(list, count);
    MixturePool pool = {.count = 0};
    double weight[MEMBERS], total = 0;
    for (int k = 0; k < MEMBERS && k < count; ++k) {
        int largest = -1;
        for (int i = 0; i < count; ++i)
            if (list[i].weight > 1e-15 &&
                (largest < 0 || list[i].weight > list[largest].weight)) largest = i;
        if (largest < 0) break;
        weight[pool.count] = list[largest].weight;
        total += list[largest].weight;
        list[largest].weight = 0;
        add_member(ctx, &pool, list[largest].cycle);
    }
    if (!pool.count) return 0;
    for (int k = 0; k < pool.count; ++k) weight[k] /= total;
    Leaf candidate;
    dyadic_weights(&pool, weight, &candidate);
    /* A simplex solution usually has fewer members than the balanced proposal,
       which substantially reduces the subsequent Lean kernel computation. */
    int accepted = optimize_pool(ctx, box, &pool, leaf, axis, depth, best) ||
        consider_mixture(ctx, box, &candidate, leaf, axis, depth, best);
    if (accepted) ++radial_accepts;
    return accepted;
}

static int evaluate(const Interval box[9], Leaf *leaf, int *axis, int depth, const Leaf *hint) {
    Context ctx;
    leaf->count = 0;
    *axis = widest_axis(box);
    if (!prepare(&ctx, box)) {
        for (int i = 0; i < 3; ++i) if (radius(box[i]) > PI2) { *axis = i; break; }
        return 0;
    }
    int64_t best = INT64_MIN;
    if (hint && hint->count) {
        ++hint_checks;
        Leaf candidate = *hint;
        Polynomial p;
        if (weighted_polynomial(&ctx, &candidate, &p)) {
            int64_t bound = lower_bound(&p);
            if ((Wide)1000*bound >= (Wide)239*ONE) {
                compact_mixture(&ctx, &candidate);
                *leaf = candidate;
                ++hint_accepts;
                return 1;
            }
            double nominal = 0;
            for (int k = 0; k < candidate.count; ++k)
                nominal += ((double)candidate.weight[k] / ONE) * cycle_area(&ctx, candidate.cycle[k]);
            if (nominal >= .239) {
                best = bound;
                *leaf = candidate;
                if (depth % 8 != 7) *axis = sensitive_axis(box, &p);
            }
        }
    }
    Candidate short_list[MEMBERS];
    int short_count = 0;
    for (int i = 2; i < 13; ++i) {
        Cycle cycle = {.count = 3, .label = {0, 1, (uint8_t)i}};
        if (cycle_area(&ctx, cycle) < 0) { cycle.label[0] = 1; cycle.label[1] = 0; }
        if (try_cycle(&ctx, box, cycle, leaf, axis, depth, &best)) return 1;
        keep_candidate(&ctx, short_list, &short_count, cycle);
    }
    /* Chords of two bodies cancel both translations in the four-point formula. */
    for (int a = 0; a < 13; ++a) for (int b = a+1; b < 13; ++b) {
        if (ctx.point[a].body != ctx.point[b].body) continue;
        for (int c = 0; c < 13; ++c) for (int d = c+1; d < 13; ++d) {
            if (ctx.point[c].body != ctx.point[d].body ||
                ctx.point[a].body >= ctx.point[c].body) continue;
            Cycle cycle = {.count = 4, .label = {(uint8_t)a, (uint8_t)c, (uint8_t)b, (uint8_t)d}};
            if (cycle_area(&ctx, cycle) < 0) {
                cycle.label[1] = (uint8_t)d; cycle.label[3] = (uint8_t)c;
            }
            if (try_cycle(&ctx, box, cycle, leaf, axis, depth, &best)) return 1;
            keep_candidate(&ctx, short_list, &short_count, cycle);
        }
    }
    Candidate list[MEMBERS];
    int count;
    candidates(&ctx, convex_hull(&ctx), list, &count, short_list, &short_count);
    for (int i = 0; i < short_count; ++i) {
        if (try_cycle(&ctx, box, short_list[i].cycle, leaf, axis, depth, &best)) return 1;
    }
    for (int i = 0; i < count; ++i) {
        if (try_cycle(&ctx, box, list[i].cycle, leaf, axis, depth, &best)) return 1;
    }
    if (try_mixtures(&ctx, box, list, count, short_list, short_count,
                     leaf, axis, depth, &best)) return 1;
    if (radial_mixture(&ctx, box, leaf, axis, depth, &best)) return 1;
    return 0;
}

static void write_byte(unsigned byte) {
    if (fputc((int)byte, output) == EOF) fail("cannot write certificate");
}

static void write_leaf(const Leaf *leaf) {
    if (leaf->count < 1 || leaf->count > MEMBERS) fail("invalid mixture count");
    int single = leaf->count == 1 && leaf->weight[0] == ONE;
    if (!single) { write_byte(16); write_byte((unsigned)leaf->count); }
    Wide total = 0;
    for (int k = 0; k < leaf->count; ++k) {
        const Cycle *cycle = &leaf->cycle[k];
        if (leaf->weight[k] <= 0 || leaf->weight[k] > ONE ||
            cycle->count < 3 || cycle->count > 13) fail("invalid mixture member");
        total += leaf->weight[k];
        if (total > ONE) fail("invalid mixture weight sum");
        if (!single) {
            uint64_t weight = (uint64_t)leaf->weight[k];
            for (int byte = 0; byte < 8; ++byte) write_byte((unsigned)((weight >> (8*byte)) & 255));
        }
        write_byte((unsigned)cycle->count + (single ? 16u : 0u));
        if (fwrite(cycle->label, 1, (size_t)cycle->count, output) != (size_t)cycle->count)
            fail("cannot write certificate");
    }
}

/* Private continuation files are never ordinary certificates. */
static uint64_t read_unsigned(FILE *input, int bytes) {
    uint64_t value = 0;
    for (int i = 0; i < bytes; ++i) {
        int byte = fgetc(input);
        if (byte == EOF) fail("truncated continuation state");
        value |= (uint64_t)(unsigned)byte << (8*i);
    }
    return value;
}

static void write_unsigned(uint64_t value, int bytes) {
    for (int i = 0; i < bytes; ++i) write_byte((unsigned)((value >> (8*i)) & 255));
}

static int64_t read_signed(FILE *input) {
    uint64_t value = read_unsigned(input, 8);
    return value <= INT64_MAX ? (int64_t)value : -(int64_t)(~value)-1;
}

static void read_state(FILE *input, Interval box[9], int *depth, Leaf *hint) {
    *depth = (int)read_unsigned(input, 2);
    if (*depth > 256) fail("invalid continuation depth");
    for (int i = 0; i < 9; ++i) {
        box[i].lo = read_signed(input);
        box[i].hi = read_signed(input);
        if (box[i].lo > box[i].hi) fail("invalid continuation interval");
    }
    hint->count = (int)read_unsigned(input, 1);
    if (hint->count > MEMBERS) fail("invalid continuation mixture");
    Wide total = 0;
    for (int k = 0; k < hint->count; ++k) {
        uint64_t weight = read_unsigned(input, 8);
        if (!weight || weight > (uint64_t)ONE) fail("invalid continuation weight");
        hint->weight[k] = (int64_t)weight;
        total += weight;
        if (total > ONE) fail("invalid continuation total weight");
        Cycle *cycle = &hint->cycle[k];
        cycle->count = (int)read_unsigned(input, 1);
        if (cycle->count < 3 || cycle->count > 13) fail("invalid continuation polygon");
        unsigned labels = 0;
        for (int j = 0; j < cycle->count; ++j) {
            unsigned label = (unsigned)read_unsigned(input, 1);
            if (label >= 13 || (labels & (1u << label))) fail("invalid continuation labels");
            labels |= 1u << label;
            cycle->label[j] = (uint8_t)label;
        }
    }
}

static void write_state(const Interval box[9], int depth, const Leaf *hint) {
    write_unsigned((uint64_t)depth, 2);
    for (int i = 0; i < 9; ++i) {
        write_unsigned((uint64_t)box[i].lo, 8);
        write_unsigned((uint64_t)box[i].hi, 8);
    }
    int count = hint ? hint->count : 0;
    write_unsigned((uint64_t)count, 1);
    for (int k = 0; k < count; ++k) {
        write_unsigned((uint64_t)hint->weight[k], 8);
        write_unsigned((uint64_t)hint->cycle[k].count, 1);
        for (int j = 0; j < hint->cycle[k].count; ++j)
            write_byte(hint->cycle[k].label[j]);
    }
}

static void progress(int complete) {
    if (fflush(output)) fail("cannot flush certificate");
    fprintf(stderr,
        "{\"complete\":%s,\"nodes\":%" PRIu64 ",\"leaves\":%" PRIu64
        ",\"mixtures\":%" PRIu64 ",\"lp_calls\":%" PRIu64
        ",\"lp_failures\":%" PRIu64 ",\"lp_pivots\":%" PRIu64
        ",\"lp_limits\":%" PRIu64
        ",\"hint_checks\":%" PRIu64 ",\"hint_accepts\":%" PRIu64
        ",\"radial_calls\":%" PRIu64 ",\"radial_candidates\":%" PRIu64
        ",\"radial_accepts\":%" PRIu64
        ",\"depth\":%d,\"cpu_seconds\":%.3f,\"reason\":\"%s\""
        ",\"chunk\":true,\"holes\":%" PRIu64 "}\n",
        complete ? "true" : "false",
        nodes, leaves, mixtures, lp_calls, lp_failures, lp_pivots, lp_limits,
        hint_checks, hint_accepts, radial_calls, radial_candidates, radial_accepts, reached_depth,
        (double)(clock()-started)/CLOCKS_PER_SEC, stop_reason, holes);
    if (fflush(stderr)) fail("cannot flush progress");
}

static int search(Interval box[9], int depth, const Leaf *hint) {
    if (nodes >= node_limit) {
        write_byte(255);
        write_state(box, depth, hint);
        ++holes;
        return 1;
    }
    ++nodes;
    if (depth > reached_depth) reached_depth = depth;
    Leaf leaf;
    int axis;
    if (evaluate(box, &leaf, &axis, depth, hint)) {
        ++leaves;
        if (leaf.count > 1) ++mixtures;
        write_leaf(&leaf);
        return 1;
    }
    if (depth >= depth_limit) { stop_reason = "depth_limit"; return 0; }
    Interval original = box[axis];
    int64_t mid = midpoint(original);
    if (mid <= original.lo || mid >= original.hi) { stop_reason = "unsplittable"; return 0; }
    write_byte((unsigned)axis);
    const Leaf *next_hint = leaf.count ? &leaf : hint;
    box[axis].hi = mid;
    if (!search(box, depth+1, next_hint)) { box[axis] = original; return 0; }
    box[axis] = (Interval){mid, original.hi};
    if (!search(box, depth+1, next_hint)) { box[axis] = original; return 0; }
    box[axis] = original;
    return 1;
}

int main(int argc, char **argv) {
    if (argc != 6 || strcmp(argv[1], "--chunk")) {
        fprintf(stderr, "usage: search --chunk TASK OUTPUT NODE_LIMIT MAX_DEPTH\n");
        return 2;
    }
    FILE *input = fopen(argv[2], "rb");
    if (!input) fail("cannot open task file");
    Interval box[9];
    int initial_depth = 0;
    Leaf initial_hint = {.count = 0};
    char magic[8];
    if (fread(magic, 1, 8, input) != 8 || memcmp(magic, "MWTASK01", 8))
        fail("invalid continuation magic");
    read_state(input, box, &initial_depth, &initial_hint);
    if (fgetc(input) != EOF || ferror(input)) fail("trailing continuation data");
    if (fclose(input)) fail("cannot close task file");
    char *end;
    errno = 0; node_limit = strtoull(argv[4], &end, 10);
    if (errno || *end || end == argv[4] || argv[4][0] == '-' || !node_limit)
        fail("invalid node limit");
    errno = 0; long limit = strtol(argv[5], &end, 10);
    if (errno || *end || end == argv[5] || limit < 1 || limit > 256 ||
        initial_depth > limit) fail("invalid depth limit");
    depth_limit = (int)limit;
    output = fopen(argv[3], "wb");
    if (!output) fail("cannot open output file");
    static char buffer[1 << 20];
    if (setvbuf(output, buffer, _IOFBF, sizeof(buffer))) fail("cannot buffer output");
    if (fwrite("MWCHNK01", 1, 8, output) != 8) fail("cannot write continuation magic");
    write_state(box, initial_depth, &initial_hint);
    started = clock();
    int complete = search(box, initial_depth, initial_hint.count ? &initial_hint : NULL);
    if (complete && holes) stop_reason = "yield";
    progress(complete && !holes);
    if (fclose(output)) fail("cannot close output file");
    return complete ? 0 : 1;
}
