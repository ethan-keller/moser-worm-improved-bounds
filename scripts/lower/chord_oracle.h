#ifndef MOSER_CHORD_ORACLE_H
#define MOSER_CHORD_ORACLE_H
#include <stddef.h>
#include <stdint.h>
#include "api.h"

#define LOWER_CHORD_ONE INT64_C(72057594037927936)
#define LOWER_CHORD_INVALID INT64_MIN
#define LOWER_CHORD_MAX_MEMBERS 24
#define LOWER_CHORD_PACKED_CAPACITY 360

/* One global, process-local context. Not thread-safe.
   raw is exactly nine (lo,hi) pairs, scale 2^-56, in paper coordinate order.
   Angles have midpoint within +/-64 and radius at most
   113187804032455044 * 2^-56; translation intervals lie within [-1,1].
   A failed prepare clears readiness. */
MOSER_LOWER_API int lower_accept_prepare(const int64_t raw[18]);

/* Signed original weighted shoelace lower bound, ignoring fan validity.
   Exactly words readable elements; rejects trailing or truncated packing.
   Returns INT64_MIN on invalid input.
   Packing is weight,n,label_0,...,label_(n-1), repeated count times. */
MOSER_LOWER_API int64_t lower_chord_area_sized(int count, const int64_t *raw, size_t words);

/* max(direct, centered) lower bound for cross(b-a,c-a), not absolute value.
   Invalid labels or unprepared state return INT64_MIN. */
MOSER_LOWER_API int64_t lower_chord_fan(int a, int b, int c);

/* 1 only if a coordinate interval of the actual b-a excludes zero.
   0 includes invalid, unprepared, or inconclusive queries. */
MOSER_LOWER_API int lower_chord_nonzero(int a, int b);
#endif
