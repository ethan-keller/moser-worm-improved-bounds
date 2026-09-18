#ifndef MOSER_LOWER_CHORD_LP_H
#define MOSER_LOWER_CHORD_LP_H

#include <stddef.h>
#include <stdint.h>
#include "api.h"

/* Proposal-only ABI. Geometry must be certified on the whole prepared box by
   the caller, and returned weights/labels/area checked before serialization. */
MOSER_LOWER_API int lower_chord_lp_mode(void);
MOSER_LOWER_API int lower_chord_lp_full_first(void);
MOSER_LOWER_API int lower_chord_lp_prepare(const int64_t box[18]);
MOSER_LOWER_API int lower_chord_lp_propose(int count, const int64_t *cycles, size_t words,
                          int64_t *accepted, size_t capacity);
MOSER_LOWER_API void lower_chord_lp_reset(void);
MOSER_LOWER_API void lower_chord_lp_stats(uint64_t out[5]);

#endif
