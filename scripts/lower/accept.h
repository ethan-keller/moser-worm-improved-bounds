#ifndef MOSER_LOWER_ACCEPT_H
#define MOSER_LOWER_ACCEPT_H

#include <stdint.h>
#include "api.h"

#ifndef MOSER_ACCEPT_API
#define MOSER_ACCEPT_API MOSER_LOWER_API
#endif

/* Internal adapters include this implementation with renamed, hidden symbols. */
MOSER_ACCEPT_API int lower_accept_prepare(const int64_t raw[18]);
MOSER_ACCEPT_API int lower_accept_try(int count, const int64_t *raw, int64_t accepted[361]);
MOSER_ACCEPT_API int lower_accept_mix(int count, const int64_t *raw, int64_t accepted[361]);
MOSER_ACCEPT_API void lower_mix_reset(void);
MOSER_ACCEPT_API void lower_mix_stats(uint64_t out[5]);

#endif
