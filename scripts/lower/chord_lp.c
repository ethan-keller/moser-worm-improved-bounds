/* Separate proposal library. Ordinary search.c/accept.c builds keep both
   fan filters. No text rewriting or alternative area arithmetic is used. */
#include "chord_lp.h"

#define MOSER_CHORD_LP_PROPOSALS 1
#define MOSER_ACCEPT_API
#define lower_accept_prepare lower_chord_lp_prepare
#define lower_accept_try chord_lp_area_unchecked
#define lower_accept_mix chord_lp_mix_unchecked
#define lower_mix_reset lower_chord_lp_reset
#define lower_mix_stats lower_chord_lp_stats
#include "accept.c"
#undef lower_accept_prepare
#undef lower_accept_try
#undef lower_accept_mix
#undef lower_mix_reset
#undef lower_mix_stats
#undef MOSER_ACCEPT_API

int lower_chord_lp_mode(void) {
    return MOSER_CHORD_LP_PROPOSALS;
}

int lower_chord_lp_full_first(void) {
    return MOSER_LP_FULL_FIRST ? 1 : 0;
}

int lower_chord_lp_propose(int count, const int64_t *cycles, size_t words,
                          int64_t *accepted, size_t capacity) {
    if (count < 2 || count > MEMBERS || !cycles || !accepted ||
        capacity < 361 || words > (size_t)MEMBERS * 14) return 0;
    size_t at = 0;
    for (int k = 0; k < count; ++k) {
        if (at >= words) return 0;
        int64_t n = cycles[at++];
        if (n < 3 || n > 13 || (size_t)n > words - at) return 0;
        unsigned used = 0;
        for (int j = 0; j < n; ++j) {
            int64_t label = cycles[at++];
            if (label < 0 || label >= 13 || (used & (1u << label))) return 0;
            used |= 1u << label;
        }
    }
    if (at != words) return 0;
    return chord_lp_mix_unchecked(count, cycles, accepted);
}
