/* bench_perf.c — minimal bench for perf profiling.
 *
 * Single push phase at n=1M, with arena compaction every 4096 ops.
 * Runs warmup before timing so first-touch page faults don't dominate.
 *
 * Build:
 *   gcc -O3 -funroll-loops -finline-functions -fomit-frame-pointer \
 *       -DNDEBUG -DKT_COMPACT_INTERVAL=4096 \
 *       -fno-omit-frame-pointer -ggdb -g3 \
 *       -o c/bench_perf c/ktdeque_dequeptr.c c/bench_perf.c
 *
 * Profile:
 *   perf record -F 999 --call-graph dwarf -- ./c/bench_perf
 *   perf report --stdio --sort=overhead,symbol | head -40
 *   perf annotate green_of_red --stdio | head -80
 *   perf stat -e cycles,instructions,branch-misses,cache-misses ./c/bench_perf
 */
#include "ktdeque.h"
#include <stdio.h>
#include <stdlib.h>

extern int kt_check_diff_invariant(kt_deque);

#ifndef KT_COMPACT_INTERVAL
#define KT_COMPACT_INTERVAL 4096
#endif

extern size_t kt_arena_compact(kt_deque*, size_t);

static inline void maybe_compact(kt_deque* d, int i) {
#if KT_COMPACT_INTERVAL > 0
    if ((i % KT_COMPACT_INTERVAL) == (KT_COMPACT_INTERVAL - 1)) {
        kt_arena_compact(d, 1);
    }
#else
    (void)d; (void)i;
#endif
}

int main(void) {
    const int N = 1000000;
    int* values = (int*)malloc(sizeof(int) * N);
    for (int i = 0; i < N; i++) values[i] = i;

    /* Warmup: page-in the arena. */
    {
        kt_deque d = kt_empty();
        for (int i = 0; i < 4096 * 16; i++) {
            d = kt_push(kt_base(&values[i % N]), d);
            maybe_compact(&d, i);
        }
    }

    /* Steady-state push at n=1M (the focus of the profile). */
    {
        kt_deque d = kt_empty();
        for (int i = 0; i < N; i++) {
            d = kt_push(kt_base(&values[i]), d);
            maybe_compact(&d, i);
        }
    }

    free(values);
    return 0;
}
