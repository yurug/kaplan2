/* eject_only.c — focused driver for profiling kt_eject in isolation.
 *
 * Build:   gcc -O3 -g -fno-omit-frame-pointer -funroll-loops \
 *               -finline-functions -Wall -Wextra -std=c11 \
 *               -D_POSIX_C_SOURCE=199309L -DNDEBUG \
 *               -o eject_only ktdeque_dequeptr.c eject_only.c
 *
 * Phase 1: build a deque of N elements via inject (back-pushes), so
 *          eject in phase 2 walks through every refill case.
 * Phase 2: eject all N elements (the part to profile).
 *
 * Use perf to profile only phase 2 by adding a marker if needed; or
 * just record the whole run — phase 1 is amortized fast (most ops are
 * in the simple-rebuild path) and contributes a known fraction.
 */

#include "ktdeque.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define N 1000000

#ifndef KT_COMPACT_INTERVAL
#define KT_COMPACT_INTERVAL 0
#endif

static long storage[N];

static inline void maybe_compact(kt_deque* d, long i) {
#if KT_COMPACT_INTERVAL > 0
    if ((i % KT_COMPACT_INTERVAL) == (KT_COMPACT_INTERVAL - 1)) {
        kt_arena_compact(d, 1);
    }
#else
    (void)d; (void)i;
#endif
}

int main(int argc, char** argv) {
    long n = N;
    if (argc > 1) n = atol(argv[1]);
    if (n <= 0 || n > N) n = N;

    /* Phase 1: build deque via inject. */
    kt_deque d = kt_empty();
    for (long i = 0; i < n; i++) {
        storage[i] = i;
        d = kt_inject(d, (kt_elem)&storage[i]);
        maybe_compact(&d, i);
    }
    fprintf(stderr, "built deque with %ld elements\n", n);

    /* Phase 2: eject all (the part we care about). */
    long sum = 0;  /* prevents the compiler from removing the eject. */
    for (long i = 0; i < n; i++) {
        kt_elem out = NULL;
        int nz = 0;
        d = kt_eject(d, &out, &nz);
        if (out) sum += *(long*)out;
        maybe_compact(&d, i);
    }
    fprintf(stderr, "ejected %ld elements, sum=%ld\n", n, sum);
    return 0;
}
