/* inject_only.c — companion driver, profile inject in isolation.
 *
 * Build with the same flags as eject_only.c:
 *   gcc -O3 -g -fno-omit-frame-pointer -funroll-loops -finline-functions \
 *       -Wall -Wextra -std=c11 -D_POSIX_C_SOURCE=199309L -DNDEBUG \
 *       -o inject_only ktdeque_dequeptr.c inject_only.c
 */

#include "ktdeque.h"
#include <stdio.h>
#include <stdlib.h>

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

    kt_deque d = kt_empty();
    for (long i = 0; i < n; i++) {
        storage[i] = i;
        d = kt_inject(d, (kt_elem)&storage[i]);
        maybe_compact(&d, i);
    }
    fprintf(stderr, "injected %ld elements\n", n);
    return 0;
}
