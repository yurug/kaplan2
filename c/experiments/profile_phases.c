/* profile_phases.c — split the bench into phases and report alloc count
 * per phase for the alloc breakdown. */

#include "ktdeque.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/resource.h>

extern size_t kt_alloc_packets(void);
extern size_t kt_alloc_pairs(void);
extern void   kt_reset_alloc_counters(void);
#ifdef KT_DIFF_TRACE
extern size_t kt_diff_count(void);
extern size_t kt_full_count(void);
#endif

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static long *storage;

int main(int argc, char** argv) {
    long n = (argc > 1) ? atol(argv[1]) : 1000000;
    storage = malloc(sizeof(long) * (size_t)n);
    for (long i = 0; i < n; i++) storage[i] = i;

    /* Phase 0: per-op breakdown */
    kt_reset_alloc_counters();
    kt_deque d = kt_empty();
    double t0 = now_sec();
    for (long i = 0; i < n; i++) d = kt_inject(d, (kt_elem)&storage[i]);
    double t1 = now_sec();
    size_t pkt_after_inject = kt_alloc_packets();
    size_t pair_after_inject = kt_alloc_pairs();
#ifdef KT_DIFF_TRACE
    size_t diff_after_inject = kt_diff_count();
    size_t full_after_inject = kt_full_count();
#endif
    printf("=== INJECT phase n=%ld ===\n", n);
    printf("  time: %.3f ms (%.1f ns/op)\n", (t1-t0)*1000.0, (t1-t0)*1e9/(double)n);
    printf("  alloc_links=%zu (%.2f/op)\n", pkt_after_inject, (double)pkt_after_inject/(double)n);
    printf("  alloc_pairs=%zu (%.2f/op)\n", pair_after_inject, (double)pair_after_inject/(double)n);
#ifdef KT_DIFF_TRACE
    printf("  full=%zu  diff=%zu  diff/total=%.3f\n",
           full_after_inject, diff_after_inject,
           (double)diff_after_inject / ((double)diff_after_inject + (double)full_after_inject));
#endif

    /* Phase 2: drain via eject */
    long sum = 0;
    double t2 = now_sec();
    for (long i = 0; i < n; i++) {
        kt_elem e = NULL; int ne;
        d = kt_eject(d, &e, &ne);
        if (e) sum += *(long*)e;
    }
    double t3 = now_sec();
    size_t pkt_eject = kt_alloc_packets() - pkt_after_inject;
    size_t pair_eject = kt_alloc_pairs() - pair_after_inject;
#ifdef KT_DIFF_TRACE
    size_t diff_eject = kt_diff_count() - diff_after_inject;
    size_t full_eject = kt_full_count() - full_after_inject;
#endif
    printf("=== EJECT phase n=%ld (sum=%ld) ===\n", n, sum);
    printf("  time: %.3f ms (%.1f ns/op)\n", (t3-t2)*1000.0, (t3-t2)*1e9/(double)n);
    printf("  alloc_links=%zu (%.2f/op)\n", pkt_eject, (double)pkt_eject/(double)n);
    printf("  alloc_pairs=%zu (%.2f/op)\n", pair_eject, (double)pair_eject/(double)n);
#ifdef KT_DIFF_TRACE
    printf("  full=%zu  diff=%zu  diff/total=%.3f\n",
           full_eject, diff_eject,
           (double)diff_eject / ((double)diff_eject + (double)full_eject + 1e-9));
#endif

    /* Phase 3: build via push */
    kt_reset_alloc_counters();
    d = kt_empty();
    double t4 = now_sec();
    for (long i = 0; i < n; i++) d = kt_push((kt_elem)&storage[i], d);
    double t5 = now_sec();
    size_t pkt_push = kt_alloc_packets();
    size_t pair_push = kt_alloc_pairs();
    printf("=== PUSH phase n=%ld ===\n", n);
    printf("  time: %.3f ms (%.1f ns/op)\n", (t5-t4)*1000.0, (t5-t4)*1e9/(double)n);
    printf("  alloc_links=%zu (%.2f/op)\n", pkt_push, (double)pkt_push/(double)n);
    printf("  alloc_pairs=%zu (%.2f/op)\n", pair_push, (double)pair_push/(double)n);

    /* Phase 4: drain via pop */
    sum = 0;
    double t6 = now_sec();
    for (long i = 0; i < n; i++) {
        kt_elem e = NULL; int ne;
        d = kt_pop(d, &e, &ne);
        if (e) sum += *(long*)e;
    }
    double t7 = now_sec();
    size_t pkt_pop = kt_alloc_packets() - pkt_push;
    size_t pair_pop = kt_alloc_pairs() - pair_push;
    printf("=== POP phase n=%ld (sum=%ld) ===\n", n, sum);
    printf("  time: %.3f ms (%.1f ns/op)\n", (t7-t6)*1000.0, (t7-t6)*1e9/(double)n);
    printf("  alloc_links=%zu (%.2f/op)\n", pkt_pop, (double)pkt_pop/(double)n);
    printf("  alloc_pairs=%zu (%.2f/op)\n", pair_pop, (double)pair_pop/(double)n);

    return 0;
}
