/* profile_path.c — count which path each pop op goes through.
 * Add temporary counters around each branch in kt_pop. */

#include "ktdeque.h"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

extern size_t kt_alloc_packets(void);
extern size_t kt_alloc_pairs(void);
extern void   kt_reset_alloc_counters(void);
extern size_t kt_diff_count(void);
extern size_t kt_full_count(void);

/* These globals are set in ktdeque_dequeptr.c via #ifdef KT_PATH_TRACE. */
extern size_t kt_path_pop_pure_ending;
extern size_t kt_path_pop_diff_simple;
extern size_t kt_path_pop_full_simple;
extern size_t kt_path_pop_redtrigger;
extern size_t kt_path_pop_psize_zero;
extern size_t kt_path_pop_calls;
extern size_t kt_path_pop_p1size[6];
extern size_t kt_path_inj_calls;
extern size_t kt_path_inj_diff_simple;
extern size_t kt_path_inj_full_simple;
extern size_t kt_path_inj_redtrigger;
extern size_t kt_path_inj_pure_ending;
extern size_t kt_path_inj_s1size[6];
extern size_t kt_path_gor_case1;
extern size_t kt_path_gor_case2;
extern size_t kt_path_gor_case3;
extern size_t kt_path_make_small_calls;

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

    kt_deque d = kt_empty();
    int use_eject = (argc > 2 && argv[2][0] == 'e');
    int trace_inject = (argc > 2 && argv[2][0] == 'i');
    if (trace_inject) {
        kt_path_inj_calls = 0;
        kt_path_inj_diff_simple = 0;
        kt_path_inj_full_simple = 0;
        kt_path_inj_redtrigger = 0;
        kt_path_inj_pure_ending = 0;
        for (int i = 0; i < 6; i++) kt_path_inj_s1size[i] = 0;
        kt_path_gor_case1 = kt_path_gor_case2 = kt_path_gor_case3 = 0;
        double tt0 = now_sec();
        for (long i = 0; i < n; i++) d = kt_inject(d, (kt_elem)&storage[i]);
        double tt1 = now_sec();
        printf("inject N=%ld: %.1f ns/op  calls=%zu\n",
               n, (tt1-tt0)*1e9/(double)n, kt_path_inj_calls);
        printf("  pure_ending=%zu\n", kt_path_inj_pure_ending);
        printf("  diff_simple=%zu (%.1f%%)\n", kt_path_inj_diff_simple,
               100.0*(double)kt_path_inj_diff_simple/(double)n);
        printf("  full_simple=%zu (%.1f%%)\n", kt_path_inj_full_simple,
               100.0*(double)kt_path_inj_full_simple/(double)n);
        printf("  redtrigger =%zu (%.1f%%)\n", kt_path_inj_redtrigger,
               100.0*(double)kt_path_inj_redtrigger/(double)n);
        printf("  s1_size: B0=%zu B1=%zu B2=%zu B3=%zu B4=%zu B5=%zu\n",
               kt_path_inj_s1size[0], kt_path_inj_s1size[1],
               kt_path_inj_s1size[2], kt_path_inj_s1size[3],
               kt_path_inj_s1size[4], kt_path_inj_s1size[5]);
        printf("  gor_case1/2/3 = %zu/%zu/%zu\n",
               kt_path_gor_case1, kt_path_gor_case2, kt_path_gor_case3);
        return 0;
    }
    for (long i = 0; i < n; i++) {
        if (use_eject) d = kt_inject(d, (kt_elem)&storage[i]);
        else           d = kt_push  ((kt_elem)&storage[i], d);
    }

    kt_path_pop_pure_ending = 0;
    kt_path_pop_diff_simple = 0;
    kt_path_pop_full_simple = 0;
    kt_path_pop_redtrigger  = 0;
    kt_path_pop_psize_zero = 0;
    kt_path_pop_calls = 0;
    kt_path_gor_case1 = 0;
    kt_path_gor_case2 = 0;
    kt_path_gor_case3 = 0;
    kt_path_make_small_calls = 0;

    double t0 = now_sec();
    long sum = 0;
    for (long i = 0; i < n; i++) {
        kt_elem e = NULL; int ne;
        if (use_eject) d = kt_eject(d, &e, &ne);
        else           d = kt_pop  (d, &e, &ne);
        if (e) sum += *(long*)e;
    }
    double t1 = now_sec();
    printf("%s N=%ld: %.1f ns/op  sum=%ld  calls=%zu\n",
           use_eject ? "eject" : "pop",
           n, (t1-t0)*1e9/(double)n, sum, kt_path_pop_calls);
    printf("  pure_ending=%zu (%.1f%%)\n", kt_path_pop_pure_ending,
           100.0*(double)kt_path_pop_pure_ending/(double)n);
    printf("  diff_simple=%zu (%.1f%%)\n", kt_path_pop_diff_simple,
           100.0*(double)kt_path_pop_diff_simple/(double)n);
    printf("  full_simple=%zu (%.1f%%)\n", kt_path_pop_full_simple,
           100.0*(double)kt_path_pop_full_simple/(double)n);
    printf("  redtrigger =%zu (%.1f%%)\n", kt_path_pop_redtrigger,
           100.0*(double)kt_path_pop_redtrigger/(double)n);
    printf("  pre_size_0 =%zu (%.1f%%)\n", kt_path_pop_psize_zero,
           100.0*(double)kt_path_pop_psize_zero/(double)n);
    printf("  gor_case1  =%zu (%.1f%%)\n", kt_path_gor_case1,
           100.0*(double)kt_path_gor_case1/(double)n);
    printf("  gor_case2  =%zu (%.1f%%)\n", kt_path_gor_case2,
           100.0*(double)kt_path_gor_case2/(double)n);
    printf("  gor_case3  =%zu (%.1f%%)\n", kt_path_gor_case3,
           100.0*(double)kt_path_gor_case3/(double)n);
    printf("  make_small =%zu\n", kt_path_make_small_calls);
    printf("  p1_size distribution: B0=%zu B1=%zu B2=%zu B3=%zu B4=%zu B5=%zu\n",
           kt_path_pop_p1size[0], kt_path_pop_p1size[1],
           kt_path_pop_p1size[2], kt_path_pop_p1size[3],
           kt_path_pop_p1size[4], kt_path_pop_p1size[5]);
    return 0;
}
