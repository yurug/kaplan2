/* bench.c — microbenchmark for the KT deque.
 *
 * KT_COMPACT_INTERVAL controls chain-link arena compaction: every K ops a
 * Cheney-style copy collector reclaims dead chain links from the bump arena,
 * keeping the working set small enough to fit in L2.  Without compaction, the
 * arena grows unbounded across long pop / eject drains and the working set
 * spills into L3 / RAM, costing ~3-5× per-op latency.  The default is
 * K = 4096 (a single L1d cycle of activity per compact), which the bench
 * empirically shows runs each operation in 30-35 ns/op.  Override at build
 * time with `-DKT_COMPACT_INTERVAL=N` (use 0 to disable entirely).
 *
 * KT_FULL_COMPACT_INTERVAL is similar but additionally compacts pair blocks
 * (bounding RSS to O(reachable)).  Off by default because chain-link compact
 * already gives most of the benefit on the bench's workloads.
 */

#include "ktdeque.h"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <sys/resource.h>

static long max_rss_kb(void) {
    struct rusage ru;
    if (getrusage(RUSAGE_SELF, &ru) != 0) return -1;
    /* On Linux, ru_maxrss is in kilobytes. */
    return ru.ru_maxrss;
}

#ifndef KT_COMPACT_INTERVAL
#define KT_COMPACT_INTERVAL 4096
#endif

#ifndef KT_FULL_COMPACT_INTERVAL
#define KT_FULL_COMPACT_INTERVAL 0
#endif

static inline void maybe_compact(kt_deque* d, int i) {
#if KT_COMPACT_INTERVAL > 0
    if ((i % KT_COMPACT_INTERVAL) == (KT_COMPACT_INTERVAL - 1)) {
        kt_arena_compact(d, 1);
    }
#endif
#if KT_FULL_COMPACT_INTERVAL > 0
    if ((i % KT_FULL_COMPACT_INTERVAL) == (KT_FULL_COMPACT_INTERVAL - 1)) {
        kt_arena_compact_full(d, 1);
    }
#endif
#if KT_COMPACT_INTERVAL == 0 && KT_FULL_COMPACT_INTERVAL == 0
    (void)d; (void)i;
#endif
}

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static long* values;

static void prepare(int n) {
    values = malloc(sizeof(long) * (size_t)n);
    for (int i = 0; i < n; i++) values[i] = i + 1;
}

static void bench(int n) {
    printf("=== n = %d ===\n", n);
    prepare(n);

    /* Pure pushes */
    {
        kt_deque d = kt_empty();
        double t0 = now_sec();
        for (int i = 0; i < n; i++) {
            d = kt_push(kt_base(&values[i]), d);
            maybe_compact(&d, i);
        }
        double t1 = now_sec();
        printf("  push   : %8.3f ms (%6.1f ns/op)\n",
               (t1 - t0) * 1000.0, (t1 - t0) * 1e9 / n);
    }

    /* Pure injects then ejects */
    {
        kt_deque d = kt_empty();
        double t0 = now_sec();
        for (int i = 0; i < n; i++) {
            d = kt_inject(d, kt_base(&values[i]));
            maybe_compact(&d, i);
        }
        double t1 = now_sec();
        printf("  inject : %8.3f ms (%6.1f ns/op)\n",
               (t1 - t0) * 1000.0, (t1 - t0) * 1e9 / n);

        double t2 = now_sec();
        for (int i = 0; i < n; i++) {
            kt_elem e; int ne;
            d = kt_eject(d, &e, &ne);
            if (!ne) break;
            maybe_compact(&d, i);
        }
        double t3 = now_sec();
        printf("  eject  : %8.3f ms (%6.1f ns/op)\n",
               (t3 - t2) * 1000.0, (t3 - t2) * 1e9 / n);
    }

    /* push then pop */
    {
        kt_deque d = kt_empty();
        for (int i = 0; i < n; i++) {
            d = kt_push(kt_base(&values[i]), d);
            maybe_compact(&d, i);
        }
        double t0 = now_sec();
        for (int i = 0; i < n; i++) {
            kt_elem e; int ne;
            d = kt_pop(d, &e, &ne);
            if (!ne) break;
            maybe_compact(&d, i);
        }
        double t1 = now_sec();
        printf("  pop    : %8.3f ms (%6.1f ns/op)\n",
               (t1 - t0) * 1000.0, (t1 - t0) * 1e9 / n);
    }

    /* Mixed: push, push, pop loop */
    {
        kt_deque d = kt_empty();
        double t0 = now_sec();
        for (int i = 0; i < n; i++) {
            d = kt_push(kt_base(&values[i % n]), d);
            d = kt_inject(d, kt_base(&values[(i+1) % n]));
            kt_elem e; int ne;
            d = kt_pop(d, &e, &ne);
            maybe_compact(&d, i);
        }
        double t1 = now_sec();
        printf("  mixed  : %8.3f ms (%6.1f ns/op total)\n",
               (t1 - t0) * 1000.0, (t1 - t0) * 1e9 / (3.0 * (double)n));
    }

    free(values);
    printf("\n");
}

/* Phase V region workload: create region -> N pushes -> N pops ->
 * destroy region.  Times each phase plus the destroy.
 *
 * Each phase uses a fresh empty deque and a fresh region (so the
 * `roots[]` array passed to kt_region_compact always lists EVERY live
 * deque, satisfying the safety contract).  This isolates per-op cost
 * from cross-phase interference.  */
static void bench_region(int n) {
    printf("=== region n = %d ===\n", n);
    prepare(n);

    double t_create_total = 0.0;
    double t_destroy_total = 0.0;

    /* push phase */
    {
        double t0 = now_sec();
        kt_region* reg = kt_region_create(0);
        double t1 = now_sec();
        t_create_total += (t1 - t0);
        kt_deque d = kt_empty_in(reg);
        double tp0 = now_sec();
        for (int i = 0; i < n; i++) {
            d = kt_push_in(reg, kt_base(&values[i]), d);
#if KT_COMPACT_INTERVAL > 0
            if ((i % KT_COMPACT_INTERVAL) == (KT_COMPACT_INTERVAL - 1)) {
                kt_region_compact(reg, &d, 1);
            }
#endif
        }
        double tp1 = now_sec();
        printf("  push   : %8.3f ms (%6.1f ns/op)\n",
               (tp1 - tp0) * 1000.0, (tp1 - tp0) * 1e9 / n);
        double td0 = now_sec();
        kt_region_destroy(reg);
        double td1 = now_sec();
        t_destroy_total += (td1 - td0);
    }
    /* inject phase */
    {
        double t0 = now_sec();
        kt_region* reg = kt_region_create(0);
        double t1 = now_sec();
        t_create_total += (t1 - t0);
        kt_deque d = kt_empty_in(reg);
        double tp0 = now_sec();
        for (int i = 0; i < n; i++) {
            d = kt_inject_in(reg, d, kt_base(&values[i]));
#if KT_COMPACT_INTERVAL > 0
            if ((i % KT_COMPACT_INTERVAL) == (KT_COMPACT_INTERVAL - 1)) {
                kt_region_compact(reg, &d, 1);
            }
#endif
        }
        double tp1 = now_sec();
        printf("  inject : %8.3f ms (%6.1f ns/op)\n",
               (tp1 - tp0) * 1000.0, (tp1 - tp0) * 1e9 / n);
        double td0 = now_sec();
        kt_region_destroy(reg);
        double td1 = now_sec();
        t_destroy_total += (td1 - td0);
    }
    /* pop: build via push then drain via pop, compacting (root = d). */
    {
        double t0 = now_sec();
        kt_region* reg = kt_region_create(0);
        double t1 = now_sec();
        t_create_total += (t1 - t0);
        kt_deque d = kt_empty_in(reg);
        for (int i = 0; i < n; i++) {
            d = kt_push_in(reg, kt_base(&values[i]), d);
        }
        double tp0 = now_sec();
        for (int i = 0; i < n; i++) {
            kt_elem e; int ne;
            d = kt_pop_in(reg, d, &e, &ne);
            if (!ne) break;
#if KT_COMPACT_INTERVAL > 0
            if ((i % KT_COMPACT_INTERVAL) == (KT_COMPACT_INTERVAL - 1)) {
                kt_region_compact(reg, &d, 1);
            }
#endif
        }
        double tp1 = now_sec();
        printf("  pop    : %8.3f ms (%6.1f ns/op)\n",
               (tp1 - tp0) * 1000.0, (tp1 - tp0) * 1e9 / n);
        double td0 = now_sec();
        kt_region_destroy(reg);
        double td1 = now_sec();
        t_destroy_total += (td1 - td0);
    }
    /* eject: build via inject then drain via eject. */
    {
        double t0 = now_sec();
        kt_region* reg = kt_region_create(0);
        double t1 = now_sec();
        t_create_total += (t1 - t0);
        kt_deque d = kt_empty_in(reg);
        for (int i = 0; i < n; i++) {
            d = kt_inject_in(reg, d, kt_base(&values[i]));
        }
        double tp0 = now_sec();
        for (int i = 0; i < n; i++) {
            kt_elem e; int ne;
            d = kt_eject_in(reg, d, &e, &ne);
            if (!ne) break;
#if KT_COMPACT_INTERVAL > 0
            if ((i % KT_COMPACT_INTERVAL) == (KT_COMPACT_INTERVAL - 1)) {
                kt_region_compact(reg, &d, 1);
            }
#endif
        }
        double tp1 = now_sec();
        printf("  eject  : %8.3f ms (%6.1f ns/op)\n",
               (tp1 - tp0) * 1000.0, (tp1 - tp0) * 1e9 / n);
        double td0 = now_sec();
        kt_region_destroy(reg);
        double td1 = now_sec();
        t_destroy_total += (td1 - td0);
    }
    /* mixed: push, inject, pop. */
    {
        double t0 = now_sec();
        kt_region* reg = kt_region_create(0);
        double t1 = now_sec();
        t_create_total += (t1 - t0);
        kt_deque dm = kt_empty_in(reg);
        double tp0 = now_sec();
        for (int i = 0; i < n; i++) {
            dm = kt_push_in(reg, kt_base(&values[i % n]), dm);
            dm = kt_inject_in(reg, dm, kt_base(&values[(i+1) % n]));
            kt_elem e; int ne;
            dm = kt_pop_in(reg, dm, &e, &ne);
#if KT_COMPACT_INTERVAL > 0
            if ((i % KT_COMPACT_INTERVAL) == (KT_COMPACT_INTERVAL - 1)) {
                kt_region_compact(reg, &dm, 1);
            }
#endif
        }
        double tp1 = now_sec();
        printf("  mixed  : %8.3f ms (%6.1f ns/op total)\n",
               (tp1 - tp0) * 1000.0, (tp1 - tp0) * 1e9 / (3 * n));
        double td0 = now_sec();
        kt_region_destroy(reg);
        double td1 = now_sec();
        t_destroy_total += (td1 - td0);
    }

    printf("  create : %8.3f us (sum of 5 creates)\n", t_create_total * 1e6);
    printf("  destroy: %8.3f us (sum of 5 destroys)\n", t_destroy_total * 1e6);

    free(values);
    printf("\n");
}

/* Warm arena, code paths, branch predictor before timed measurement.
 * Without this the first `bench()` row absorbed first-touch costs
 * (~150-200 ns/op at N=10^4 instead of the steady-state ~35-60 ns/op). */
static void warmup_runtime(void) {
    long warm_values[5000];
    for (int i = 0; i < 5000; i++) warm_values[i] = i + 1;
    kt_deque d = kt_empty();
    for (int i = 0; i < 5000; i++) {
        d = kt_push(kt_base(&warm_values[i]), d);
    }
    for (int i = 0; i < 5000; i++) {
        kt_elem e; int ne;
        d = kt_pop(d, &e, &ne);
        if (!ne) break;
    }
    /* Also exercise inject/eject paths and the compaction path. */
    d = kt_empty();
    for (int i = 0; i < 5000; i++) {
        d = kt_inject(d, kt_base(&warm_values[i]));
        if ((i & 0xfff) == 0xfff) kt_arena_compact(&d, 1);
    }
}

/* If invoked with one or more numeric arguments, run the core `bench`
 * (no region workload) at exactly those sizes — used by the sweep
 * harness in bench/sweep.sh.  With no arguments, run the default
 * three-size sweep + the region workload. */
int main(int argc, char** argv) {
    warmup_runtime();
    if (argc > 1) {
        for (int i = 1; i < argc; i++) {
            long n = strtol(argv[i], NULL, 10);
            if (n <= 0) {
                fprintf(stderr, "bench: bad size '%s'\n", argv[i]);
                return 2;
            }
            bench((int)n);
        }
        printf("max RSS at end: %ld KB\n", max_rss_kb());
        return 0;
    }
    bench(10000);
    bench(100000);
    bench(1000000);
    printf("=== Phase V region workload ===\n");
    bench_region(10000);
    bench_region(100000);
    bench_region(1000000);
    printf("max RSS at end: %ld KB\n", max_rss_kb());
    return 0;
}
