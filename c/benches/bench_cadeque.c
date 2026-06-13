/* bench_cadeque.c — microbenchmark of the §6 catenable C port.
 *
 * Mirrors the workloads of ocaml/bench/cadeque_compare.ml so the C
 * numbers line up against the Viennot-OCaml and KTf-OCaml columns:
 * push / inject / pop-drain / eject-drain / mixed / concat-fold /
 * concat-tree / interleave / persistent-fork.  Prints ns/op.
 *
 * Args: ./bench_cadeque [N] [COMPACT_K]   (defaults: 1000000, 4096)
 *
 * Compaction is caller-driven, exactly like the §4 deque's
 * kt_arena_compact (which `make bench` runs every 4096 ops): the
 * per-element workloads call kc_arena_compact every COMPACT_K ops on the
 * live deque to reclaim dead intermediate versions.  COMPACT_K=0
 * disables it (the unreclaimed regime).  Ground elements are unboxed and
 * 8-byte aligned (<<3) per the §6 contract. */
#include "ktcadeque.h"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>

static double now(void) {
    struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec + t.tv_nsec * 1e-9;
}

static long g_ck = 4096;   /* compaction interval (0 = off) */

/* PLAIN builders — never compact (compaction is global, so a helper must
 * not compact while the caller holds other live deques).  Compaction in
 * the build-heavy workloads is done at the top level, where the full
 * live-root set is known. */
static kc_cadeque build_push(long n) {
    kc_cadeque d = kc_empty();
    for (long i = 0; i < n; i++)
        d = kc_push((kt_elem)(intptr_t)(((long)i+1)<<3), d);
    return d;
}
static kc_cadeque build_inject(long n) {
    kc_cadeque d = kc_empty();
    for (long i = 0; i < n; i++)
        d = kc_inject(d, (kt_elem)(intptr_t)(((long)i+1)<<3));
    return d;
}
static kc_cadeque block(int len) {
    kc_cadeque b = kc_empty();
    for (int i = 0; i < len; i++) b = kc_inject(b, (kt_elem)(intptr_t)(((long)i+1)<<3));
    return b;
}

int main(int argc, char** argv) {
    long N = argc > 1 ? atol(argv[1]) : 1000000;
    g_ck   = argc > 2 ? atol(argv[2]) : 4096;
    volatile intptr_t sink = 0;
    double t0, t1;
    double r_push, r_inj, r_pop, r_eje, r_mix, r_cf, r_ct, r_il, r_fork;

    /* Each build is immediately followed by its drain so at most one large
     * deque is live at a time — the compaction root set is then just {d},
     * honouring the "all live deques are roots" contract. */

    /* push, then pop-drain.  Build with top-level compaction (the deque
     * is the sole live one here), reclaiming dead versions as we go. */
    { kc_cadeque d = kc_empty();
      t0 = now();
      for (long i = 0; i < N; i++) {
          d = kc_push((kt_elem)(intptr_t)(((long)i+1)<<3), d);
          if (g_ck && (i % g_ck) == 0) { kc_cadeque r[1]={d}; kc_arena_compact(r,1); d=r[0]; }
      }
      t1 = now(); r_push = (t1-t0)*1e9/N;
      t0 = now();
      { long i = 0;
        for (;;) { kt_elem e; int ok; d = kc_pop(d, &e, &ok);
          if (!ok) break; sink += (intptr_t)e;
          if (g_ck && (++i % g_ck) == 0) { kc_cadeque r[1]={d}; kc_arena_compact(r,1); d=r[0]; } } }
      t1 = now(); r_pop = (t1-t0)*1e9/N;
    }

    /* inject, then eject-drain */
    { kc_cadeque d = kc_empty();
      t0 = now();
      for (long i = 0; i < N; i++) {
          d = kc_inject(d, (kt_elem)(intptr_t)(((long)i+1)<<3));
          if (g_ck && (i % g_ck) == 0) { kc_cadeque r[1]={d}; kc_arena_compact(r,1); d=r[0]; }
      }
      t1 = now(); r_inj = (t1-t0)*1e9/N;
      t0 = now();
      { long i = 0;
        for (;;) { kt_elem e; int ok; d = kc_eject(d, &e, &ok);
          if (!ok) break; sink += (intptr_t)e;
          if (g_ck && (++i % g_ck) == 0) { kc_cadeque r[1]={d}; kc_arena_compact(r,1); d=r[0]; } } }
      t1 = now(); r_eje = (t1-t0)*1e9/N;
    }

    /* mixed push/push/pop (3n ops) */
    t0 = now();
    { kc_cadeque d = kc_empty();
      for (long i = 0; i < N; i++) {
          d = kc_push((kt_elem)(intptr_t)((long)i<<3), d);
          d = kc_push((kt_elem)(intptr_t)((long)i<<3), d);
          kt_elem e; int ok; d = kc_pop(d, &e, &ok); sink += (intptr_t)e;
          if (g_ck && (i % g_ck) == 0) { kc_cadeque r[1]={d}; kc_arena_compact(r,1); d=r[0]; }
      } }
    t1 = now();
    r_mix = (t1-t0)*1e9/(3*N);

    /* concat-fold: N/64 blocks of 64 */
    { kc_cadeque b = block(64);
      t0 = now(); kc_cadeque acc = kc_empty();
      for (long i = 0; i < N/64; i++) { acc = kc_concat(acc, b);
          /* both acc and the reused block b are live -> both are roots */
          if (g_ck && (i % g_ck) == 0) { kc_cadeque r[2]={acc,b}; kc_arena_compact(r,2); acc=r[0]; b=r[1]; } }
      t1 = now();
      sink += (intptr_t)kc_length(acc);
      r_cf = (t1-t0)*1e9/(N/64); }

    /* concat-tree: pairwise fold of N/64 blocks */
    { int m = (int)(N/64); kc_cadeque* arr = malloc((size_t)m*sizeof(kc_cadeque));
      for (int i = 0; i < m; i++) arr[i] = block(64);
      t0 = now();
      int cnt = m;
      while (cnt > 1) {
          int w = 0;
          for (int i = 0; i+1 < cnt; i += 2) arr[w++] = kc_concat(arr[i], arr[i+1]);
          if (cnt & 1) arr[w++] = arr[cnt-1];
          cnt = w;
      }
      t1 = now();
      sink += (intptr_t)kc_length(arr[0]);
      r_ct = (t1-t0)*1e9/(N/64);
      free(arr); }

    /* interleave: concat(8)+pop x4 */
    { t0 = now(); kc_cadeque d = build_push(8); long ops = 0;
      for (long i = 0; i < N/12; i++) {
          kc_cadeque b8 = build_push(8);
          d = kc_concat(d, b8); ops++;
          for (int k = 0; k < 4; k++) { kt_elem e; int ok; d = kc_pop(d, &e, &ok);
              if (ok) sink += (intptr_t)e; ops++; }
          if (g_ck && (i % g_ck) == 0) { kc_cadeque r[1]={d}; kc_arena_compact(r,1); d=r[0]; }
      }
      t1 = now();
      r_il = (t1-t0)*1e9/ops; }

    /* persistent fork: pop the same fixed d N times (no compaction) */
    { kc_cadeque d = build_push(1024);
      t0 = now();
      for (long i = 0; i < N; i++) { kt_elem e; int ok;
          kc_cadeque d2 = kc_pop(d, &e, &ok); sink += (intptr_t)e;
          (void)d2; }
      t1 = now();
      r_fork = (t1-t0)*1e9/N; }

    if (sink == 0x7fffffff) printf("");  /* keep sink live */

    /* print in canonical order (matches the OCaml comparison table) */
    printf("push n            %7.1f ns/op\n", r_push);
    printf("inject n          %7.1f ns/op\n", r_inj);
    printf("pop drain         %7.1f ns/op\n", r_pop);
    printf("eject drain       %7.1f ns/op\n", r_eje);
    printf("mixed (3n ops)    %7.1f ns/op\n", r_mix);
    printf("concat fold       %7.1f ns/op\n", r_cf);
    printf("concat tree       %7.1f ns/op\n", r_ct);
    printf("interleave        %7.1f ns/op\n", r_il);
    printf("persistent fork   %7.1f ns/op\n", r_fork);
    return 0;
}
