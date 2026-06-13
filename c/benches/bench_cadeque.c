/* bench_cadeque.c — microbenchmark of the §6 catenable C port.
 *
 * Mirrors the workloads of ocaml/bench/cadeque_compare.ml so the C
 * numbers line up against the Viennot-OCaml and KTf-OCaml columns:
 * push / inject / pop-drain / eject-drain / mixed / concat-fold /
 * concat-tree / interleave / persistent-fork.  Prints ns/op.
 *
 * Args: ./bench_cadeque [N]    (default 1000000)
 *
 * Note: ground elements are unboxed (no per-element malloc); the spine
 * nodes and the rarer small/big cells use malloc with no arena
 * compaction on this path, so these numbers are an honest first-cut,
 * not the compaction-tuned regime the §4 C deque reports.  Elements
 * are 8-byte aligned (<<3) per the §6 contract. */
#include "ktcadeque.h"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>

static double now(void) {
    struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec + t.tv_nsec * 1e-9;
}

static kc_cadeque build_push(long n) {
    kc_cadeque d = kc_empty();
    for (long i = 0; i < n; i++) d = kc_push((kt_elem)(intptr_t)(((long)i+1)<<3), d);
    return d;
}
static kc_cadeque build_inject(long n) {
    kc_cadeque d = kc_empty();
    for (long i = 0; i < n; i++) d = kc_inject(d, (kt_elem)(intptr_t)(((long)i+1)<<3));
    return d;
}
static kc_cadeque block(int len) {
    kc_cadeque b = kc_empty();
    for (int i = 0; i < len; i++) b = kc_inject(b, (kt_elem)(intptr_t)(((long)i+1)<<3));
    return b;
}

int main(int argc, char** argv) {
    long N = argc > 1 ? atol(argv[1]) : 1000000;
    volatile intptr_t sink = 0;
    double t0, t1;

    /* push */
    t0 = now(); kc_cadeque dp = build_push(N); t1 = now();
    printf("push n            %7.1f ns/op\n", (t1-t0)*1e9/N);

    /* inject */
    t0 = now(); kc_cadeque di = build_inject(N); t1 = now();
    printf("inject n          %7.1f ns/op\n", (t1-t0)*1e9/N);

    /* pop-drain (after push n) */
    t0 = now();
    { kc_cadeque d = dp; for (;;) { kt_elem e; int ok; d = kc_pop(d, &e, &ok);
        if (!ok) break; sink += (intptr_t)e; } }
    t1 = now();
    printf("pop drain         %7.1f ns/op\n", (t1-t0)*1e9/N);

    /* eject-drain (after inject n) */
    t0 = now();
    { kc_cadeque d = di; for (;;) { kt_elem e; int ok; d = kc_eject(d, &e, &ok);
        if (!ok) break; sink += (intptr_t)e; } }
    t1 = now();
    printf("eject drain       %7.1f ns/op\n", (t1-t0)*1e9/N);

    /* mixed push/push/pop (3n ops) */
    t0 = now();
    { kc_cadeque d = kc_empty();
      for (long i = 0; i < N; i++) {
          d = kc_push((kt_elem)(intptr_t)((long)i<<3), d);
          d = kc_push((kt_elem)(intptr_t)((long)i<<3), d);
          kt_elem e; int ok; d = kc_pop(d, &e, &ok); sink += (intptr_t)e;
      } }
    t1 = now();
    printf("mixed (3n ops)    %7.1f ns/op\n", (t1-t0)*1e9/(3*N));

    /* concat-fold: N/64 blocks of 64 */
    { kc_cadeque b = block(64);
      t0 = now(); kc_cadeque acc = kc_empty();
      for (long i = 0; i < N/64; i++) acc = kc_concat(acc, b);
      t1 = now();
      sink += (intptr_t)kc_length(acc);
      printf("concat fold       %7.1f ns/op\n", (t1-t0)*1e9/(N/64)); }

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
      printf("concat tree       %7.1f ns/op\n", (t1-t0)*1e9/(N/64));
      free(arr); }

    /* interleave: concat(8)+pop x4 */
    { t0 = now(); kc_cadeque d = build_push(8); long ops = 0;
      for (long i = 0; i < N/12; i++) {
          kc_cadeque b8 = build_push(8);
          d = kc_concat(d, b8); ops++;
          for (int k = 0; k < 4; k++) { kt_elem e; int ok; d = kc_pop(d, &e, &ok);
              if (ok) sink += (intptr_t)e; ops++; }
      }
      t1 = now();
      printf("interleave        %7.1f ns/op\n", (t1-t0)*1e9/ops); }

    /* persistent fork: pop the same d N times */
    { kc_cadeque d = build_push(1024);
      t0 = now();
      for (long i = 0; i < N; i++) { kt_elem e; int ok;
          kc_cadeque d2 = kc_pop(d, &e, &ok); sink += (intptr_t)e;
          (void)d2; }
      t1 = now();
      printf("persistent fork   %7.1f ns/op\n", (t1-t0)*1e9/N); }

    if (sink == 0x7fffffff) printf("");  /* keep sink live */
    return 0;
}
