/* fuzz_cadeque.c — bug hunter for the §6 catenable C port (ktcadeque.c).
 *
 * Drives a bank of K persistent catenable deques ("registers") with a
 * program decoded from a byte stream — push / inject / pop / eject /
 * concat / compact — and checks every step against a reference model
 * (a doubly-ended array per register).  Any divergence, or any
 * pop/eject value mismatch, or any wrong length, calls abort(); built
 * with ASan + UBSan it also abort()s on memory errors.  This exercises
 * the parts the unit tests can't enumerate: arbitrary concat topologies
 * (which build SBig/SSmall boxes inside buffers) interleaved with
 * compaction (which must trace and relocate those nested §4 deques) and
 * with the unboxed-ground tagging.
 *
 * THREE build modes from this one file:
 *
 *  1. Deterministic seed-sweep (default; CI-friendly, no fuzzer needed):
 *       gcc -O1 -g -fsanitize=address,undefined -DNDEBUG -Ic/include \
 *           -o c/fuzz_cadeque c/src/ktcadeque.c c/src/ktdeque_dequeptr.c \
 *           c/tests/fuzz_cadeque.c
 *       ASAN_OPTIONS=detect_leaks=0 ./c/fuzz_cadeque 2000   # 2000 seeds
 *     (`make fuzz_cadeque` / `make check-fuzz-cadeque`.)
 *
 *  2. AFL coverage-guided (forkserver -> fresh state per input):
 *       afl-cc -O2 -DAFL_HARNESS -DNDEBUG -Ic/include -o c/fuzz_cadeque_afl \
 *           c/src/ktcadeque.c c/src/ktdeque_dequeptr.c c/tests/fuzz_cadeque.c
 *       AFL_SKIP_CPUFREQ=1 afl-fuzz -i c/tests/afl_seeds_cadeque \
 *           -o c/tests/afl_findings_cadeque -- ./c/fuzz_cadeque_afl
 *     (`make fuzz_cadeque_afl` builds it; `make run-fuzz-cadeque-afl` runs.)
 *
 *  3. libFuzzer (in-process, coverage-guided):
 *       clang -O1 -g -fsanitize=fuzzer,address,undefined -DFUZZ_LIBFUZZER \
 *           -DNDEBUG -Ic/include -o c/fuzz_cadeque_lf c/src/ktcadeque.c \
 *           c/src/ktdeque_dequeptr.c c/tests/fuzz_cadeque.c
 *       ASAN_OPTIONS=detect_leaks=0 ./c/fuzz_cadeque_lf -rss_limit_mb=4096
 *     (`make fuzz_cadeque_lf`.)
 */
#include "ktcadeque.h"
#include "ktdeque.h"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>

#define KREG 4              /* number of registers */

/* ---- reference model: a doubly-ended growable array of element values ---- */
typedef struct { long* a; size_t lo, hi, cap; } refdq;
static void ref_init(refdq* d) { d->cap = 16; d->a = malloc(d->cap*sizeof(long)); d->lo = d->hi = d->cap/2; }
static void ref_free(refdq* d) { free(d->a); d->a = NULL; d->lo = d->hi = d->cap = 0; }
static void ref_grow(refdq* d) {
    size_t n = d->hi - d->lo, nc = d->cap ? d->cap*4 : 16;
    long* na = malloc(nc*sizeof(long));
    size_t nl = nc/2 - n/2;
    if (d->a) memcpy(na+nl, d->a+d->lo, n*sizeof(long));
    free(d->a); d->a = na; d->cap = nc; d->lo = nl; d->hi = nl+n;
}
static void ref_push(refdq* d, long v)   { if (d->lo == 0) ref_grow(d); d->a[--d->lo] = v; }
static void ref_inject(refdq* d, long v) { if (d->hi == d->cap) ref_grow(d); d->a[d->hi++] = v; }
static int  ref_len(refdq* d)            { return (int)(d->hi - d->lo); }

static void __attribute__((noreturn)) die(const char* what, int reg) {
    fprintf(stderr, "fuzz_cadeque: DIVERGENCE — %s (reg %d)\n", what, reg);
    abort();
}

/* walk a register and compare its full sequence to the model */
typedef struct { long* a; size_t i, n; int ok; } walk_ctx;
static void walk_cb(kt_elem e, void* ctx) {
    walk_ctx* w = (walk_ctx*)ctx;
    if (w->i >= w->n || (long)(intptr_t)e != w->a[w->i]) w->ok = 0;
    w->i++;
}

static long g_serial = 1;   /* unique, monotone; <<3 keeps bit0..2 and bit63 clear */

/* Run one program (a byte stream).  abort() on any divergence. */
static void run_program(const uint8_t* data, size_t n) {
    kc_cadeque reg[KREG];
    refdq      mdl[KREG];
    for (int i = 0; i < KREG; i++) { reg[i] = kc_empty(); ref_init(&mdl[i]); }

    for (size_t k = 0; k < n; k++) {
        unsigned b = data[k];
        int op = b % 6;
        int i  = (int)((b >> 3) % KREG);
        switch (op) {
            case 0: { long v = (g_serial++) << 3;
                reg[i] = kc_push((kt_elem)(intptr_t)v, reg[i]); ref_push(&mdl[i], v); break; }
            case 1: { long v = (g_serial++) << 3;
                reg[i] = kc_inject(reg[i], (kt_elem)(intptr_t)v); ref_inject(&mdl[i], v); break; }
            case 2: { kt_elem e; int ne;
                reg[i] = kc_pop(reg[i], &e, &ne);
                int rne = ref_len(&mdl[i]) > 0;
                if (ne != rne) die("pop nonempty flag", i);
                if (ne) { if ((long)(intptr_t)e != mdl[i].a[mdl[i].lo]) die("pop value", i); mdl[i].lo++; }
                break; }
            case 3: { kt_elem e; int ne;
                reg[i] = kc_eject(reg[i], &e, &ne);
                int rne = ref_len(&mdl[i]) > 0;
                if (ne != rne) die("eject nonempty flag", i);
                if (ne) { if ((long)(intptr_t)e != mdl[i].a[mdl[i].hi-1]) die("eject value", i); mdl[i].hi--; }
                break; }
            case 4: { int j = (i + 1 + (int)((b >> 5) % (KREG - 1))) % KREG;
                reg[i] = kc_concat(reg[i], reg[j]);
                for (size_t t = mdl[j].lo; t < mdl[j].hi; t++) ref_inject(&mdl[i], mdl[j].a[t]);
                mdl[j].lo = mdl[j].hi = mdl[j].cap/2;        /* model j now empty */
                reg[j] = kc_empty();
                break; }
            case 5:                                          /* compact ALL live registers */
                kc_arena_compact(reg, KREG);
                break;
        }
        if (op != 5 && (int)kc_length(reg[i]) != ref_len(&mdl[i])) die("length", i);
    }

    /* final: every register's full sequence must match its model */
    for (int i = 0; i < KREG; i++) {
        int len = ref_len(&mdl[i]);
        long* exp = (len > 0) ? &mdl[i].a[mdl[i].lo] : NULL;
        walk_ctx w = { exp, 0, (size_t)len, 1 };
        kc_walk(reg[i], walk_cb, &w);
        if (!w.ok || (int)w.i != len) die("final walk", i);
        ref_free(&mdl[i]);
    }

    /* reclaim the §4 buffer arena between programs (no live roots) so a
     * long in-process campaign does not grow without bound */
    { kt_deque none = 0; kt_arena_compact(&none, 0); }
}

#if defined(FUZZ_LIBFUZZER)
int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) {
    run_program(data, size);
    return 0;
}
#elif defined(AFL_HARNESS)
#define MAX_OPS 8192
int main(void) {
    unsigned char buf[MAX_OPS];
    int n = (int)read(0, buf, sizeof(buf));
    if (n <= 0) return 0;
    run_program(buf, (size_t)n);
    return 0;
}
#else
/* Deterministic seed-sweep — no fuzzer required (CI gate). */
static uint64_t xs;
static uint64_t xn(void) { uint64_t x = xs; x ^= x<<13; x ^= x>>7; x ^= x<<17; xs = x; return x; }
int main(int argc, char** argv) {
    int n_seeds = argc > 1 ? atoi(argv[1]) : 2000;
    int lengths[] = { 64, 256, 1024, 4096 };
    unsigned char prog[4096];
    for (int s = 0; s < n_seeds; s++) {
        xs = (uint64_t)s * 0x9E3779B97F4A7C15ull + 0xD1B54A32D192ED03ull;
        int len = lengths[s % 4];
        for (int i = 0; i < len; i++) prog[i] = (unsigned char)(xn() & 0xff);
        run_program(prog, (size_t)len);
        if ((s % 200) == 0) fprintf(stderr, "  progress: %d/%d\n", s, n_seeds);
    }
    printf("fuzz_cadeque: %d seeds OK\n", n_seeds);
    return 0;
}
#endif
