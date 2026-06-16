/* bench_wcet.c — worst-case per-operation timing probe for the §4 C deque.
 *
 * The C analogue of ocaml/bench/wcet.ml.  For each operation
 * (push/inject/pop/eject) we measure, over a battery of reachable states
 * (several op-histories + a seeded random walk), the worst-case ns/op:
 * the MAX over states of the MIN-over-trials mean at each state.  Timing
 * uses persistent re-execution (the op is applied to one saved state
 * many times; the state is immutable so every call repeats the same
 * work), exactly the pattern in bench_adversarial.c.
 *
 * The worst-case *allocation* per op (the deterministic work bound) is
 * measured separately and is already flat across n: see tests/wc_test.c
 * (<= 8 alloc objects/op) and COMPARISON.md.  This binary covers timing.
 *
 * Each state is built, probed, then the arena is flushed before the next
 * — we only ever hold one battery state live, so periodic compaction
 * during timing (root = that one state) respects kt_arena_compact's
 * "enumerate every live deque" contract.
 *
 * Output: a Markdown table on stdout.  Driven from bench/wcet.sh.
 *
 * Usage: bench_wcet [--m M] [--trials T]
 */

#include "ktdeque.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <math.h>

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

/* One element pointer reused everywhere: the §4 deque's structural shape
 * depends on the op sequence, not on element values, so a single
 * 8-aligned slot suffices.  (static long is 8-aligned, bit 63 clear.) */
static long g_elt = 1;
#define ELT kt_base(&g_elt)

/* ---------------- state builders (return deque, set *size) ---------- */

static kt_deque build_push(long n, long* size) {
    kt_deque d = kt_empty();
    for (long i = 0; i < n; i++) d = kt_push(ELT, d);
    *size = n; return d;
}
static kt_deque build_inject(long n, long* size) {
    kt_deque d = kt_empty();
    for (long i = 0; i < n; i++) d = kt_inject(d, ELT);
    *size = n; return d;
}
static kt_deque build_alt(long n, long* size) {
    kt_deque d = kt_empty();
    for (long i = 0; i < n; i++)
        d = (i & 1) ? kt_inject(d, ELT) : kt_push(ELT, d);
    *size = n; return d;
}
static kt_deque build_churn(long n, long* size) {
    kt_deque d = kt_empty();
    long s = 0;
    for (long i = 0; i < n + n / 2; i++) { d = kt_push(ELT, d); s++; }
    for (long i = 0; i < n / 2; i++) {
        kt_elem e; int ok;
        if (s > 0) { d = kt_pop(d, &e, &ok); s--; }
    }
    *size = s; return d;
}
static kt_deque build_random(unsigned seed, long n, long* size) {
    srand(seed);
    kt_deque d = kt_empty();
    long s = 0;
    for (long i = 0; i < n; i++) { d = kt_push(ELT, d); s++; }
    for (long i = 0; i < 2 * n; i++) {
        kt_elem e; int ok;
        switch (rand() % 4) {
            case 0: d = kt_push(ELT, d); s++; break;
            case 1: d = kt_inject(d, ELT); s++; break;
            case 2: if (s > 0) { d = kt_pop(d, &e, &ok); s--; } break;
            default: if (s > 0) { d = kt_eject(d, &e, &ok); s--; } break;
        }
    }
    *size = s; return d;
}

/* ---------------- timing: one op on one saved state ----------------- */
/* opcode: 0 push, 1 inject, 2 pop, 3 eject.  *savedp is relocated by the
 * periodic compaction (root = the single live state), so we update it in
 * place; compaction time is excluded from the measurement. */

static double time_op_ns(int opcode, kt_deque* savedp, long m, int trials) {
    const long CI = 4096;
    double best = INFINITY;
    for (int tr = 0; tr < trials; tr++) {
        double accum = 0.0;
        long i = 0;
        while (i < m) {
            long todo = m - i; if (todo > CI) todo = CI;
            double t0 = now_sec();
            for (long j = 0; j < todo; j++) {
                kt_elem out; int ok; kt_deque r;
                switch (opcode) {
                    case 0: r = kt_push(ELT, *savedp); break;
                    case 1: r = kt_inject(*savedp, ELT); break;
                    case 2: r = kt_pop(*savedp, &out, &ok); break;
                    default: r = kt_eject(*savedp, &out, &ok); break;
                }
                (void)r;
            }
            double t1 = now_sec();
            accum += (t1 - t0);
            i += todo;
            kt_arena_compact(savedp, 1); /* excluded from timing */
        }
        double ns = accum * 1e9 / (double)m;
        if (ns < best) best = ns;
    }
    return best;
}

/* ---------------- per-op accumulators ------------------------------- */

static const char* OP_NAMES[4] = { "push", "inject", "pop", "eject" };

typedef struct {
    double worst; char worst_label[64];
    double vals[512]; int nvals;
} opstat;
static opstat g_ops[4];

static int cmp_double(const void* a, const void* b) {
    double x = *(const double*)a, y = *(const double*)b;
    return (x < y) ? -1 : (x > y) ? 1 : 0;
}
static double median(double* xs, int n) {
    if (n == 0) return 0.0;
    qsort(xs, (size_t)n, sizeof(double), cmp_double);
    return (n & 1) ? xs[n / 2] : (xs[n / 2 - 1] + xs[n / 2]) / 2.0;
}

/* Build one state, time all four ops on it, record, then flush arena. */
static void probe(const char* label, kt_deque saved, long size, long m, int trials) {
    (void)size; /* all battery states are non-empty */
    for (int opc = 0; opc < 4; opc++) {
        double ns = time_op_ns(opc, &saved, m, trials);
        opstat* st = &g_ops[opc];
        if (ns > st->worst) { st->worst = ns; snprintf(st->worst_label, sizeof st->worst_label, "%s", label); }
        if (st->nvals < (int)(sizeof st->vals / sizeof st->vals[0])) st->vals[st->nvals++] = ns;
    }
    /* Discard this state: flush the §4 arena (0 roots) before the next. */
    kt_deque none = kt_empty();
    kt_arena_compact(&none, 0);
}

int main(int argc, char** argv) {
    long m = 80000; int trials = 7;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--m") && i + 1 < argc) m = strtol(argv[++i], NULL, 10);
        else if (!strcmp(argv[i], "--trials") && i + 1 < argc) trials = (int)strtol(argv[++i], NULL, 10);
        else { fprintf(stderr, "usage: %s [--m M] [--trials T]\n", argv[0]); return 2; }
    }
    for (int i = 0; i < 4; i++) { g_ops[i].worst = 0.0; g_ops[i].nvals = 0; }

    /* Warm allocator / ICache. */
    { long sz; kt_deque w = build_push(1000, &sz); kt_arena_compact(&w, 1);
      (void)time_op_ns(0, &w, 10000, 1);
      kt_deque none = kt_empty(); kt_arena_compact(&none, 0); }

    static const long sizes[] = { 7,15,31,63,127,255,511,1023,4095,16383,131071 };
    char label[64];
    for (size_t si = 0; si < sizeof sizes / sizeof sizes[0]; si++) {
        long n = sizes[si], sz;
        kt_deque d;
        d = build_push(n, &sz);   snprintf(label, sizeof label, "push^%ld", n);   probe(label, d, sz, m, trials);
        d = build_inject(n, &sz); snprintf(label, sizeof label, "inject^%ld", n); probe(label, d, sz, m, trials);
        d = build_alt(n, &sz);    snprintf(label, sizeof label, "alt^%ld", n);    probe(label, d, sz, m, trials);
        d = build_churn(n, &sz);  snprintf(label, sizeof label, "churn~%ld", n);  probe(label, d, sz, m, trials);
    }
    static const long rsizes[] = { 127, 4095, 131071 };
    for (size_t ri = 0; ri < sizeof rsizes / sizeof rsizes[0]; ri++) {
        for (unsigned seed = 1; seed <= 3; seed++) {
            long n = rsizes[ri], sz;
            kt_deque d = build_random(seed, n, &sz);
            snprintf(label, sizeof label, "rand%u~%ld", seed, n);
            probe(label, d, sz, m, trials);
        }
    }

    printf("| op | worst-case ns/op | median ns/op | worst-case state |\n");
    printf("|---|---:|---:|---|\n");
    for (int opc = 0; opc < 4; opc++) {
        opstat* st = &g_ops[opc];
        printf("| `%s` | %.1f | %.1f | %s |\n",
               OP_NAMES[opc], st->worst, median(st->vals, st->nvals), st->worst_label);
    }
    return 0;
}
