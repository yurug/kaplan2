/* diff_workload.c — emit a deterministic workload + final sequence as text.
 *
 * The companion OCaml driver (ocaml/extracted/diff_workload.ml) generates
 * the SAME workload (same xorshift64 seed/sequence) and emits its final
 * sequence.  `diff` the two outputs to detect any divergence between
 * the C and the Coq-extracted OCaml implementations.
 *
 * Output format:
 *   - One line per push/inject/pop/eject op showing the op and the
 *     resulting deque length.
 *   - Final block "FINAL [N]: v1,v2,...,vN".
 *
 * Args:  ./diff_workload [N] [SEED_HEX] [MODE]
 *   N         — operation count (default 10000)
 *   SEED_HEX  — 64-bit xorshift seed, hex with or without 0x (default
 *               0x123456789abcdef0)
 *   MODE      — workload generator:
 *                 "mix"  — uniform random push/inject/pop/eject (default).
 *                 "deep" — 4 monotonic phases of N/4 ops each
 *                          (push, inject, pop, eject) which drives the
 *                          deque to depth Θ(log₂(N/4)) on the
 *                          push/inject phase, then exercises the deepest
 *                          green→red cascades on the drain phase.  This
 *                          is the workload class the KT99 worst-case
 *                          analysis is about; see the C/OCaml
 *                          equivalence report at
 *                          https://github.com/yurug/kaplan2/blob/main/kb/reports/c-ocaml-equivalence.md
 *                          for why this layer matters.
 */
#include "ktdeque.h"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

extern int kt_check_regular(kt_deque);

/* xorshift64: simple deterministic PRNG. */
static uint64_t xorshift_state;
static uint64_t xorshift_next(void) {
    uint64_t x = xorshift_state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    xorshift_state = x;
    return x;
}

/* Op encoding: 0=push, 1=inject, 2=pop, 3=eject. */
static int next_op_mix(void) { return (int)(xorshift_next() % 4); }

/* deep-mode op for step i out of n (4 monotonic phases of n/4). */
static int next_op_deep(int i, int n) {
    int q = n / 4;
    if (i < q)         return 0;   /* push */
    if (i < 2 * q)     return 1;   /* inject */
    if (i < 3 * q)     return 2;   /* pop */
    return 3;                       /* eject (or no-op if drained) */
}

static long g_storage[10000000];

typedef struct { long* out; size_t idx; } arr_ctx;
static void collect_cb(kt_elem e, void* ctx) {
    arr_ctx* a = (arr_ctx*)ctx;
    a->out[a->idx++] = *(long*)e;
}

int main(int argc, char** argv) {
    int n = (argc > 1) ? atoi(argv[1]) : 10000;
    /* Seed: accept "0xDEADBEEF" or "DEADBEEF" hex. */
    uint64_t seed = 0x123456789abcdef0ULL;
    if (argc > 2) {
        const char* s = argv[2];
        if (s[0] == '0' && (s[1] == 'x' || s[1] == 'X')) s += 2;
        seed = strtoull(s, NULL, 16);
    }
    /* Workload mode. */
    const char* mode = (argc > 3) ? argv[3] : "mix";
    int deep = (strcmp(mode, "deep") == 0);
    if (!deep && strcmp(mode, "mix") != 0) {
        fprintf(stderr, "diff_workload: unknown mode '%s' (use 'mix' or 'deep')\n", mode);
        return 2;
    }

    /* Bound N for storage safety: g_storage holds 10M longs. */
    if (n < 0 || n > 10000000) {
        fprintf(stderr, "diff_workload: N=%d out of range [0, 10000000]\n", n);
        return 2;
    }

    xorshift_state = seed;

    kt_deque d = kt_empty();
    /* Track length as a counter (mirroring the OCaml side).  kt_length()
     * could be O(n) on some chain shapes; at n=400k deep this matters.
     * Both sides agree on what each op does to the length, so the printed
     * `len=` field is still a discriminating signal — and the FINAL-line
     * walk catches any mismatch between the counter and the real deque. */
    long len = 0;
    int next_val = 1;
    long* storage_idx_to_val = g_storage;

    for (int i = 0; i < n; i++) {
        int op = deep ? next_op_deep(i, n) : next_op_mix();
        if (deep) (void)xorshift_next();  /* consume in lockstep with OCaml */

        switch (op) {
        case 0:
            storage_idx_to_val[next_val - 1] = next_val;
            d = kt_push(kt_base(&storage_idx_to_val[next_val - 1]), d);
            len++;
            printf("push %d -> len=%ld\n", next_val, len);
            next_val++;
            break;
        case 1:
            storage_idx_to_val[next_val - 1] = next_val;
            d = kt_inject(d, kt_base(&storage_idx_to_val[next_val - 1]));
            len++;
            printf("inject %d -> len=%ld\n", next_val, len);
            next_val++;
            break;
        case 2: {
            kt_elem e; int ne;
            d = kt_pop(d, &e, &ne);
            if (ne) { len--; printf("pop %ld -> len=%ld\n", *(long*)e, len); }
            else    printf("pop NONE -> len=0\n");
            break;
        }
        case 3: {
            kt_elem e; int ne;
            d = kt_eject(d, &e, &ne);
            if (ne) { len--; printf("eject %ld -> len=%ld\n", *(long*)e, len); }
            else    printf("eject NONE -> len=0\n");
            break;
        }
        }
        if (kt_check_regular(d) != 0) {
            fprintf(stderr, "i=%d: irregular!\n", i);
            return 1;
        }
    }

    /* Final sequence: walk the deque front-to-back.  Use the real
     * kt_length here (not the counter) so we cross-check the counter
     * against the actual structure: if they ever disagree, FINAL-line
     * length misprints relative to OCaml's List.length and the diff
     * fails. */
    size_t real_len = kt_length(d);
    long* arr = (long*)malloc(sizeof(long) * (real_len ? real_len : 1));
    arr_ctx a = { arr, 0 };
    kt_walk(d, collect_cb, &a);
    printf("FINAL %zu:", real_len);
    for (size_t i = 0; i < real_len; i++) {
        printf(" %ld", arr[i]);
    }
    printf("\n");
    free(arr);
    return 0;
}
