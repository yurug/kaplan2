/* diff_cadeque.c — deterministic CATENABLE workload + per-slot sequences.
 *
 * The companion OCaml driver (ocaml/bench/diff_cadeque.ml) generates the
 * SAME workload (same xorshift64 seed/sequence, same op decoding) against
 * the Coq-extracted KTFlatCadeque, and emits the same text.  `diff` the
 * two outputs to detect any divergence between the C catenable port and
 * the verified OCaml artifact.
 *
 * Workload: K register slots, each a persistent cadeque.  Each step the
 * PRNG picks an op and slot(s):
 *   0 push   ctr -> slot i        1 inject slot i <- ctr
 *   2 pop    slot i               3 eject  slot i
 *   4 concat slot i := i ++ j ;  if i!=j then slot j := empty
 * Values are a monotone counter so order is checkable.  Both drivers call
 * the PRNG the same number of times in the same order.
 *
 * Output: one line per slot, "SLOT i [n]: v1,v2,...", the slot drained
 * front-to-back via kc_pop (so the emission itself exercises pop), then
 * "DONE total=T".
 *
 * Args: ./diff_cadeque [N] [SEED_HEX] [K]
 */
#include "ktcadeque.h"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

static uint64_t xs;
static uint64_t xnext(void) {
    uint64_t x = xs;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    xs = x; return x;
}

int main(int argc, char** argv) {
    long N = argc > 1 ? atol(argv[1]) : 100000;
    xs     = argc > 2 ? strtoull(argv[2], NULL, 16) : 0x123456789abcdef0ULL;
    int K  = argc > 3 ? atoi(argv[3]) : 8;
    if (K < 2) K = 2;

    kc_cadeque* slot = malloc((size_t)K * sizeof(kc_cadeque));
    for (int i = 0; i < K; i++) slot[i] = kc_empty();

    long ctr = 1;
    for (long step = 0; step < N; step++) {
        int op = (int)(xnext() % 5);
        int i  = (int)(xnext() % (uint64_t)K);
        switch (op) {
            case 0: slot[i] = kc_push((kt_elem)(intptr_t)(ctr++), slot[i]); break;
            case 1: slot[i] = kc_inject(slot[i], (kt_elem)(intptr_t)(ctr++)); break;
            case 2: { kt_elem e; int ok; slot[i] = kc_pop(slot[i], &e, &ok); break; }
            case 3: { kt_elem e; int ok; slot[i] = kc_eject(slot[i], &e, &ok); break; }
            case 4: {
#ifdef KC_COMPACT_EVERY
                if ((step % KC_COMPACT_EVERY) == 0) kc_arena_compact(slot, K);
#endif
                /* j != i: self-concat would double the sequence length
                 * (exponential blow-up over many steps) — exclude it so the
                 * workload stays linear-sized.  One PRNG draw, K-1 choices. */
                int j = (i + 1 + (int)(xnext() % (uint64_t)(K - 1))) % K;
                slot[i] = kc_concat(slot[i], slot[j]);
                slot[j] = kc_empty();
                break;
            }
        }
    }

    long total = 0;
    for (int i = 0; i < K; i++) {
        size_t n = kc_length(slot[i]);
        printf("SLOT %d [%zu]:", i, n);
        kc_cadeque d = slot[i];
        for (;;) {
            kt_elem e; int ok;
            d = kc_pop(d, &e, &ok);
            if (!ok) break;
            printf(" %ld", (long)(intptr_t)e);
            total++;
        }
        printf("\n");
    }
    printf("DONE total=%ld\n", total);
    free(slot);
    return 0;
}
