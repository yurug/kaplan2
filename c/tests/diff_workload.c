/* diff_workload.c — emit a deterministic workload + final sequence as text.
 *
 * The companion OCaml driver (ocaml/test/diff_workload.ml) generates the
 * SAME workload (same xorshift64 seed/sequence) and emits its final
 * sequence.  `diff` the two outputs to detect any divergence between
 * the C and the Coq-extracted OCaml implementations.
 *
 * Output format:
 *   - One line per push/inject/pop/eject op showing the op and the
 *     resulting deque length.
 *   - Final block "FINAL [N]: v1,v2,...,vN".
 *
 * Workload size is the first arg (default 10000).
 */
#include "ktdeque.h"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

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
static int next_op(void) { return (int)(xorshift_next() % 4); }

static long g_storage[10000000];

typedef struct { long* out; size_t idx; } arr_ctx;
static void collect_cb(kt_elem e, void* ctx) {
    arr_ctx* a = (arr_ctx*)ctx;
    a->out[a->idx++] = *(long*)e;
}

int main(int argc, char** argv) {
    int n = (argc > 1) ? atoi(argv[1]) : 10000;
    xorshift_state = 0x123456789abcdef0ULL;

    kt_deque d = kt_empty();
    int next_val = 1;
    long* storage_idx_to_val = g_storage;

    for (int i = 0; i < n; i++) {
        int op = next_op();
        switch (op) {
        case 0:
            storage_idx_to_val[next_val - 1] = next_val;
            d = kt_push(kt_base(&storage_idx_to_val[next_val - 1]), d);
            printf("push %d -> len=%zu\n", next_val, kt_length(d));
            next_val++;
            break;
        case 1:
            storage_idx_to_val[next_val - 1] = next_val;
            d = kt_inject(d, kt_base(&storage_idx_to_val[next_val - 1]));
            printf("inject %d -> len=%zu\n", next_val, kt_length(d));
            next_val++;
            break;
        case 2: {
            kt_elem e; int ne;
            d = kt_pop(d, &e, &ne);
            if (ne) printf("pop %ld -> len=%zu\n", *(long*)e, kt_length(d));
            else    printf("pop NONE -> len=0\n");
            break;
        }
        case 3: {
            kt_elem e; int ne;
            d = kt_eject(d, &e, &ne);
            if (ne) printf("eject %ld -> len=%zu\n", *(long*)e, kt_length(d));
            else    printf("eject NONE -> len=0\n");
            break;
        }
        }
        if (kt_check_regular(d) != 0) {
            fprintf(stderr, "i=%d: irregular!\n", i);
            return 1;
        }
    }

    /* Final sequence: walk the deque front-to-back. */
    size_t len = kt_length(d);
    long* arr = (long*)malloc(sizeof(long) * (len ? len : 1));
    arr_ctx a = { arr, 0 };
    kt_walk(d, collect_cb, &a);
    printf("FINAL %zu:", len);
    for (size_t i = 0; i < len; i++) {
        printf(" %ld", arr[i]);
    }
    printf("\n");
    free(arr);
    return 0;
}
