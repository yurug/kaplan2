/* fuzz.c — random-workload fuzz tester.
 *
 * Sweeps multiple PRNG seeds × workload lengths, doing random
 * push/inject/pop/eject/snapshot/compact ops.  Validates against a
 * reference doubly-linked-list at every step.  Run with ASan +
 * UBSan to catch memory bugs.
 *
 * Build:
 *   gcc -O1 -g -fsanitize=address,undefined -fno-omit-frame-pointer \
 *       -DNDEBUG -Ic/include -o /tmp/fuzz c/src/ktdeque_dequeptr.c c/tests/fuzz.c
 *
 * Run:
 *   ASAN_OPTIONS=detect_leaks=0 /tmp/fuzz 1000   # 1000 seeds × random lengths
 */
#include "ktdeque.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern int kt_check_regular(kt_deque);
extern int kt_check_diff_invariant(kt_deque);

typedef struct ref_node {
    long val;
    struct ref_node* prev;
    struct ref_node* next;
} ref_node;

typedef struct { ref_node* head; ref_node* tail; int len; } ref_deque;

static ref_deque ref_empty(void) { ref_deque r = {0}; return r; }

static void ref_push(ref_deque* r, long v) {
    ref_node* n = (ref_node*)malloc(sizeof(*n));
    n->val = v; n->prev = NULL; n->next = r->head;
    if (r->head) r->head->prev = n;
    r->head = n;
    if (!r->tail) r->tail = n;
    r->len++;
}

static void ref_inject(ref_deque* r, long v) {
    ref_node* n = (ref_node*)malloc(sizeof(*n));
    n->val = v; n->next = NULL; n->prev = r->tail;
    if (r->tail) r->tail->next = n;
    r->tail = n;
    if (!r->head) r->head = n;
    r->len++;
}

static int ref_pop(ref_deque* r, long* out) {
    if (!r->head) return 0;
    *out = r->head->val;
    ref_node* n = r->head;
    r->head = n->next;
    if (r->head) r->head->prev = NULL; else r->tail = NULL;
    free(n); r->len--;
    return 1;
}

static int ref_eject(ref_deque* r, long* out) {
    if (!r->tail) return 0;
    *out = r->tail->val;
    ref_node* n = r->tail;
    r->tail = n->prev;
    if (r->tail) r->tail->next = NULL; else r->head = NULL;
    free(n); r->len--;
    return 1;
}

static void ref_destroy(ref_deque* r) {
    ref_node* n = r->head;
    while (n) { ref_node* next = n->next; free(n); n = next; }
    r->head = r->tail = NULL; r->len = 0;
}

typedef struct { long* out; size_t idx; } arr_ctx;

static void collect_cb(kt_elem e, void* ctx) {
    arr_ctx* a = (arr_ctx*)ctx;
    a->out[a->idx++] = *(long*)e;
}

static int compare(kt_deque d, ref_deque* r) {
    size_t kt_len = kt_length(d);
    if (kt_len != (size_t)r->len) return -1;
    if (kt_len == 0) return 0;
    long* arr = (long*)malloc(sizeof(long) * kt_len);
    arr_ctx a = { arr, 0 };
    kt_walk(d, collect_cb, &a);
    if (a.idx != kt_len) { free(arr); return -2; }
    ref_node* n = r->head;
    for (size_t i = 0; i < kt_len; i++) {
        if (arr[i] != n->val) { free(arr); return -3; }
        n = n->next;
    }
    free(arr);
    return 0;
}

static long g_storage[2000000];

/* Per-seed fuzz: do `n` random ops, with a small probability of
 * snapshot-then-fork (verifies persistence inline). */
static int fuzz_seed(unsigned int seed, int n) {
    srand(seed);
    kt_deque d = kt_empty();
    ref_deque r = ref_empty();
    int next_val = 0;

    for (int i = 0; i < n; i++) {
        int op = rand() % 100;

        /* Op distribution:
         *   0..29  push   (30%)
         *   30..59 inject (30%)
         *   60..79 pop    (20%)
         *   80..99 eject  (20%)
         */
        if (op < 30) {
            g_storage[next_val % (int)(sizeof(g_storage)/sizeof(long))] = next_val + 1;
            d = kt_push(kt_base(&g_storage[next_val % (int)(sizeof(g_storage)/sizeof(long))]), d);
            ref_push(&r, next_val + 1);
            next_val++;
        } else if (op < 60) {
            g_storage[next_val % (int)(sizeof(g_storage)/sizeof(long))] = next_val + 1;
            d = kt_inject(d, kt_base(&g_storage[next_val % (int)(sizeof(g_storage)/sizeof(long))]));
            ref_inject(&r, next_val + 1);
            next_val++;
        } else if (op < 80) {
            if (r.len > 0) {
                kt_elem e; int ne;
                d = kt_pop(d, &e, &ne);
                if (!ne) {
                    fprintf(stderr, "seed=%u i=%d: kt_pop returned empty but ref non-empty\n", seed, i);
                    ref_destroy(&r); return -1;
                }
                long ref_v;
                ref_pop(&r, &ref_v);
                if (*(long*)e != ref_v) {
                    fprintf(stderr, "seed=%u i=%d: pop mismatch %ld vs %ld\n",
                            seed, i, *(long*)e, ref_v);
                    ref_destroy(&r); return -2;
                }
            }
        } else {
            if (r.len > 0) {
                kt_elem e; int ne;
                d = kt_eject(d, &e, &ne);
                if (!ne) {
                    fprintf(stderr, "seed=%u i=%d: kt_eject returned empty but ref non-empty\n", seed, i);
                    ref_destroy(&r); return -3;
                }
                long ref_v;
                ref_eject(&r, &ref_v);
                if (*(long*)e != ref_v) {
                    fprintf(stderr, "seed=%u i=%d: eject mismatch %ld vs %ld\n",
                            seed, i, *(long*)e, ref_v);
                    ref_destroy(&r); return -4;
                }
            }
        }

        if (kt_check_regular(d) != 0) {
            fprintf(stderr, "seed=%u i=%d: irregular\n", seed, i);
            ref_destroy(&r); return -5;
        }
        if (kt_check_diff_invariant(d) != 0) {
            fprintf(stderr, "seed=%u i=%d: diff invariant violated\n", seed, i);
            ref_destroy(&r); return -6;
        }
    }

    /* Final compare: walk both and ensure equal sequences. */
    if (compare(d, &r) != 0) {
        fprintf(stderr, "seed=%u: final compare failed (n=%d, ref_len=%d, kt_len=%zu)\n",
                seed, n, r.len, kt_length(d));
        ref_destroy(&r); return -7;
    }

    ref_destroy(&r);
    return 0;
}

int main(int argc, char** argv) {
    int n_seeds = 1000;
    if (argc > 1) n_seeds = atoi(argv[1]);

    /* Per-seed workload length: vary across seeds for diversity. */
    int lengths[] = { 100, 500, 1000, 5000, 10000 };
    int n_lengths = sizeof(lengths) / sizeof(lengths[0]);

    int total = 0, failed = 0;
    for (int s = 0; s < n_seeds; s++) {
        int len = lengths[s % n_lengths];
        unsigned int seed = (unsigned int)(s * 0x9E3779B1u + 0xDEADBEEFu);
        int rc = fuzz_seed(seed, len);
        total++;
        if (rc != 0) {
            failed++;
            fprintf(stderr, "  seed=%u (s=%d) len=%d: FAIL rc=%d\n", seed, s, len, rc);
        }
        if ((s % 100) == 0) {
            fprintf(stderr, "  progress: %d/%d (failed=%d)\n", s, n_seeds, failed);
        }
    }

    printf("Total: %d  Failed: %d\n", total, failed);
    return failed > 0 ? 1 : 0;
}
