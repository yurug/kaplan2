/* test_persistence_stress.c — adversarial multi-branch persistence test.
 *
 * The simple test_persistence in test.c forks the deque exactly once and
 * checks the original is unaffected.  That covers the basic COW
 * invariant but does not stress the shared-internal-cells case the
 * report calls out (point G of the C/OCaml equivalence report at
 * https://github.com/yurug/kaplan2/blob/main/kb/reports/c-ocaml-equivalence.md ).
 *
 * This stress test:
 *   1. Builds a "trunk" of N snapshots S[0..N], where S[i+1] = inject S[i] v_i.
 *      Every snapshot shares internal cells with its predecessors.
 *   2. For each snapshot S[i], runs K random operations on it.  These
 *      operations must NOT mutate any S[j] (j ≠ i) — that's the
 *      persistence guarantee.
 *   3. After all branches diverge, walks every S[i] AGAIN and checks
 *      its sequence still equals the trunk reference at index i.
 *   4. Repeats with a different fork pattern: pick a random S[i], fork
 *      it B times, apply distinct op sequences to each fork, validate
 *      no fork affects S[i] or any other fork.
 *
 * If the C ever did an in-place mutation that violated COW under shared
 * cells (e.g. a pair-block that two branches reach), this test would
 * detect it: the trunk references would diverge from their snapshots
 * after branches were exercised.
 */
#include "ktdeque.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern int kt_check_regular(kt_deque);

static long g_storage[10000000];
static long g_used = 0;

static long* alloc_val(long v) {
    long* p = &g_storage[g_used++];
    *p = v;
    return p;
}

/* Reference deque: doubly-linked list. */
typedef struct ref_node {
    long val;
    struct ref_node* prev;
    struct ref_node* next;
} ref_node;

typedef struct { ref_node* head; ref_node* tail; int len; } ref_deque;

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
    memset(r, 0, sizeof(*r));
}
static void ref_copy(ref_deque* dst, const ref_deque* src) {
    dst->head = dst->tail = NULL; dst->len = 0;
    for (ref_node* n = src->head; n; n = n->next) ref_inject(dst, n->val);
}

/* Compare a kt_deque to a ref_deque (front-to-back). */
typedef struct { long* arr; size_t idx, cap; } walk_ctx;
static void walk_cb(kt_elem e, void* ctx) {
    walk_ctx* w = (walk_ctx*)ctx;
    if (w->idx < w->cap) w->arr[w->idx] = *(long*)e;
    w->idx++;
}
static int compare_d(kt_deque d, const ref_deque* r) {
    size_t kt_len = kt_length(d);
    if ((int)kt_len != r->len) {
        fprintf(stderr, "  length mismatch: kt=%zu ref=%d\n", kt_len, r->len);
        return -1;
    }
    if (kt_len == 0) return 0;
    long* arr = (long*)malloc(sizeof(long) * kt_len);
    walk_ctx w = { arr, 0, kt_len };
    kt_walk(d, walk_cb, &w);
    int rc = 0;
    ref_node* n = r->head;
    for (size_t i = 0; i < kt_len; i++, n = n->next) {
        if (arr[i] != n->val) {
            fprintf(stderr, "  mismatch at %zu: kt=%ld ref=%ld\n", i, arr[i], n->val);
            rc = -2; break;
        }
    }
    free(arr);
    return rc;
}

/* Apply K xorshift-driven ops to (d, r) in lockstep.  Returns mutated. */
static uint64_t xs_state;
static uint64_t xs_next(void) {
    uint64_t x = xs_state;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    xs_state = x; return x;
}
static kt_deque apply_ops(kt_deque d, ref_deque* r, int k, long base_val) {
    for (int i = 0; i < k; i++) {
        int op = (int)(xs_next() % 4);
        long v = base_val + i;
        switch (op) {
            case 0:
                d = kt_push(kt_base(alloc_val(v)), d);
                ref_push(r, v); break;
            case 1:
                d = kt_inject(d, kt_base(alloc_val(v)));
                ref_inject(r, v); break;
            case 2: {
                kt_elem e; int ne; long ref_v;
                d = kt_pop(d, &e, &ne);
                int rne = ref_pop(r, &ref_v);
                if (ne != rne) { fprintf(stderr, "  pop ne mismatch\n"); return d; }
                if (ne && *(long*)e != ref_v) {
                    fprintf(stderr, "  pop val mismatch %ld vs %ld\n", *(long*)e, ref_v);
                    return d;
                }
                break;
            }
            case 3: {
                kt_elem e; int ne; long ref_v;
                d = kt_eject(d, &e, &ne);
                int rne = ref_eject(r, &ref_v);
                if (ne != rne) { fprintf(stderr, "  eject ne mismatch\n"); return d; }
                if (ne && *(long*)e != ref_v) {
                    fprintf(stderr, "  eject val mismatch %ld vs %ld\n", *(long*)e, ref_v);
                    return d;
                }
                break;
            }
        }
    }
    return d;
}

/* Phase 1: build a trunk of N snapshots with maximum sharing.  Each
 * S[i+1] is derived from S[i] by injecting i+1.  Then fork EACH S[i]
 * with K random ops, validate the fork, then re-validate every S[j]
 * (j != i) is still the trunk reference. */
static int test_trunk(int n, int k) {
    printf("  trunk: n=%d snapshots, k=%d ops/fork\n", n, k);
    kt_deque* trunk_d = (kt_deque*)calloc(n + 1, sizeof(kt_deque));
    ref_deque* trunk_r = (ref_deque*)calloc(n + 1, sizeof(ref_deque));
    trunk_d[0] = kt_empty();
    for (int i = 0; i < n; i++) {
        long v = i + 1;
        trunk_d[i + 1] = kt_inject(trunk_d[i], kt_base(alloc_val(v)));
        ref_copy(&trunk_r[i + 1], &trunk_r[i]);
        ref_inject(&trunk_r[i + 1], v);
    }
    /* Initial sanity: every snapshot equals its trunk reference. */
    for (int i = 0; i <= n; i++) {
        if (compare_d(trunk_d[i], &trunk_r[i]) != 0) {
            fprintf(stderr, "  initial trunk[%d] mismatch\n", i);
            return -1;
        }
    }
    /* Fork each S[i] independently and validate. */
    long base = 1000000;
    for (int i = 0; i <= n; i++) {
        ref_deque rfork; ref_copy(&rfork, &trunk_r[i]);
        kt_deque dfork = trunk_d[i];
        dfork = apply_ops(dfork, &rfork, k, base);
        base += k;
        (void)dfork; /* fork value not preserved across iters */
        if (compare_d(dfork, &rfork) != 0) {
            fprintf(stderr, "  forked S[%d] diverged from per-fork ref\n", i);
            ref_destroy(&rfork);
            return -2;
        }
        ref_destroy(&rfork);
    }
    /* CRITICAL: every original S[j] must STILL equal trunk_r[j].  If any
     * fork above mutated shared internal cells, this would diverge. */
    for (int i = 0; i <= n; i++) {
        if (compare_d(trunk_d[i], &trunk_r[i]) != 0) {
            fprintf(stderr, "  POST-FORK trunk[%d] CORRUPTED!\n", i);
            return -3;
        }
        if (kt_check_regular(trunk_d[i]) != 0) {
            fprintf(stderr, "  POST-FORK trunk[%d] irregular\n", i);
            return -4;
        }
    }
    /* Cleanup. */
    for (int i = 0; i <= n; i++) ref_destroy(&trunk_r[i]);
    free(trunk_d); free(trunk_r);
    return 0;
}

/* Phase 2: pick one trunk node, fork B branches off it, apply distinct
 * op sequences to each, validate every branch and that the source is
 * unaffected.  This is the densest sharing pattern (B branches all
 * referring to the same internal cells). */
static int test_starburst(int trunk_n, int branches, int k_per_branch) {
    printf("  starburst: trunk_n=%d, branches=%d, k=%d ops/branch\n",
           trunk_n, branches, k_per_branch);
    /* Build a single deque with trunk_n elements. */
    kt_deque src = kt_empty();
    ref_deque src_r = {0};
    for (int i = 0; i < trunk_n; i++) {
        long v = i + 1;
        src = kt_inject(src, kt_base(alloc_val(v)));
        ref_inject(&src_r, v);
    }
    /* Snapshot src for the post-fork comparison. */
    kt_deque src_snap = src;
    ref_deque src_snap_r; ref_copy(&src_snap_r, &src_r);

    /* Fork B branches, each with its own ref. */
    kt_deque*  branch_d = (kt_deque*) calloc(branches, sizeof(kt_deque));
    ref_deque* branch_r = (ref_deque*)calloc(branches, sizeof(ref_deque));
    long base = 5000000;
    for (int b = 0; b < branches; b++) {
        ref_copy(&branch_r[b], &src_r);
        branch_d[b] = src;
        branch_d[b] = apply_ops(branch_d[b], &branch_r[b], k_per_branch, base);
        base += k_per_branch;
    }
    /* Validate every branch matches its own ref. */
    for (int b = 0; b < branches; b++) {
        if (compare_d(branch_d[b], &branch_r[b]) != 0) {
            fprintf(stderr, "  branch[%d] diverged from per-branch ref\n", b);
            return -10;
        }
        if (kt_check_regular(branch_d[b]) != 0) {
            fprintf(stderr, "  branch[%d] irregular\n", b);
            return -11;
        }
    }
    /* Validate the source is STILL the original. */
    if (compare_d(src_snap, &src_snap_r) != 0) {
        fprintf(stderr, "  POST-STARBURST src corrupted\n");
        return -12;
    }
    /* Cleanup. */
    for (int b = 0; b < branches; b++) ref_destroy(&branch_r[b]);
    free(branch_d); free(branch_r);
    ref_destroy(&src_r); ref_destroy(&src_snap_r);
    return 0;
}

int main(int argc, char** argv) {
    int n  = (argc > 1) ? atoi(argv[1]) : 200;
    int k  = (argc > 2) ? atoi(argv[2]) : 100;
    int br = (argc > 3) ? atoi(argv[3]) : 64;
    uint64_t seed = (argc > 4) ? strtoull(argv[4], NULL, 0) : 0xCAFEBABE12345678ULL;
    xs_state = seed;
    printf("=== test_persistence_stress ===\n");
    printf("  seed=0x%016lx\n", (unsigned long)seed);
    int rc;
    rc = test_trunk(n, k);
    if (rc != 0) { fprintf(stderr, "trunk: rc=%d\n", rc); return 1; }
    rc = test_starburst(n, br, k);
    if (rc != 0) { fprintf(stderr, "starburst: rc=%d\n", rc); return 1; }
    printf("  PASS: %d trunk snapshots × %d branches all preserved\n", n, br);
    return 0;
}
