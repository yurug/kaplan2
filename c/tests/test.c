/* test.c — correctness tests against a list reference. */

#include "ktdeque.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

/* ---- Reference: a doubly-linked list ---- */
typedef struct ref_node {
    long val;
    struct ref_node* prev;
    struct ref_node* next;
} ref_node;

typedef struct {
    ref_node* head;
    ref_node* tail;
    int len;
} ref_deque;

static ref_deque ref_empty(void) { ref_deque r = {0}; return r; }

static void ref_push(ref_deque* r, long v) {
    ref_node* n = malloc(sizeof(*n));
    n->val = v; n->prev = NULL; n->next = r->head;
    if (r->head) r->head->prev = n;
    r->head = n;
    if (!r->tail) r->tail = n;
    r->len++;
}

static void ref_inject(ref_deque* r, long v) {
    ref_node* n = malloc(sizeof(*n));
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
    free(n);
    r->len--;
    return 1;
}

static int ref_eject(ref_deque* r, long* out) {
    if (!r->tail) return 0;
    *out = r->tail->val;
    ref_node* n = r->tail;
    r->tail = n->prev;
    if (r->tail) r->tail->next = NULL; else r->head = NULL;
    free(n);
    r->len--;
    return 1;
}

static void ref_destroy(ref_deque* r) {
    ref_node* n = r->head;
    while (n) {
        ref_node* next = n->next;
        free(n);
        n = next;
    }
    r->head = r->tail = NULL;
    r->len = 0;
}

/* ---- Compare deque against ref by walking front to back ---- */

typedef struct {
    long*  out;
    size_t idx;
} arr_ctx;

static void collect_cb(kt_elem e, void* ctx) {
    arr_ctx* a = (arr_ctx*)ctx;
    a->out[a->idx++] = *(long*)e;
}

static void kt_to_array(kt_deque d, long* out, size_t* idx) {
    arr_ctx a; a.out = out; a.idx = *idx;
    kt_walk(d, collect_cb, &a);
    *idx = a.idx;
}

static int compare(kt_deque d, ref_deque* r) {
    size_t kt_len = kt_length(d);
    if (kt_len != (size_t)r->len) {
        fprintf(stderr, "FAIL: lengths differ: kt=%zu, ref=%d\n", kt_len, r->len);
        return -1;
    }
    if (kt_len == 0) return 0;
    long* kt_arr = malloc(sizeof(long) * kt_len);
    size_t idx = 0;
    kt_to_array(d, kt_arr, &idx);
    if (idx != kt_len) {
        fprintf(stderr, "FAIL: extracted len mismatch: %zu vs %zu\n", idx, kt_len);
        free(kt_arr);
        return -2;
    }
    /* Walk ref from head and compare. */
    ref_node* n = r->head;
    for (size_t i = 0; i < kt_len; i++) {
        if (kt_arr[i] != n->val) {
            fprintf(stderr, "FAIL: mismatch at %zu: kt=%ld, ref=%ld\n",
                    i, kt_arr[i], n->val);
            free(kt_arr);
            return -3;
        }
        n = n->next;
    }
    free(kt_arr);
    return 0;
}

/* ---- Workloads ---- */

/* g_storage holds enough longs to back the deepest workload below.
 * test_region_isolation uses 2*n elements; max n we drive = 1,000,000. */
static long g_storage[3000000];

static int test_push_pop(int n) {
    kt_deque d = kt_empty();
    ref_deque r = ref_empty();
    for (int i = 0; i < n; i++) {
        g_storage[i] = i + 1;
        d = kt_push(kt_base(&g_storage[i]), d);
        ref_push(&r, i + 1);
        int rc = kt_check_regular(d);
        if (rc != 0) {
            fprintf(stderr, "test_push_pop: irregular at i=%d (rc=%d)\n", i, rc);
            return -1;
        }
        int dr = kt_check_diff_invariant(d);
        if (dr != 0) {
            fprintf(stderr, "test_push_pop: diff invariant at i=%d (rc=%d)\n", i, dr);
            return -1;
        }
    }
    if (compare(d, &r) != 0) return -2;
    /* Now pop them all. */
    for (int i = 0; i < n; i++) {
        kt_elem e; int ne;
        d = kt_pop(d, &e, &ne);
        if (!ne) {
            fprintf(stderr, "test_push_pop: pop empty at i=%d\n", i);
            return -3;
        }
        long ref;
        ref_pop(&r, &ref);
        long got = *(long*)e;
        if (got != ref) {
            fprintf(stderr, "test_push_pop: pop mismatch at i=%d: got %ld, ref %ld\n",
                    i, got, ref);
            return -4;
        }
    }
    if (d != NULL) {
        fprintf(stderr, "test_push_pop: deque not empty after %d pops\n", n);
        return -5;
    }
    return 0;
}

static int test_inject_eject(int n) {
    kt_deque d = kt_empty();
    ref_deque r = ref_empty();
    for (int i = 0; i < n; i++) {
        g_storage[i] = i + 1;
        d = kt_inject(d, kt_base(&g_storage[i]));
        ref_inject(&r, i + 1);
        int rc = kt_check_regular(d);
        if (rc != 0) {
            fprintf(stderr, "test_inject_eject: irregular at i=%d (rc=%d)\n", i, rc);
            return -1;
        }
        int dr = kt_check_diff_invariant(d);
        if (dr != 0) {
            fprintf(stderr, "test_inject_eject: diff invariant at i=%d (rc=%d)\n", i, dr);
            return -1;
        }
    }
    if (compare(d, &r) != 0) return -2;
    for (int i = 0; i < n; i++) {
        kt_elem e; int ne;
        d = kt_eject(d, &e, &ne);
        if (!ne) return -3;
        long ref;
        ref_eject(&r, &ref);
        if (*(long*)e != ref) return -4;
    }
    return 0;
}

static int test_mixed(int n, unsigned int seed) {
    srand(seed);
    kt_deque d = kt_empty();
    ref_deque r = ref_empty();
    int next_val = 0;
    for (int i = 0; i < n; i++) {
        int op = rand() % 4;
        switch (op) {
        case 0:
            g_storage[next_val] = next_val + 1;
            d = kt_push(kt_base(&g_storage[next_val]), d);
            ref_push(&r, next_val + 1);
            next_val++;
            break;
        case 1:
            g_storage[next_val] = next_val + 1;
            d = kt_inject(d, kt_base(&g_storage[next_val]));
            ref_inject(&r, next_val + 1);
            next_val++;
            break;
        case 2:
            if (r.len > 0) {
                kt_elem e; int ne;
                d = kt_pop(d, &e, &ne);
                if (!ne) return -1;
                long ref;
                ref_pop(&r, &ref);
                if (*(long*)e != ref) {
                    fprintf(stderr, "mixed: pop mismatch at i=%d\n", i);
                    return -2;
                }
            }
            break;
        case 3:
            if (r.len > 0) {
                kt_elem e; int ne;
                d = kt_eject(d, &e, &ne);
                if (!ne) return -3;
                long ref;
                ref_eject(&r, &ref);
                if (*(long*)e != ref) {
                    fprintf(stderr, "mixed: eject mismatch at i=%d\n", i);
                    return -4;
                }
            }
            break;
        }
        if (kt_check_regular(d) != 0) {
            fprintf(stderr, "mixed: irregular at i=%d (op=%d)\n", i, op);
            return -5;
        }
        if (kt_check_diff_invariant(d) != 0) {
            fprintf(stderr, "mixed: diff invariant at i=%d (op=%d)\n", i, op);
            return -7;
        }
    }
    if (compare(d, &r) != 0) { ref_destroy(&r); return -6; }
    ref_destroy(&r);
    return 0;
}

/* ---- Phase V region tests ---- */

/* Drive a region through n pushes then n pops, validating against a
 * reference deque.  After return, the region has been destroyed; any
 * deque value built in it is dangling and must not be used. */
static int test_region_push_pop(int n) {
    kt_region* reg = kt_region_create(0);
    if (reg == NULL) return -100;
    kt_deque d = kt_empty_in(reg);
    ref_deque r = ref_empty();
    for (int i = 0; i < n; i++) {
        g_storage[i] = i + 1;
        d = kt_push_in(reg, kt_base(&g_storage[i]), d);
        ref_push(&r, i + 1);
    }
    if (compare(d, &r) != 0) { kt_region_destroy(reg); return -1; }
    for (int i = 0; i < n; i++) {
        kt_elem e; int ne;
        d = kt_pop_in(reg, d, &e, &ne);
        if (!ne) { kt_region_destroy(reg); return -2; }
        long ref;
        ref_pop(&r, &ref);
        if (*(long*)e != ref) { kt_region_destroy(reg); return -3; }
    }
    if (d != NULL) { kt_region_destroy(reg); return -4; }
    /* Destroy the region: O(chunks); deque value `d` is now dangling
       (here it's NULL anyway). */
    kt_region_destroy(reg);
    return 0;
}

/* Two regions co-exist; ops on one don't disturb the other; destroy of
 * the first leaves the second functional. */
static int test_region_isolation(int n) {
    kt_region* r1 = kt_region_create(0);
    kt_region* r2 = kt_region_create(0);
    if (!r1 || !r2) return -100;
    kt_deque d1 = kt_empty_in(r1);
    kt_deque d2 = kt_empty_in(r2);
    ref_deque ref1 = ref_empty();
    ref_deque ref2 = ref_empty();
    for (int i = 0; i < n; i++) {
        g_storage[i]   = (long)(i + 1);
        g_storage[i+n] = (long)(i + 1) * 2;
        d1 = kt_push_in(r1, kt_base(&g_storage[i]),   d1);
        d2 = kt_inject_in(r2, d2, kt_base(&g_storage[i+n]));
        ref_push(&ref1, i + 1);
        ref_inject(&ref2, (i + 1) * 2);
    }
    if (compare(d1, &ref1) != 0) return -1;
    if (compare(d2, &ref2) != 0) return -2;
    /* Destroy r1.  d1 is now dangling — do not touch.  d2 / r2 should
       remain fully usable. */
    kt_region_destroy(r1);
    /* Drain d2 entirely. */
    for (int i = 0; i < n; i++) {
        kt_elem e; int ne;
        d2 = kt_eject_in(r2, d2, &e, &ne);
        if (!ne) { kt_region_destroy(r2); return -3; }
        long ref;
        ref_eject(&ref2, &ref);
        if (*(long*)e != ref) { kt_region_destroy(r2); return -4; }
    }
    kt_region_destroy(r2);
    ref_destroy(&ref1);  /* ref1 drains via r1's destroy semantically; free its nodes here. */
    return 0;
}

/* ---- Persistence / sharing test ----
 *
 * The deque is supposed to be persistent: holding a reference to a deque
 * value `d`, doing ops on `d` to produce `d'`, must not affect any
 * subsequent op done on `d` (which still represents the original
 * sequence).  This test forks a deque and validates both branches.
 */
static int test_persistence(int n) {
    kt_deque d = kt_empty();
    ref_deque r = ref_empty();
    /* Build initial deque with n elements. */
    for (int i = 0; i < n; i++) {
        g_storage[i] = i + 1;
        d = kt_push(kt_base(&g_storage[i]), d);
        ref_push(&r, i + 1);
    }
    /* Snapshot d as d_orig. */
    kt_deque d_orig = d;

    /* Build a SECOND ref representing what `d_orig` should look like
     * (same as `r` at this snapshot point). */
    ref_deque r_orig = ref_empty();
    for (int i = 0; i < n; i++) {
        g_storage[n + i] = i + 1;  /* duplicate values, separate storage. */
        ref_push(&r_orig, i + 1);
    }

    /* Branch A: pop n/2 from d_orig.  Must not affect d_orig itself. */
    kt_deque d_a = d_orig;
    for (int i = 0; i < n / 2; i++) {
        kt_elem e; int ne;
        d_a = kt_pop(d_a, &e, &ne);
        if (!ne) { ref_destroy(&r); ref_destroy(&r_orig); return -1; }
    }
    /* d_orig should still be the full original sequence. */
    if (compare(d_orig, &r_orig) != 0) {
        fprintf(stderr, "test_persistence: d_orig corrupted by branch A pops\n");
        ref_destroy(&r); ref_destroy(&r_orig); return -2;
    }

    /* Branch B: inject n/2 onto d_orig.  Must not affect d_orig itself. */
    kt_deque d_b = d_orig;
    for (int i = 0; i < n / 2; i++) {
        g_storage[2 * n + i] = -(i + 1);
        d_b = kt_inject(d_b, kt_base(&g_storage[2 * n + i]));
    }
    /* d_orig should still be the full original sequence. */
    if (compare(d_orig, &r_orig) != 0) {
        fprintf(stderr, "test_persistence: d_orig corrupted by branch B injects\n");
        ref_destroy(&r); ref_destroy(&r_orig); return -3;
    }

    /* Branch A should still hold the popped-by-half sequence. */
    {
        ref_deque r_a = ref_empty();
        for (int i = n/2; i < n; i++) ref_push(&r_a, i + 1);
        /* Reverse: ref_push prepends; we want the tail of the original.
         * The original was r = [n, n-1, ..., 1] (push prepends).
         * After n/2 pops from front, A = [n - n/2, ..., 1].  That's the
         * elements pushed at indices i=0..n/2-1, prepended in order,
         * i.e., final list = [n-n/2, n-n/2-1, ..., 1].
         * Easier: build the expected ref from scratch, mimicking the ops. */
        ref_destroy(&r_a);
        r_a = ref_empty();
        for (int i = 0; i < n; i++) ref_push(&r_a, i + 1);
        for (int i = 0; i < n / 2; i++) { long _v; ref_pop(&r_a, &_v); }
        if (compare(d_a, &r_a) != 0) {
            fprintf(stderr, "test_persistence: branch A diverged from expected\n");
            ref_destroy(&r); ref_destroy(&r_orig); ref_destroy(&r_a); return -4;
        }
        ref_destroy(&r_a);
    }

    /* Branch B should hold the original + n/2 injected at the back. */
    {
        ref_deque r_b = ref_empty();
        for (int i = 0; i < n; i++) ref_push(&r_b, i + 1);
        for (int i = 0; i < n / 2; i++) ref_inject(&r_b, -(i + 1));
        if (compare(d_b, &r_b) != 0) {
            fprintf(stderr, "test_persistence: branch B diverged from expected\n");
            ref_destroy(&r); ref_destroy(&r_orig); ref_destroy(&r_b); return -5;
        }
        ref_destroy(&r_b);
    }

    /* Final cross-check: d_orig is STILL the original sequence even after
     * both branches diverged. */
    if (compare(d_orig, &r_orig) != 0) {
        fprintf(stderr, "test_persistence: d_orig corrupted at final check\n");
        ref_destroy(&r); ref_destroy(&r_orig); return -6;
    }

    ref_destroy(&r);
    ref_destroy(&r_orig);
    return 0;
}

/* Build deque, compact mid-stream, continue ops, destroy. */
static int test_region_compact(int n) {
    kt_region* reg = kt_region_create(0);
    if (reg == NULL) return -100;
    kt_deque d = kt_empty_in(reg);
    ref_deque ref = ref_empty();
    for (int i = 0; i < n / 2; i++) {
        g_storage[i] = i + 1;
        d = kt_push_in(reg, kt_base(&g_storage[i]), d);
        ref_push(&ref, i + 1);
    }
    /* Mid-stream compaction (chain-link only).  Roots: the single live d. */
    (void)kt_region_compact(reg, &d, 1);
    if (compare(d, &ref) != 0) { kt_region_destroy(reg); return -1; }
    /* Continue: inject the rest. */
    for (int i = n / 2; i < n; i++) {
        g_storage[i] = i + 1;
        d = kt_inject_in(reg, d, kt_base(&g_storage[i]));
        ref_inject(&ref, i + 1);
    }
    /* Full compaction (chain-link + pair). */
    (void)kt_region_compact_full(reg, &d, 1);
    if (compare(d, &ref) != 0) { kt_region_destroy(reg); return -2; }
    /* Drain. */
    for (int i = 0; i < n; i++) {
        kt_elem e; int ne;
        d = kt_pop_in(reg, d, &e, &ne);
        if (!ne) { kt_region_destroy(reg); return -3; }
        long ref_v;
        ref_pop(&ref, &ref_v);
        if (*(long*)e != ref_v) { kt_region_destroy(reg); return -4; }
    }
    kt_region_destroy(reg);
    return 0;
}

int main(void) {
    int n;
    int rc;

    printf("=== test_push_pop ===\n");
    int sizes[] = {1, 2, 5, 10, 50, 100, 500, 1000, 10000, 100000, 1000000};
    int nsizes = sizeof(sizes)/sizeof(sizes[0]);
    for (int k = 0; k < nsizes; k++) {
        n = sizes[k];
        rc = test_push_pop(n);
        printf("  n=%-7d : %s\n", n, rc == 0 ? "OK" : "FAIL");
        if (rc != 0) return 1;
    }

    printf("\n=== test_inject_eject ===\n");
    for (int k = 0; k < nsizes; k++) {
        n = sizes[k];
        rc = test_inject_eject(n);
        printf("  n=%-7d : %s\n", n, rc == 0 ? "OK" : "FAIL");
        if (rc != 0) return 2;
    }

    printf("\n=== test_mixed ===\n");
    for (int k = 0; k < nsizes; k++) {
        n = sizes[k];
        rc = test_mixed(n, 42 + k);
        printf("  n=%-7d : %s\n", n, rc == 0 ? "OK" : "FAIL");
        if (rc != 0) return 3;
    }

    printf("\n=== test_persistence ===\n");
    for (int k = 0; k < nsizes; k++) {
        n = sizes[k];
        rc = test_persistence(n);
        printf("  n=%-7d : %s\n", n, rc == 0 ? "OK" : "FAIL");
        if (rc != 0) return 7;
    }

    printf("\n=== test_region_push_pop ===\n");
    for (int k = 0; k < nsizes; k++) {
        n = sizes[k];
        rc = test_region_push_pop(n);
        printf("  n=%-7d : %s\n", n, rc == 0 ? "OK" : "FAIL");
        if (rc != 0) return 4;
    }

    printf("\n=== test_region_isolation ===\n");
    for (int k = 0; k < nsizes; k++) {
        n = sizes[k];
        rc = test_region_isolation(n);
        printf("  n=%-7d : %s\n", n, rc == 0 ? "OK" : "FAIL");
        if (rc != 0) return 5;
    }

    printf("\n=== test_region_compact ===\n");
    for (int k = 0; k < nsizes; k++) {
        n = sizes[k];
        rc = test_region_compact(n);
        printf("  n=%-7d : %s\n", n, rc == 0 ? "OK" : "FAIL");
        if (rc != 0) return 6;
    }

    printf("\nAll tests passed.\n");
    return 0;
}
