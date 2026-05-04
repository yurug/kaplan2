/* test_fallback_trace.c - Phase S audit closure (F2):
 *
 * Builds with -DKT_TRACE_FALLBACK to count the kt_pop/kt_eject side
 * fallback branches identified in audit-phase5-spec-compliance.md F2.
 * After running the test corpus at all standard sizes (1..100k), prints
 * the cumulative fallback counts.  If both are zero, the fallback
 * branches are dead code per the test corpus.
 */

#include "ktdeque.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Forward declarations of counter accessors (only present when
 * KT_TRACE_FALLBACK is defined when compiling ktdeque_dequeptr.c). */
size_t kt_fallback_pop_suf(void);
size_t kt_fallback_eject_pre(void);
void   kt_reset_fallback_counters(void);

/* ---- Doubly-linked-list reference (copied from test.c, tightened). ---- */
typedef struct ref_node {
    long val;
    struct ref_node* prev;
    struct ref_node* next;
} ref_node;

typedef struct {
    ref_node* head;
    ref_node* tail;
    size_t len;
} ref_t;

static void ref_push(ref_t* r, long v) {
    ref_node* n = malloc(sizeof(*n));
    n->val = v; n->prev = NULL; n->next = r->head;
    if (r->head) r->head->prev = n; else r->tail = n;
    r->head = n;
    r->len++;
}
static void ref_inject(ref_t* r, long v) {
    ref_node* n = malloc(sizeof(*n));
    n->val = v; n->next = NULL; n->prev = r->tail;
    if (r->tail) r->tail->next = n; else r->head = n;
    r->tail = n;
    r->len++;
}
static int ref_pop(ref_t* r, long* out) {
    if (!r->head) return 0;
    ref_node* n = r->head;
    *out = n->val;
    r->head = n->next;
    if (r->head) r->head->prev = NULL; else r->tail = NULL;
    free(n);
    r->len--;
    return 1;
}
static int ref_eject(ref_t* r, long* out) {
    if (!r->tail) return 0;
    ref_node* n = r->tail;
    *out = n->val;
    r->tail = n->prev;
    if (r->tail) r->tail->next = NULL; else r->head = NULL;
    free(n);
    r->len--;
    return 1;
}
static void ref_destroy(ref_t* r) {
    ref_node* n = r->head;
    while (n) { ref_node* nx = n->next; free(n); n = nx; }
    r->head = r->tail = NULL; r->len = 0;
}

static int run_push_pop(int n) {
    kt_deque d = kt_empty();
    ref_t r = {0};
    for (int i = 0; i < n; i++) {
        long v = (long)i;
        d = kt_push((kt_elem)&v, d);
        ref_push(&r, v);
    }
    for (int i = 0; i < n; i++) {
        kt_elem e; int ok;
        d = kt_pop(d, &e, &ok);
        long ref;
        if (!ok || !ref_pop(&r, &ref)) { ref_destroy(&r); return -1; }
    }
    ref_destroy(&r);
    return 0;
}

static int run_inject_eject(int n) {
    kt_deque d = kt_empty();
    ref_t r = {0};
    for (int i = 0; i < n; i++) {
        long v = (long)i;
        d = kt_inject(d, (kt_elem)&v);
        ref_inject(&r, v);
    }
    for (int i = 0; i < n; i++) {
        kt_elem e; int ok;
        d = kt_eject(d, &e, &ok);
        long ref;
        if (!ok || !ref_eject(&r, &ref)) { ref_destroy(&r); return -1; }
    }
    ref_destroy(&r);
    return 0;
}

static int run_mixed(int n, unsigned int seed) {
    kt_deque d = kt_empty();
    ref_t r = {0};
    srand(seed);
    for (int i = 0; i < n; i++) {
        int op = rand() & 3;
        if (op == 0) { long v = (long)i; d = kt_push((kt_elem)&v, d); ref_push(&r, v); }
        else if (op == 1) { long v = (long)i; d = kt_inject(d, (kt_elem)&v); ref_inject(&r, v); }
        else if (op == 2) { kt_elem e; int ok; d = kt_pop(d, &e, &ok); long ref; if (ok) ref_pop(&r, &ref); }
        else              { kt_elem e; int ok; d = kt_eject(d, &e, &ok); long ref; if (ok) ref_eject(&r, &ref); }
    }
    while (r.len > 0) {
        kt_elem e; int ok; d = kt_pop(d, &e, &ok);
        long ref; if (!ok || !ref_pop(&r, &ref)) { ref_destroy(&r); return -1; }
    }
    ref_destroy(&r);
    return 0;
}

int main(void) {
    int sizes[] = {1, 2, 5, 10, 50, 100, 500, 1000, 10000, 100000};
    int nsizes = sizeof(sizes)/sizeof(sizes[0]);

    printf("=== F2 fallback reachability trace ===\n");
    kt_reset_fallback_counters();

    printf("-- push_pop\n");
    for (int k = 0; k < nsizes; k++) {
        int n = sizes[k];
        int rc = run_push_pop(n);
        printf("  n=%-7d : %s   pop_suf=%zu eject_pre=%zu\n",
               n, rc == 0 ? "OK" : "FAIL",
               kt_fallback_pop_suf(), kt_fallback_eject_pre());
    }
    printf("-- inject_eject\n");
    for (int k = 0; k < nsizes; k++) {
        int n = sizes[k];
        int rc = run_inject_eject(n);
        printf("  n=%-7d : %s   pop_suf=%zu eject_pre=%zu\n",
               n, rc == 0 ? "OK" : "FAIL",
               kt_fallback_pop_suf(), kt_fallback_eject_pre());
    }
    printf("-- mixed\n");
    for (int k = 0; k < nsizes; k++) {
        int n = sizes[k];
        int rc = run_mixed(n, 42 + (unsigned)k);
        printf("  n=%-7d : %s   pop_suf=%zu eject_pre=%zu\n",
               n, rc == 0 ? "OK" : "FAIL",
               kt_fallback_pop_suf(), kt_fallback_eject_pre());
    }

    printf("\n=== Final cumulative counters ===\n");
    printf("  kt_pop  fallback (pop suf when pre empty)   : %zu\n",
           kt_fallback_pop_suf());
    printf("  kt_eject fallback (eject pre when suf empty): %zu\n",
           kt_fallback_eject_pre());
    if (kt_fallback_pop_suf() == 0 && kt_fallback_eject_pre() == 0) {
        printf("\nVERDICT: F2 fallbacks UNREACHABLE on the test corpus.\n");
        return 0;
    } else {
        printf("\nVERDICT: F2 fallbacks REACHED -- fallback IS live code.\n");
        return 1;
    }
}
