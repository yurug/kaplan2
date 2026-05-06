/* fuzz_afl.c — AFL harness for the C deque.
 *
 * Reads up to MAX_OPS bytes from stdin.  Each byte b encodes one op:
 *   op  = b & 3      (0=push, 1=inject, 2=pop, 3=eject)
 *   tag = b >> 2     (carried as part of the pushed value, so AFL has
 *                     a discriminator for branch differentiation)
 *
 * On every op, the deque mirror is validated against a reference deque
 * (doubly-linked list) — abort() on any divergence.  AFL records the
 * abort as a crash and saves the input that produced it.
 *
 * Build:
 *   afl-gcc -O2 -DAFL_HARNESS -o c/fuzz_afl c/src/ktdeque_dequeptr.c c/tests/fuzz_afl.c
 *
 * Run (sandbox-friendly):
 *   AFL_SKIP_CPUFREQ=1 AFL_I_DONT_CARE_ABOUT_MISSING_CRASHES=1 \
 *   afl-fuzz -i c/tests/afl_seeds -o c/tests/afl_findings -- ./c/fuzz_afl
 */
#include "ktdeque.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define MAX_OPS 4096

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

/* Walk the kt_deque and compare to ref. */
typedef struct { long* arr; size_t idx, cap; } walk_ctx;
static void walk_cb(kt_elem e, void* ctx) {
    walk_ctx* w = (walk_ctx*)ctx;
    if (w->idx < w->cap) w->arr[w->idx] = *(long*)e;
    w->idx++;
}

static long g_storage[MAX_OPS];
static long g_used = 0;

static void __attribute__((noreturn)) die(const char* what) {
    fprintf(stderr, "fuzz_afl: divergence — %s\n", what);
    abort();
}

int main(void) {
    unsigned char buf[MAX_OPS];
    int n = (int)read(0, buf, sizeof(buf));
    if (n <= 0) return 0;

    kt_deque d = kt_empty();
    ref_deque r = {0};

    for (int i = 0; i < n; i++) {
        int op  = buf[i] & 3;
        int tag = buf[i] >> 2;
        long v = ((long)tag << 32) | (long)i;
        switch (op) {
            case 0:
                g_storage[g_used] = v;
                d = kt_push(kt_base(&g_storage[g_used]), d);
                g_used++;
                ref_push(&r, v);
                break;
            case 1:
                g_storage[g_used] = v;
                d = kt_inject(d, kt_base(&g_storage[g_used]));
                g_used++;
                ref_inject(&r, v);
                break;
            case 2: {
                kt_elem e; int ne; long ref_v;
                d = kt_pop(d, &e, &ne);
                int rne = ref_pop(&r, &ref_v);
                if (ne != rne) die("pop nonempty flag");
                if (ne && *(long*)e != ref_v) die("pop value");
                break;
            }
            case 3: {
                kt_elem e; int ne; long ref_v;
                d = kt_eject(d, &e, &ne);
                int rne = ref_eject(&r, &ref_v);
                if (ne != rne) die("eject nonempty flag");
                if (ne && *(long*)e != ref_v) die("eject value");
                break;
            }
        }
        /* Per-op invariant: lengths agree. */
        if ((int)kt_length(d) != r.len) die("length");
    }

    /* Final consistency: walk both, compare. */
    int len = r.len;
    if (len > 0) {
        long* arr = (long*)malloc(sizeof(long) * len);
        walk_ctx w = { arr, 0, (size_t)len };
        kt_walk(d, walk_cb, &w);
        if ((int)w.idx != len) { free(arr); die("walk count"); }
        ref_node* node = r.head;
        for (int i = 0; i < len; i++, node = node->next) {
            if (arr[i] != node->val) { free(arr); die("final walk value"); }
        }
        free(arr);
    }
    return 0;
}
