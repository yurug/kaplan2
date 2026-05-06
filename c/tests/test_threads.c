/* test_threads.c — multi-thread test: two threads, each with its own
 * deque (in its own thread-local arena), push/pop independently and
 * validate against per-thread reference deque.
 *
 * Build:
 *   gcc -O2 -g -fsanitize=thread -DNDEBUG -Ic/include -pthread \
 *       -o /tmp/test_threads c/src/ktdeque_dequeptr.c c/tests/test_threads.c
 *
 * Run:
 *   /tmp/test_threads 100000   # 100k ops per thread
 */
#include "ktdeque.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>

extern int kt_check_regular(kt_deque);

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

static int ref_pop(ref_deque* r, long* out) {
    if (!r->head) return 0;
    *out = r->head->val;
    ref_node* n = r->head;
    r->head = n->next;
    if (r->head) r->head->prev = NULL; else r->tail = NULL;
    free(n); r->len--;
    return 1;
}

static void ref_destroy(ref_deque* r) {
    ref_node* n = r->head;
    while (n) { ref_node* next = n->next; free(n); n = next; }
    memset(r, 0, sizeof(*r));
}

typedef struct {
    int n;
    int seed;
    int rc;             /* output: 0 if OK, non-zero on failure. */
    int thread_id;
} thread_arg;

static void* thread_main(void* p) {
    thread_arg* arg = (thread_arg*)p;
    int n = arg->n;
    unsigned int seed = (unsigned int)arg->seed;
    int tid = arg->thread_id;
    /* Each thread has its OWN storage backing for the values it pushes. */
    long* storage = (long*)malloc(sizeof(long) * n);

    /* Steady push, validate, pop, validate. */
    kt_deque d = kt_empty();
    ref_deque r = { 0 };
    for (int i = 0; i < n; i++) {
        long v = (long)tid * 1000000L + (long)i;
        storage[i] = v;
        d = kt_push(kt_base(&storage[i]), d);
        ref_push(&r, v);
    }
    if (kt_check_regular(d) != 0) {
        fprintf(stderr, "thread %d: irregular after %d pushes\n", tid, n);
        arg->rc = -1;
        ref_destroy(&r); free(storage); return NULL;
    }
    if ((int)kt_length(d) != r.len) {
        fprintf(stderr, "thread %d: length mismatch: kt=%zu ref=%d\n",
                tid, kt_length(d), r.len);
        arg->rc = -2;
        ref_destroy(&r); free(storage); return NULL;
    }

    /* Drain via pop, comparing each value against ref. */
    for (int i = 0; i < n; i++) {
        kt_elem e; int ne;
        d = kt_pop(d, &e, &ne);
        if (!ne) {
            fprintf(stderr, "thread %d: pop empty at i=%d\n", tid, i);
            arg->rc = -3;
            ref_destroy(&r); free(storage); return NULL;
        }
        long ref_v = 0;
        if (!ref_pop(&r, &ref_v)) {
            fprintf(stderr, "thread %d: ref empty at i=%d (kt non-empty)\n", tid, i);
            arg->rc = -5;
            ref_destroy(&r); free(storage); return NULL;
        }
        if (*(long*)e != ref_v) {
            fprintf(stderr, "thread %d: pop mismatch %ld vs %ld at i=%d\n",
                    tid, *(long*)e, ref_v, i);
            arg->rc = -4;
            ref_destroy(&r); free(storage); return NULL;
        }
    }

    arg->rc = 0;
    (void)seed;  /* (reserved for randomized variant) */
    ref_destroy(&r);
    free(storage);
    return NULL;
}

int main(int argc, char** argv) {
    int n = (argc > 1) ? atoi(argv[1]) : 100000;
    int n_threads = 4;
    pthread_t threads[8];
    thread_arg args[8];

    for (int i = 0; i < n_threads; i++) {
        args[i].n = n;
        args[i].seed = 42 + i;
        args[i].thread_id = i;
        args[i].rc = -100;
        if (pthread_create(&threads[i], NULL, thread_main, &args[i]) != 0) {
            fprintf(stderr, "pthread_create %d failed\n", i);
            return 1;
        }
    }
    for (int i = 0; i < n_threads; i++) {
        pthread_join(threads[i], NULL);
    }

    int failures = 0;
    for (int i = 0; i < n_threads; i++) {
        printf("  thread %d (n=%d): rc=%d %s\n",
               i, n, args[i].rc, args[i].rc == 0 ? "OK" : "FAIL");
        if (args[i].rc != 0) failures++;
    }
    return failures == 0 ? 0 : 1;
}
