/* profile_no_deref.c — like profile_driver but doesn't deref the popped element. */

#include "ktdeque.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static long *storage;

int main(int argc, char** argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s <pop|eject|inject|push> <N>\n", argv[0]); return 1; }
    const char* op = argv[1];
    long n = atol(argv[2]);
    storage = malloc(sizeof(long) * (size_t)n);
    for (long i = 0; i < n; i++) storage[i] = i;

    kt_deque d = kt_empty();
    int build_inject = (strcmp(op, "eject") == 0 || strcmp(op, "inject") == 0);
    if (build_inject) for (long i = 0; i < n; i++) d = kt_inject(d, (kt_elem)&storage[i]);
    else              for (long i = 0; i < n; i++) d = kt_push  ((kt_elem)&storage[i], d);

    if (strcmp(op, "pop") == 0 || strcmp(op, "eject") == 0) {
        long usepop = (strcmp(op, "pop") == 0);
        unsigned long sumptr = 0;
        double t0 = now_sec();
        for (long i = 0; i < n; i++) {
            kt_elem e = NULL; int ne;
            if (usepop) d = kt_pop(d, &e, &ne);
            else        d = kt_eject(d, &e, &ne);
            sumptr ^= (unsigned long)e;  /* no deref */
        }
        double t1 = now_sec();
        printf("%s N=%ld (no deref): %.1f ns/op  ptrxor=0x%lx\n",
               op, n, (t1-t0)*1e9/(double)n, sumptr);
    } else if (strcmp(op, "pop_deref") == 0 || strcmp(op, "eject_deref") == 0) {
        long usepop = (strcmp(op, "pop_deref") == 0);
        long sum = 0;
        double t0 = now_sec();
        for (long i = 0; i < n; i++) {
            kt_elem e = NULL; int ne;
            if (usepop) d = kt_pop(d, &e, &ne);
            else        d = kt_eject(d, &e, &ne);
            if (e) sum += *(long*)e;
        }
        double t1 = now_sec();
        printf("%s N=%ld (deref): %.1f ns/op  sum=%ld\n",
               op, n, (t1-t0)*1e9/(double)n, sum);
    } else {
        printf("unknown op\n");
    }
    return 0;
}
