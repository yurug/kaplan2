/* profile_warm.c — repeatedly push N then pop N to test cache-warm pop. */
#include "ktdeque.h"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static long *storage;

int main(int argc, char** argv) {
    long n = (argc > 1) ? atol(argv[1]) : 10000;
    long iters = (argc > 2) ? atol(argv[2]) : 100;
    storage = malloc(sizeof(long) * (size_t)n);
    for (long i = 0; i < n; i++) storage[i] = i;

    double tt_pop = 0, tt_push = 0;
    long total_ops = 0;
    for (long iter = 0; iter < iters; iter++) {
        kt_deque d = kt_empty();
        double t0 = now_sec();
        for (long i = 0; i < n; i++) d = kt_push((kt_elem)&storage[i], d);
        double t1 = now_sec();
        long sum = 0;
        for (long i = 0; i < n; i++) {
            kt_elem e; int ne;
            d = kt_pop(d, &e, &ne);
            if (e) sum += *(long*)e;
        }
        double t2 = now_sec();
        tt_push += (t1 - t0);
        tt_pop  += (t2 - t1);
        total_ops += n;
        if (sum != n*(n-1)/2) { fprintf(stderr, "sum mismatch %ld vs %ld\n", sum, n*(n-1)/2); return 1; }
    }
    printf("n=%ld iters=%ld total=%ld ops:\n", n, iters, total_ops);
    printf("  push avg: %.1f ns/op\n", tt_push * 1e9 / (double)total_ops);
    printf("  pop  avg: %.1f ns/op\n", tt_pop  * 1e9 / (double)total_ops);
    return 0;
}
