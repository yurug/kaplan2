/* profile_driver.c — runs configurable workload and reports max RSS,
 * page faults, and timing.  Compile with same flags as eject_only.
 *
 * Usage: ./profile_driver <eject|inject|pop|push|mixed> <N>
 */

#include "ktdeque.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/resource.h>

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static long rss_kb(void) {
    struct rusage r; getrusage(RUSAGE_SELF, &r);
    return r.ru_maxrss;
}

static long page_faults(void) {
    struct rusage r; getrusage(RUSAGE_SELF, &r);
    return r.ru_minflt + r.ru_majflt;
}

static long *storage;

int main(int argc, char** argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s <op> <N>\n", argv[0]); return 1; }
    const char* op = argv[1];
    long n = atol(argv[2]);
    storage = malloc(sizeof(long) * (size_t)n);
    for (long i = 0; i < n; i++) storage[i] = i;

    long rss0 = rss_kb();
    long pf0  = page_faults();
    double t_build0 = now_sec();
    kt_deque d = kt_empty();

    if (strcmp(op, "inject") == 0) {
        for (long i = 0; i < n; i++) d = kt_inject(d, (kt_elem)&storage[i]);
        double t1 = now_sec();
        printf("inject N=%ld: %.3f ms (%.1f ns/op)  rss-delta=%ld KB  pf=%ld\n",
               n, (t1 - t_build0) * 1000.0, (t1 - t_build0) * 1e9 / (double)n,
               rss_kb() - rss0, page_faults() - pf0);
    } else if (strcmp(op, "push") == 0) {
        for (long i = 0; i < n; i++) d = kt_push((kt_elem)&storage[i], d);
        double t1 = now_sec();
        printf("push N=%ld: %.3f ms (%.1f ns/op)  rss-delta=%ld KB  pf=%ld\n",
               n, (t1 - t_build0) * 1000.0, (t1 - t_build0) * 1e9 / (double)n,
               rss_kb() - rss0, page_faults() - pf0);
    } else if (strcmp(op, "eject") == 0) {
        for (long i = 0; i < n; i++) d = kt_inject(d, (kt_elem)&storage[i]);
        long rss1 = rss_kb(); long pf1 = page_faults();
        printf("post-build N=%ld: rss=%ld KB pf=%ld\n", n, rss1, pf1 - pf0);
        double t1 = now_sec();
        long sum = 0;
        for (long i = 0; i < n; i++) {
            kt_elem e = NULL; int ne;
            d = kt_eject(d, &e, &ne);
            if (e) sum += *(long*)e;
        }
        double t2 = now_sec();
        printf("eject N=%ld: %.3f ms (%.1f ns/op)  sum=%ld  rss-delta-during=%ld KB  pf-during=%ld\n",
               n, (t2 - t1) * 1000.0, (t2 - t1) * 1e9 / (double)n,
               sum, rss_kb() - rss1, page_faults() - pf1);
    } else if (strcmp(op, "pop") == 0) {
        for (long i = 0; i < n; i++) d = kt_push((kt_elem)&storage[i], d);
        long rss1 = rss_kb(); long pf1 = page_faults();
        printf("post-build N=%ld: rss=%ld KB pf=%ld\n", n, rss1, pf1 - pf0);
        double t1 = now_sec();
        long sum = 0;
        for (long i = 0; i < n; i++) {
            kt_elem e = NULL; int ne;
            d = kt_pop(d, &e, &ne);
            if (e) sum += *(long*)e;
        }
        double t2 = now_sec();
        printf("pop N=%ld: %.3f ms (%.1f ns/op)  sum=%ld  rss-delta-during=%ld KB  pf-during=%ld\n",
               n, (t2 - t1) * 1000.0, (t2 - t1) * 1e9 / (double)n,
               sum, rss_kb() - rss1, page_faults() - pf1);
    } else if (strcmp(op, "mixed") == 0) {
        double t1 = now_sec();
        for (long i = 0; i < n; i++) {
            d = kt_push((kt_elem)&storage[i % n], d);
            d = kt_inject(d, (kt_elem)&storage[(i+1) % n]);
            kt_elem e; int ne;
            d = kt_pop(d, &e, &ne);
        }
        double t2 = now_sec();
        printf("mixed N=%ld: %.3f ms (%.1f ns/op)  rss-delta=%ld KB  pf=%ld\n",
               n, (t2 - t1) * 1000.0, (t2 - t1) * 1e9 / (double)(3*n),
               rss_kb() - rss0, page_faults() - pf0);
    } else { fprintf(stderr, "bad op\n"); return 1; }

    return 0;
}
