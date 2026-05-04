/* wc_test.c — adversarial worst-case allocation test.
 *
 * Verifies that the maximum number of allocations across ANY single op is
 * bounded by a small constant — i.e. the deque is worst-case O(1), not
 * just amortized.  Compile with -DKT_PROFILE so the counters are live.
 */

#include "ktdeque.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern size_t kt_alloc_packets(void);
extern size_t kt_alloc_chains(void);
extern size_t kt_alloc_pairs(void);
extern size_t kt_alloc_bufs(void);
extern void   kt_reset_alloc_counters(void);

static long g_storage[2000000];

typedef struct {
    size_t max_pkt, max_lnk, max_pair, max_buf;
    size_t total_ops;
} stats;

#define MEASURE(d, op_expr) do {                                 \
    size_t pkt0  = kt_alloc_packets();                           \
    size_t lnk0  = kt_alloc_chains();                            \
    size_t pair0 = kt_alloc_pairs();                             \
    size_t buf0  = kt_alloc_bufs();                              \
    op_expr;                                                     \
    size_t dpkt  = kt_alloc_packets() - pkt0;                    \
    size_t dlnk  = kt_alloc_chains()  - lnk0;                    \
    size_t dpair = kt_alloc_pairs()   - pair0;                   \
    size_t dbuf  = kt_alloc_bufs()    - buf0;                    \
    if (dpkt  > st.max_pkt)  st.max_pkt  = dpkt;                 \
    if (dlnk  > st.max_lnk)  st.max_lnk  = dlnk;                 \
    if (dpair > st.max_pair) st.max_pair = dpair;                \
    if (dbuf  > st.max_buf)  st.max_buf  = dbuf;                 \
    st.total_ops++;                                              \
} while (0)

static stats run_workload(int n_ops) {
    stats st = {0};
    kt_reset_alloc_counters();
    kt_deque d = kt_empty();

    /* Phase 1: monotonic push -> grows chain depth to ~log2(n). */
    for (int i = 0; i < n_ops; i++) {
        g_storage[i] = i + 1;
        MEASURE(d, d = kt_push(kt_base(&g_storage[i]), d));
    }
    /* Phase 2: monotonic inject. */
    for (int i = 0; i < n_ops; i++) {
        g_storage[n_ops + i] = n_ops + i + 1;
        MEASURE(d, d = kt_inject(d, kt_base(&g_storage[n_ops + i])));
    }
    /* Phase 3: drain via pop / eject. */
    for (int i = 0; i < n_ops; i++) {
        kt_elem e; int ne;
        MEASURE(d, d = kt_pop(d, &e, &ne));
    }
    for (int i = 0; i < n_ops; i++) {
        kt_elem e; int ne;
        MEASURE(d, d = kt_eject(d, &e, &ne));
    }
    /* Phase 4: tight push/pop interleaving. */
    srand(42);
    for (int i = 0; i < n_ops; i++) {
        int op = rand() % 4;
        kt_elem e; int ne;
        switch (op) {
            case 0: g_storage[i] = i;
                    MEASURE(d, d = kt_push(kt_base(&g_storage[i]), d)); break;
            case 1: g_storage[i] = i;
                    MEASURE(d, d = kt_inject(d, kt_base(&g_storage[i]))); break;
            case 2: MEASURE(d, d = kt_pop(d, &e, &ne)); break;
            case 3: MEASURE(d, d = kt_eject(d, &e, &ne)); break;
        }
    }
    return st;
}

int main(void) {
    int sizes[] = { 1000, 10000, 100000 };
    for (size_t i = 0; i < sizeof(sizes)/sizeof(sizes[0]); i++) {
        int n = sizes[i];
        stats st = run_workload(n);
        printf("=== workload n = %d (%zu ops) ===\n", n, st.total_ops);
        printf("  max packets / op: %zu\n", st.max_pkt);
        printf("  max links   / op: %zu\n", st.max_lnk);
        printf("  max pairs   / op: %zu\n", st.max_pair);
        printf("  max bufs    / op: %zu\n", st.max_buf);
        printf("  total       / op: %zu\n",
               st.max_pkt + st.max_lnk + st.max_pair + st.max_buf);
    }
    printf("\nFor true worst-case O(1), the maxima must be flat across n.\n");
    return 0;
}
