/* bench_adversarial.c — persistent-fork microbench for the C library.
 *
 * Mirror of the OCaml-side adversarial bench (paired with
 * https://github.com/yurug/kaplan2/blob/main/ocaml/bench/adversarial.ml ):
 * build a deque to
 * a target logical size by sequential pushes (cost ignored), then time
 * M push operations using the *same saved state* as LHS each time.
 * Persistence: each call returns a new deque; the saved state never
 * changes, so D4-style amortized analyses can't carry credits across
 * calls.
 *
 * For our library this is just another flat line on the plot — we are
 * WC O(1) by construction, so the per-op cost is state-independent.
 * Its presence on the plot is the C ceiling next to the OCaml WC O(1)
 * lines.
 *
 * Output: one CSV row per depth: `C,<depth>,<size>,<ns_per_op>`.
 *
 * Usage:
 *   bench_adversarial --depths 0,1,2,...,18 --m 200000
 */

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

/* Logical size of the primed-d4 chain at given depth: matches
 * the OCaml-side adversarial.ml so the X-axis matches across plots
 * (https://github.com/yurug/kaplan2/blob/main/ocaml/bench/adversarial.ml). */
static long logical_size(int depth) {
    return 5L * ((1L << (depth + 1)) - 1L);
}

static long warm_storage[4096];

/* Warm allocator + ICache + branch predictor before any timed loop.
 * Mirrors what the timed loop does: build a small saved state and run
 * a discarded-result persistent-push loop with periodic compaction —
 * the unusual pattern that the simpler push+pop warmup in bench.c
 * does not exercise. */
static void warmup_runtime(void) {
    for (int i = 0; i < 4096; i++) warm_storage[i] = i + 1;
    kt_deque saved = kt_empty();
    for (int i = 0; i < 256; i++) {
        saved = kt_push(kt_base(&warm_storage[i]), saved);
    }
    kt_arena_compact(&saved, 1);
    kt_elem e = kt_base(&warm_storage[0]);
    /* Mirror the timed-loop body: discarded persistent push with the
     * same compaction cadence the timed loop uses. */
    for (long i = 0; i < 50000; i++) {
        kt_deque _r = kt_push(e, saved);
        (void)_r;
        if ((i & 0xfff) == 0xfff) kt_arena_compact(&saved, 1);
    }
}

/* For each depth d:
 *   - build saved = sequential push of logical_size(d) elements;
 *   - compact arena so the timed loop measures only the per-op cost,
 *     not the cleanup of the build phase;
 *   - time M kt_push calls with `saved` as LHS; discard result.
 * Print one CSV row.
 */
static void run_depth(int depth, long m, long* values, long n_values) {
    long size = logical_size(depth);
    if (size > n_values) {
        fprintf(stderr, "C bench_adversarial: depth %d needs %ld elements "
                "but values[] is %ld\n", depth, size, n_values);
        return;
    }
    kt_deque saved = kt_empty();
    for (long i = 0; i < size; i++) {
        saved = kt_push(kt_base(&values[i]), saved);
    }
    /* Compact so dead links from any prior depth are reclaimed and the
     * timed loop sees a tight working set rooted at `saved`. */
    kt_arena_compact(&saved, 1);

    /* Use a single value for the M persistent pushes — the structural
     * work is value-independent.  We point at warm_storage[0] which
     * is alive through the whole bench (file-scope static).
     *
     * We periodically compact the arena DURING the loop because each
     * persistent push allocates a chain link whose result we discard.
     * Without compaction, M=200k iterations leak ~10 MB of dead links
     * into the arena, spilling the working set out of L2 and adding
     * memory-system noise that has nothing to do with the per-op
     * cost.  The OCaml side avoids this implicitly via minor GC; in
     * C we need to ask for it explicitly.  Compact time is excluded
     * from the per-op measurement. */
    const long COMPACT_INTERVAL = 4096;
    kt_elem e = kt_base(&warm_storage[0]);
    double accum = 0.0;
    long burst = 0;
    long i = 0;
    while (i < m) {
        long todo = m - i;
        if (todo > COMPACT_INTERVAL) todo = COMPACT_INTERVAL;
        double t0 = now_sec();
        for (long j = 0; j < todo; j++) {
            kt_deque _r = kt_push(e, saved);
            (void)_r;
        }
        double t1 = now_sec();
        accum += (t1 - t0);
        i += todo;
        burst++;
        kt_arena_compact(&saved, 1);
    }
    double ns_per_op = accum * 1e9 / (double)m;
    printf("C,%d,%ld,%.3f\n", depth, size, ns_per_op);
    fflush(stdout);
}

static void parse_csv_ints(const char* s, int** out, int* out_n) {
    int n = 1;
    for (const char* p = s; *p; p++) if (*p == ',') n++;
    int* arr = malloc(sizeof(int) * (size_t)n);
    int idx = 0;
    const char* p = s;
    while (*p) {
        char* endp;
        long v = strtol(p, &endp, 10);
        if (endp == p) break;
        arr[idx++] = (int)v;
        if (*endp == ',') p = endp + 1;
        else break;
    }
    *out = arr;
    *out_n = idx;
}

int main(int argc, char** argv) {
    const char* depths_arg = "0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18";
    long m = 200000;
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--depths") == 0 && i + 1 < argc) {
            depths_arg = argv[++i];
        } else if (strcmp(argv[i], "--m") == 0 && i + 1 < argc) {
            m = strtol(argv[++i], NULL, 10);
        } else {
            fprintf(stderr, "usage: %s --depths d1,d2,... --m M\n", argv[0]);
            return 2;
        }
    }
    int* depths = NULL;
    int n_depths = 0;
    parse_csv_ints(depths_arg, &depths, &n_depths);

    /* Worst-case payload: largest depth determines the values[] sizing. */
    int max_depth = 0;
    for (int i = 0; i < n_depths; i++)
        if (depths[i] > max_depth) max_depth = depths[i];
    long n_values = logical_size(max_depth);
    long* values = malloc(sizeof(long) * (size_t)n_values);
    if (!values) { perror("malloc values"); return 1; }
    for (long i = 0; i < n_values; i++) values[i] = i + 1;

    warmup_runtime();
    for (int i = 0; i < n_depths; i++) {
        run_depth(depths[i], m, values, n_values);
    }
    free(values);
    free(depths);
    return 0;
}
