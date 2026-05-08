/* hello.c — minimal example of using the ktdeque C library.
 *
 * Walks through the four core operations (push / inject / pop / eject)
 * plus a brief persistence demonstration.  Every line is annotated.
 *
 * For the algorithm intuition (why this deque is worst-case O(1) per
 * op when the natural "spill on overflow" approach would be O(log n)),
 * read kb/spec/why-bounded-cascade.md.  For the public C surface,
 * see ../include/ktdeque.h.
 *
 * Build (after `make install` from c/):
 *
 *     cc hello.c -lktdeque -o hello
 *
 * Or via pkg-config:
 *
 *     cc hello.c $(pkg-config --cflags --libs ktdeque) -o hello
 *
 * Or directly against the in-tree build:
 *
 *     cc -I../include -L.. hello.c -lktdeque -o hello
 *
 * Then: ./hello
 */
#include <ktdeque.h>
#include <stdio.h>

static void print_long(kt_elem e, void* ctx) {
    int* first = (int*)ctx;
    if (!*first) printf(", ");
    *first = 0;
    printf("%ld", *(long*)e);
}

int main(void) {
    /* Storage backing for the values we push.  ktdeque does not copy or
     * own values — it stores raw pointers, so the storage must outlive
     * the deque. */
    long values[] = { 10, 20, 30, 40 };

    kt_deque d = kt_empty();
    d = kt_push  (kt_base(&values[0]), d);   /* front -> 10 */
    d = kt_inject(d, kt_base(&values[1]));   /* back  <- 20 */
    d = kt_push  (kt_base(&values[2]), d);   /* front -> 30 */
    /* Deque is now [30, 10, 20]. */

    /* Persistence: branching d gives independent derivatives. */
    kt_deque branch = kt_inject(d, kt_base(&values[3]));  /* [30, 10, 20, 40] */

    printf("d      = ["); { int f = 1; kt_walk(d,      print_long, &f); } printf("]\n");
    printf("branch = ["); { int f = 1; kt_walk(branch, print_long, &f); } printf("]\n");
    printf("|d| = %zu, |branch| = %zu\n",
           kt_length(d), kt_length(branch));

    /* Drain d via pop+eject. */
    kt_elem out; int nonempty;
    d = kt_pop  (d, &out, &nonempty); printf("pop:   %ld\n", *(long*)out);
    d = kt_eject(d, &out, &nonempty); printf("eject: %ld\n", *(long*)out);
    d = kt_pop  (d, &out, &nonempty); printf("pop:   %ld\n", *(long*)out);
    d = kt_pop  (d, &out, &nonempty); printf("empty? %d\n", !nonempty);
    return 0;
}
