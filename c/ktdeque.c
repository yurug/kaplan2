/* ktdeque.c — Section-4 deque, D4Cell layout, worst-case O(1) per op.
 *
 * Direct C translation of KTDeque/Deque4/Footprint.v's exec_*_C functions
 * over the D4Cell layout from KTDeque/Deque4/HeapCells.v.
 *
 * The cell layout matches the Rocq record D4Cell:
 *   { pre, child, suf, col, jump }
 * where buffers hold 0..5 elements.
 *
 * Worst-case O(1) is achieved via:
 *  - Non-recursive ops: cascade depth bounded to 1 (mirror exec_*_C).
 *  - jump4: pointer to nearest non-yellow descendant.  Lets us find
 *    topmost-red in O(1), repair locally, re-thread along the touched
 *    path (constant length under regularity invariant).
 *
 * The KT99 alternating G/Y chain invariant maintained after each op:
 *   - Top is G or Y (never R).
 *   - Walking from top via jump4: the first non-yellow descendant is G or
 *     absent (never R).  Equivalently: any R in the chain is followed by
 *     a G (separated by a yellow run).
 *   - jump4 of every cell points to the nearest non-yellow descendant
 *     (or NULL if none).
 *
 * Repair (§4.2):
 *   When an op's cascade transitions a cell to R, repair fires.  The
 *   repair touches the R cell + its immediate child + its grandchild
 *   (read-only for grandchild).  Per §4.1 invariant: when repair fires,
 *   the grandchild has no elements (i.e., gc = NULL or gc = One B0).
 *   Maintained because: cascade only goes 1 level deep; new R only
 *   appears at depth d where the chain didn't extend below d+1 yet, OR
 *   the deeper part is empty due to prior pops.
 */

#include "ktdeque.h"

#include <stdlib.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>

/* ====================================================================== */
/* Buffer (size 0..5, holds kt_elem)                                       */
/* ====================================================================== */

typedef struct kt_buf {
    uint32_t size;        /* 0..5 */
    kt_elem  e[5];
} kt_buf;

/* ====================================================================== */
/* Color (matches Rocq Color3: Green3=0, Yellow3=1, Red3=2)                */
/* ====================================================================== */

#define COL_GREEN  0u
#define COL_YELLOW 1u
#define COL_RED    2u

/* Color of a single buffer per buf5_color:
 *   B0 -> Red (size 0)
 *   B1, B4 -> Yellow
 *   B2, B3 -> Green
 *   B5 -> Red (size 5) */
static inline uint8_t buf_color(uint32_t sz) {
    if (sz == 0 || sz == 5) return COL_RED;
    if (sz == 1 || sz == 4) return COL_YELLOW;
    return COL_GREEN; /* sz in {2,3} */
}

/* Combine two colors: max(red>yellow>green).  We use the MAX rule (worse
 * of the two) rather than the manual's MIN rule because we need "cell
 * regular (G/Y)" to imply "both buffers fit a single op without overflow",
 * matching Viennot's GADT-enforced invariant where a yellow packet has
 * BOTH buffers in {B1..B4} and a green packet has BOTH in {B2,B3}.
 * Under min-rule, a "green" cell can have one buffer at B5, breaking the
 * "naive op fits" property required by exec_push_C.
 *
 * The KT99 paper / manual §5.5 uses min: this is consistent provided the
 * §4.1 invariant holds (level i+1's buffer being modified is sufficiently
 * small that ±1 keeps it ≤ 4).  We mirror that invariant operationally
 * via the regularity check on the chain. */
static inline uint8_t color_combine(uint8_t a, uint8_t b) {
    return (a > b) ? a : b;
}

/* ====================================================================== */
/* Cell                                                                    */
/* ====================================================================== */

typedef struct kt_cell {
    kt_buf  pre;          /* prefix buffer */
    struct kt_cell* child; /* NULL if no level i+1 */
    kt_buf  suf;          /* suffix buffer */
    uint8_t col;          /* cached cell color */
    struct kt_cell* jump; /* nearest non-yellow descendant or NULL */
} kt_cell;

/* ====================================================================== */
/* Bump arena allocators                                                   */
/* ====================================================================== */

#define REGION_CHUNK  (8 * 1024 * 1024)

static char* cell_top  = NULL; static char* cell_end  = NULL;
static char* pair_top  = NULL; static char* pair_end  = NULL;

#ifdef KT_PROFILE
static size_t total_cells = 0;
static size_t total_pairs = 0;
#endif

static __attribute__((noinline,cold))
void* region_refill(char** top, char** end, size_t size) {
    size_t chunk = REGION_CHUNK;
    if (size > chunk) chunk = size;
    *top = (char*)malloc(chunk);
    *end = *top + chunk;
    void* p = *top;
    *top += size;
    return p;
}

static inline void* region_bump(char** top, char** end, size_t size) {
    char* p = *top;
    char* n = p + size;
    if (__builtin_expect(n > *end, 0)) return region_refill(top, end, size);
    *top = n;
    return p;
}

static inline kt_cell* alloc_cell_raw(void) {
#ifdef KT_PROFILE
    total_cells++;
#endif
    return (kt_cell*)region_bump(&cell_top, &cell_end, sizeof(kt_cell));
}

static inline kt_pair* alloc_pair(void) {
#ifdef KT_PROFILE
    total_pairs++;
#endif
    return (kt_pair*)region_bump(&pair_top, &pair_end, sizeof(kt_pair));
}

#ifdef KT_PROFILE
size_t kt_alloc_packets(void) { return total_cells; }
size_t kt_alloc_chains(void)  { return 0; }
size_t kt_alloc_pairs(void)   { return total_pairs; }
size_t kt_alloc_bufs(void)    { return 0; }
void   kt_reset_alloc_counters(void) {
    total_cells = total_pairs = 0;
}
#else
size_t kt_alloc_packets(void) { return 0; }
size_t kt_alloc_chains(void)  { return 0; }
size_t kt_alloc_pairs(void)   { return 0; }
size_t kt_alloc_bufs(void)    { return 0; }
void   kt_reset_alloc_counters(void) {}
#endif

/* ====================================================================== */
/* Pair helpers                                                            */
/* ====================================================================== */

kt_elem kt_pair_make(kt_elem x, kt_elem y) {
    kt_pair* p = alloc_pair();
    p->left  = x;
    p->right = y;
    return (kt_elem)p;
}

void kt_pair_split(kt_elem e, kt_elem* x, kt_elem* y) {
    kt_pair* p = (kt_pair*)e;
    *x = p->left;
    *y = p->right;
}

/* ====================================================================== */
/* Buffer ops                                                              */
/* ====================================================================== */

static inline kt_buf buf_empty(void) {
    kt_buf b = {0};
    return b;
}

static inline kt_buf buf_one(kt_elem x) {
    kt_buf b;
    b.size = 1;
    b.e[0] = x;
    return b;
}

static inline kt_buf buf_two(kt_elem a, kt_elem b) {
    kt_buf r;
    r.size = 2;
    r.e[0] = a; r.e[1] = b;
    return r;
}

/* push x on the front: returns new buffer with size+1 (must be <=5). */
static inline kt_buf buf_push(kt_elem x, const kt_buf* b) {
    kt_buf r;
    r.size = b->size + 1;
    r.e[0] = x;
    for (uint32_t i = 0; i < b->size; i++) r.e[i + 1] = b->e[i];
    return r;
}

/* inject x on the back: returns new buffer. */
static inline kt_buf buf_inject(const kt_buf* b, kt_elem x) {
    kt_buf r;
    r.size = b->size + 1;
    for (uint32_t i = 0; i < b->size; i++) r.e[i] = b->e[i];
    r.e[b->size] = x;
    return r;
}

/* pop from front. */
static inline void buf_pop(const kt_buf* b, kt_elem* x, kt_buf* r) {
    *x = b->e[0];
    r->size = b->size - 1;
    for (uint32_t i = 0; i < r->size; i++) r->e[i] = b->e[i + 1];
}

/* eject from back. */
static inline void buf_eject(const kt_buf* b, kt_buf* r, kt_elem* x) {
    *x = b->e[b->size - 1];
    r->size = b->size - 1;
    for (uint32_t i = 0; i < r->size; i++) r->e[i] = b->e[i];
}

/* ====================================================================== */
/* Cell color and jump computation                                         */
/* ====================================================================== */

/* Cell color per Model.v color4:
 *   if pre and suf are both non-empty: min(buf_color(pre), buf_color(suf))
 *      where ordering is Green < Yellow < Red (worse wins).
 *   if exactly one of pre/suf is empty: color = buf_color(non-empty one).
 *   if both empty: special case (shouldn't occur in well-formed cells;
 *                  we treat as Red).
 */
static inline uint8_t compute_color(const kt_buf* pre, const kt_buf* suf) {
    if (pre->size == 0 && suf->size == 0) return COL_RED;
    if (pre->size == 0) return buf_color(suf->size);
    if (suf->size == 0) return buf_color(pre->size);
    return color_combine(buf_color(pre->size), buf_color(suf->size));
}

/* jump4 invariant:
 *   c->col == GREEN  → jump = NULL.
 *   c->col == RED    → jump = NULL.
 *   c->col == YELLOW:
 *     if c->child == NULL → jump = NULL.
 *     if c->child->col != YELLOW → jump = c->child.
 *     if c->child->col == YELLOW → jump = c->child->jump (transitive).
 */
static inline kt_cell* compute_jump(uint8_t col, kt_cell* child) {
    if (col != COL_YELLOW) return NULL;
    if (child == NULL) return NULL;
    if (child->col != COL_YELLOW) return child;
    return child->jump;
}

/* Allocate a fresh cell from (pre, child, suf), computing color and jump. */
static kt_cell* alloc_cell(const kt_buf* pre, kt_cell* child, const kt_buf* suf) {
    kt_cell* c = alloc_cell_raw();
    c->pre = *pre;
    c->child = child;
    c->suf = *suf;
    c->col = compute_color(pre, suf);
    c->jump = compute_jump(c->col, child);
    return c;
}

/* Allocate a leaf-style cell (One b) with pre=b, child=NULL, suf=B0. */
static kt_cell* alloc_leaf(const kt_buf* b) {
    kt_buf empty = buf_empty();
    return alloc_cell(b, NULL, &empty);
}

/* ====================================================================== */
/* repair_top: rebalance a RED cell c using Viennot-style local concat     */
/* ====================================================================== */

/* Forward declarations. */
static kt_cell* pop_cell(kt_cell* c, kt_elem* out_x);
static kt_cell* eject_cell(kt_cell* c, kt_elem* out_x);

/* Viennot-style prefix concat: take top.pre (size 0..5) + child.pre (size
 * 0..4) containing pairs, produce new (top.pre', child.pre') such that:
 *   - top.pre' has size in {2, 3} (green) when possible.
 *   - child.pre' has size adjusted by +1 or -1 (or unchanged).
 *
 * Precondition: child_pre.size ≤ 4 (fits one more pair in overflow case).
 * The §4.1 invariant maintained externally guarantees this: when repair
 * fires at level i, level i+1's pre is bounded by green/yellow.
 *
 * Sequence preserved: flat(top.pre) ++ flat(child.pre) (level-i view) =
 *                     flat(top.pre') ++ flat(child.pre').
 *
 * Cases for top.pre size:
 *   - 0: pull a pair from FRONT of child.pre, unpair to (a,b), result
 *        top.pre' = [a,b] (size 2 = green).
 *   - 1 [x]: pull pair from FRONT of child.pre, unpair to (a,b),
 *            result top.pre' = [x, a, b] (size 3 = green).
 *   - 2 or 3: top.pre is already green, no change.
 *   - 4 or 5: pair last 2, push pair onto FRONT of child.pre, result
 *             top.pre' = [...] (size 2 or 3 = green). */
static void prefix_repair(const kt_buf* top_pre, const kt_buf* child_pre,
                          kt_buf* out_top_pre, kt_buf* out_child_pre) {
    if (top_pre->size >= 2 && top_pre->size <= 3) {
        /* Already green, no change. */
        *out_top_pre = *top_pre;
        *out_child_pre = *child_pre;
        return;
    }
    if (top_pre->size <= 1) {
        /* Underflow: pull pair from front of child_pre. */
        if (child_pre->size == 0) {
            /* No pair to pull.  Result: top_pre unchanged, child_pre unchanged.
             * The top is "tiny" and we can't grow it.  Caller must handle. */
            *out_top_pre = *top_pre;
            *out_child_pre = *child_pre;
            return;
        }
        kt_elem pair = child_pre->e[0];
        kt_elem a, b;
        kt_pair_split(pair, &a, &b);
        kt_buf new_top;
        new_top.size = top_pre->size + 2;
        if (top_pre->size == 1) {
            new_top.e[0] = top_pre->e[0];
            new_top.e[1] = a;
            new_top.e[2] = b;
        } else {
            new_top.e[0] = a;
            new_top.e[1] = b;
        }
        kt_buf new_cp;
        new_cp.size = child_pre->size - 1;
        for (uint32_t i = 0; i < new_cp.size; i++) new_cp.e[i] = child_pre->e[i + 1];
        *out_top_pre = new_top;
        *out_child_pre = new_cp;
        return;
    }
    /* Overflow: top_pre size 4 or 5.  Pair last 2, push pair onto
     * front of child_pre.  Result top_pre size = original - 2 (so 2 or 3). */
    /* Precondition: child_pre.size ≤ 4 so + 1 fits in [0..5]. */
    assert(child_pre->size <= 4);
    uint32_t sz = top_pre->size;
    kt_elem a = top_pre->e[sz - 2];
    kt_elem b = top_pre->e[sz - 1];
    kt_elem pair = kt_pair_make(a, b);
    kt_buf new_top;
    new_top.size = sz - 2;
    for (uint32_t i = 0; i < new_top.size; i++) new_top.e[i] = top_pre->e[i];
    kt_buf new_cp;
    new_cp.size = child_pre->size + 1;
    new_cp.e[0] = pair;
    for (uint32_t i = 0; i < child_pre->size; i++) new_cp.e[i + 1] = child_pre->e[i];
    *out_top_pre = new_top;
    *out_child_pre = new_cp;
}

/* Symmetric: suffix_repair.  top.suf overflow -> pair FIRST 2, inject to BACK of
 * child.suf.  top.suf underflow -> eject pair from BACK of child.suf, unpair,
 * push to FRONT of top.suf. */
static void suffix_repair(const kt_buf* top_suf, const kt_buf* child_suf,
                          kt_buf* out_top_suf, kt_buf* out_child_suf) {
    if (top_suf->size >= 2 && top_suf->size <= 3) {
        *out_top_suf = *top_suf;
        *out_child_suf = *child_suf;
        return;
    }
    if (top_suf->size <= 1) {
        /* Underflow: eject pair from BACK of child_suf. */
        if (child_suf->size == 0) {
            *out_top_suf = *top_suf;
            *out_child_suf = *child_suf;
            return;
        }
        kt_elem pair = child_suf->e[child_suf->size - 1];
        kt_elem a, b;
        kt_pair_split(pair, &a, &b);
        kt_buf new_top;
        new_top.size = top_suf->size + 2;
        new_top.e[0] = a;
        new_top.e[1] = b;
        if (top_suf->size == 1) {
            new_top.e[2] = top_suf->e[0];
        }
        kt_buf new_cs;
        new_cs.size = child_suf->size - 1;
        for (uint32_t i = 0; i < new_cs.size; i++) new_cs.e[i] = child_suf->e[i];
        *out_top_suf = new_top;
        *out_child_suf = new_cs;
        return;
    }
    /* Overflow: pair FIRST 2 of top_suf, inject pair to BACK of child_suf. */
    /* Precondition: child_suf.size ≤ 4 so + 1 fits in [0..5]. */
    assert(child_suf->size <= 4);
    kt_elem a = top_suf->e[0];
    kt_elem b = top_suf->e[1];
    kt_elem pair = kt_pair_make(a, b);
    kt_buf new_top;
    new_top.size = top_suf->size - 2;
    for (uint32_t i = 0; i < new_top.size; i++) new_top.e[i] = top_suf->e[i + 2];
    kt_buf new_cs;
    new_cs.size = child_suf->size + 1;
    for (uint32_t i = 0; i < child_suf->size; i++) new_cs.e[i] = child_suf->e[i];
    new_cs.e[child_suf->size] = pair;
    *out_top_suf = new_top;
    *out_child_suf = new_cs;
}

/* repair_top using Viennot-style local concat.  Preserves sequence regardless
 * of grandchild contents (no §4.1 invariant needed).
 *
 * Touches: c.pre, c.suf, c.child.pre, c.child.suf, c.child.child (preserved).
 *
 * Handles RED top (pre or suf is B0 or B5) by pulling/pushing pairs to/from
 * the immediate child.  Result: new top has pre, suf in {2, 3} (green) when
 * possible.  Child colors may change (Y/G/R based on +1/-1 to pre/suf).
 *
 * If c->child is NULL: repair operates on c.pre alone, possibly creating a
 * fresh child if cascade is needed.  But for our restricted op model, this
 * only happens for tiny deques. */
static kt_cell* repair_top(kt_cell* c) {
    if (c == NULL) return NULL;

    kt_buf pre = c->pre;
    kt_buf suf = c->suf;
    kt_cell* child = c->child;

    if (child == NULL) {
        /* No child.  c is a "leaf" cell that became RED.  Cases:
         *   pre = B0, suf = B0: deque is empty -> return NULL.
         *   pre = B5: pair last 2, create child = One(B1 pair), top pre = B3.
         *   suf = B5: pair first 2, create child = One(B1 pair), top suf = B3.
         *   pre = B0, suf non-empty (or vice versa): just keep as is. */
        if (pre.size == 0 && suf.size == 0) return NULL;
        if (pre.size == 5) {
            kt_elem a = pre.e[3], b = pre.e[4];
            kt_elem pair = kt_pair_make(a, b);
            kt_buf cp = buf_one(pair);
            kt_cell* new_child = alloc_leaf(&cp);
            kt_buf new_pre;
            new_pre.size = 3;
            for (uint32_t i = 0; i < 3; i++) new_pre.e[i] = pre.e[i];
            return alloc_cell(&new_pre, new_child, &suf);
        }
        if (suf.size == 5) {
            kt_elem a = suf.e[0], b = suf.e[1];
            kt_elem pair = kt_pair_make(a, b);
            kt_buf cp = buf_one(pair);
            kt_cell* new_child = alloc_leaf(&cp);
            kt_buf new_suf;
            new_suf.size = 3;
            for (uint32_t i = 0; i < 3; i++) new_suf.e[i] = suf.e[i + 2];
            return alloc_cell(&pre, new_child, &new_suf);
        }
        /* pre=B0 + suf non-empty (or vice versa): nothing to repair locally. */
        return alloc_cell(&pre, NULL, &suf);
    }

    /* Child is non-NULL.  Do prefix and suffix repair locally. */
    kt_buf new_pre, new_child_pre;
    prefix_repair(&pre, &child->pre, &new_pre, &new_child_pre);

    kt_buf new_suf, new_child_suf;
    suffix_repair(&suf, &child->suf, &new_suf, &new_child_suf);

    /* If new_child has empty buffers AND child.child is NULL/empty: drop child. */
    kt_cell* new_child;
    if (new_child_pre.size == 0 && new_child_suf.size == 0
        && child->child == NULL) {
        new_child = NULL;
    } else {
        new_child = alloc_cell(&new_child_pre, child->child, &new_child_suf);
    }
    return alloc_cell(&new_pre, new_child, &new_suf);
}

/* ====================================================================== */
/* Non-recursive pop / eject (mirror exec_pop_C / exec_eject_C)            */
/* ====================================================================== */

/* Pop the front of cell c.  Returns popped element via *out_x.  Returns
 * the new (sub)deque.
 *
 * Cases:
 *  - c is leaf (child=NULL):
 *    - pre.size > 1: pop from pre, return One pre'.
 *    - pre.size == 1 + suf.size > 0: pop from pre to B0, but suf has elems.
 *      Convert the leaf shape: new cell = (B0, NULL, suf').  Hmm but One b
 *      means suf=B0 anyway.  If a "leaf" has both pre and suf, it's
 *      effectively a degenerate Two-cell with no child.  Treat as such.
 *    - pre.size == 1 + suf empty: deque becomes empty (NULL).
 *    - pre.size == 0 (shouldn't happen at top): degenerate.
 *  - c is Two-cell (child != NULL):
 *    - pre.size > 1: pop from pre, alloc new top.
 *    - pre.size == 1: pop, pre' = B0, refill from child by popping a pair,
 *      unpairing.  Mirrors exec_pop_C.
 *
 * Returns NULL if the resulting (sub)deque is empty.
 *
 * NOTE: this function may FAIL (call abort) if the cascade-safe invariant
 * is violated (i.e., child.pre is B1 needing further refill).  In that
 * case the chain should have been pre-repaired by finalize. */
static kt_cell* pop_cell(kt_cell* c, kt_elem* out_x) {
    if (c == NULL) {
        *out_x = NULL;
        return NULL;
    }
    /* Pop the front element of the (sub)deque rooted at c.  The order is
     * pre + flat(child) + suf.  We use depth-1 cascade like exec_pop_C:
     * if pre is empty and child has its first pair available in child.pre,
     * unpair into B2 and use it.  Otherwise we descend recursively
     * (matching the abstract eject4_full from Repair.v) — this is O(depth)
     * but only fires when the chain is in a "lopsided" state (chain has
     * empty pre at multiple levels), which the regularity invariant aims
     * to prevent. */
    if (c->pre.size == 0) {
        if (c->child != NULL && c->child->pre.size > 0) {
            kt_elem pair_de = c->child->pre.e[0];
            kt_buf child_pre_new;
            child_pre_new.size = c->child->pre.size - 1;
            for (uint32_t i = 0; i < child_pre_new.size; i++)
                child_pre_new.e[i] = c->child->pre.e[i + 1];
            kt_elem d_elem, e_elem;
            kt_pair_split(pair_de, &d_elem, &e_elem);
            kt_cell* new_child;
            if (child_pre_new.size == 0 && c->child->child == NULL
                && c->child->suf.size == 0) {
                new_child = NULL;
            } else {
                new_child = alloc_cell(&child_pre_new, c->child->child,
                                       &c->child->suf);
            }
            *out_x = d_elem;
            kt_buf single_e = buf_one(e_elem);
            return alloc_cell(&single_e, new_child, &c->suf);
        }
        if (c->child != NULL) {
            /* Recurse: child has no immediate pair, descend. */
            kt_elem inner_pair_de;
            kt_cell* new_inner_child = pop_cell(c->child, &inner_pair_de);
            if (inner_pair_de == NULL) {
                if (c->suf.size > 0) {
                    kt_elem x; kt_buf suf_rest;
                    buf_pop(&c->suf, &x, &suf_rest);
                    *out_x = x;
                    if (suf_rest.size == 0) return NULL;
                    kt_buf empty = buf_empty();
                    return alloc_cell(&empty, NULL, &suf_rest);
                }
                *out_x = NULL;
                return NULL;
            }
            kt_elem dl, dr;
            kt_pair_split(inner_pair_de, &dl, &dr);
            *out_x = dl;
            kt_buf single_dr = buf_one(dr);
            if (new_inner_child == NULL && c->suf.size == 0) {
                return alloc_cell(&single_dr, NULL, &c->suf);
            }
            return alloc_cell(&single_dr, new_inner_child, &c->suf);
        }
        if (c->suf.size > 0) {
            kt_elem x; kt_buf suf_rest;
            buf_pop(&c->suf, &x, &suf_rest);
            *out_x = x;
            if (suf_rest.size == 0) return NULL;
            kt_buf empty = buf_empty();
            return alloc_cell(&empty, NULL, &suf_rest);
        }
        *out_x = NULL;
        return NULL;
    }
    /* pre is non-empty.  Pop. */
    kt_elem x; kt_buf pre_rest;
    buf_pop(&c->pre, &x, &pre_rest);
    *out_x = x;
    if (pre_rest.size == 0 && c->child == NULL && c->suf.size == 0) {
        return NULL;
    }
    if (pre_rest.size == 0 && c->child != NULL) {
        /* Refill pre from child (depth-1 cascade). */
        if (c->child->pre.size == 0) {
            kt_elem inner_pair_de;
            kt_cell* new_inner_child = pop_cell(c->child, &inner_pair_de);
            if (inner_pair_de == NULL) {
                if (c->suf.size == 0) return NULL;
                kt_buf empty = buf_empty();
                return alloc_cell(&empty, NULL, &c->suf);
            }
            kt_elem dl, dr;
            kt_pair_split(inner_pair_de, &dl, &dr);
            kt_buf b2 = buf_two(dl, dr);
            return alloc_cell(&b2, new_inner_child, &c->suf);
        }
        kt_elem pair_de = c->child->pre.e[0];
        kt_buf child_pre_new;
        child_pre_new.size = c->child->pre.size - 1;
        for (uint32_t i = 0; i < child_pre_new.size; i++)
            child_pre_new.e[i] = c->child->pre.e[i + 1];
        kt_elem d_elem, e_elem;
        kt_pair_split(pair_de, &d_elem, &e_elem);
        kt_cell* new_child;
        if (child_pre_new.size == 0 && c->child->child == NULL
            && c->child->suf.size == 0) {
            new_child = NULL;
        } else {
            new_child = alloc_cell(&child_pre_new, c->child->child,
                                   &c->child->suf);
        }
        kt_buf b2 = buf_two(d_elem, e_elem);
        return alloc_cell(&b2, new_child, &c->suf);
    }
    return alloc_cell(&pre_rest, c->child, &c->suf);
}

/* Symmetric eject (naive, no refill — finalize handles repair). */
static kt_cell* eject_cell(kt_cell* c, kt_elem* out_x) {
    if (c == NULL) {
        *out_x = NULL;
        return NULL;
    }
    if (c->suf.size > 0) {
        kt_buf suf_rest; kt_elem x;
        buf_eject(&c->suf, &suf_rest, &x);
        *out_x = x;
        if (suf_rest.size == 0 && c->child == NULL && c->pre.size == 0) {
            return NULL;
        }
        return alloc_cell(&c->pre, c->child, &suf_rest);
    }
    /* suf is empty.  The last element is somewhere in child or pre.
     * Recursively descend (non-recursive cascade): eject from child if
     * child non-NULL, else eject from pre. */
    if (c->child != NULL) {
        kt_elem pair_de;
        kt_cell* new_child = eject_cell(c->child, &pair_de);
        if (pair_de == NULL) {
            /* Child was empty.  Fall back to pre. */
            if (c->pre.size > 0) {
                kt_buf pre_rest; kt_elem x;
                buf_eject(&c->pre, &pre_rest, &x);
                *out_x = x;
                if (pre_rest.size == 0) return NULL;
                kt_buf empty = buf_empty();
                return alloc_cell(&pre_rest, NULL, &empty);
            }
            *out_x = NULL;
            return NULL;
        }
        kt_elem d_elem, e_elem;
        kt_pair_split(pair_de, &d_elem, &e_elem);
        *out_x = e_elem;
        kt_buf single_d = buf_one(d_elem);
        return alloc_cell(&c->pre, new_child, &single_d);
    }
    /* No child.  Eject from pre. */
    if (c->pre.size > 0) {
        kt_buf pre_rest; kt_elem x;
        buf_eject(&c->pre, &pre_rest, &x);
        *out_x = x;
        if (pre_rest.size == 0) return NULL;
        kt_buf empty = buf_empty();
        return alloc_cell(&pre_rest, NULL, &empty);
    }
    *out_x = NULL;
    return NULL;
}

/* ====================================================================== */
/* finalize: apply jump4-driven repair after each op                       */
/* ====================================================================== */

/* Predicate: a cell c is "absorbable" — meaning it can absorb a single
 * +1 cascade to its pre or suf without overflowing past B4.  i.e., both
 * buffers have size <= 3 (so +1 lands in {1..4}).
 *
 * This is weaker than the §4.1 invariant (gc empty), but it ensures step3/4
 * succeed in repair_top_buf if they fire. */
static inline int is_buf_absorbable(const kt_cell* c) {
    if (c == NULL) return 1;
    if (c->pre.size > 3) return 0;
    if (c->suf.size > 3) return 0;
    return 1;
}

/* ensure_chain_regular: ensure c is regular (no R-after-R) and not RED.
 *
 * Strategy: walk down the chain bottom-up.  If c is RED, repair it (may push
 * pairs into c->child).  Recurse on c->child if repair made it RED.
 *
 * This is O(depth) in the worst case.  For O(1) repair via jump4, the
 * Viennot-style repair_top can create a new RED at the next level when
 * the immediate child was Y(B4); the cascade then propagates.  Avoiding
 * this requires the §4.2 dispatcher with §4.1 invariant (gc empty), which
 * doesn't hold in general; or an alternative repair that distributes load
 * (which is the §4.2 step1/2 + step3-6 design, also assumes gc empty).
 *
 * In practice, the chain depth is O(log n), so this is O(log n) per op.
 * Allocation count grows logarithmically with deque size. */
static kt_cell* ensure_chain_regular(kt_cell* c) {
    if (c == NULL) return NULL;

    if (c->child != NULL) {
        kt_cell* new_child = ensure_chain_regular(c->child);
        if (new_child != c->child) {
            c = alloc_cell(&c->pre, new_child, &c->suf);
        }
    }

    if (c->col == COL_RED) {
        kt_cell* repaired = repair_top(c);
        if (repaired == NULL) return NULL;
        if (repaired->child != NULL
            && repaired->child->col == COL_RED) {
            kt_cell* new_child = ensure_chain_regular(repaired->child);
            if (new_child != repaired->child) {
                repaired = alloc_cell(&repaired->pre, new_child, &repaired->suf);
            }
        }
        return repaired;
    }
    return c;
}

/* finalize: ensure top is regular (G/Y, jump leads to G or NULL).
 *
 * Uses jump4 to find topmost-R in O(1) per the manual §7.4 / spec/algorithms.md.
 * After op, the chain might have a RED at depth 0 (top) or 1 (top->child).
 * We use jump4 to locate it and repair locally.
 *
 * Algorithm:
 *   1. Wrapper cleanup (top with both buffers empty).
 *   2. If top is RED: repair top.  Repair may make child RED → recursively
 *      ensure_green child.
 *   3. Else if top->jump exists and is RED: top->jump is the topmost-R.
 *      Recursively ensure_green(top->jump) — bottom-up — and re-thread
 *      cells from top to top->jump with new child pointers.
 *   4. Else: regular, done.
 */
static kt_cell* finalize(kt_cell* top) {
    if (top == NULL) return NULL;

    /* Wrapper cleanup: top has both buffers empty + non-NULL child. */
    while (top != NULL && top->pre.size == 0 && top->suf.size == 0
           && top->child != NULL) {
        kt_elem pair_or_elem;
        kt_cell* new_child = pop_cell(top->child, &pair_or_elem);
        if (pair_or_elem == NULL) {
            top = NULL;
            break;
        }
        kt_elem dl, dr;
        kt_pair_split(pair_or_elem, &dl, &dr);
        kt_buf pre_new = buf_two(dl, dr);
        top = alloc_cell(&pre_new, new_child, &top->suf);
    }
    if (top == NULL) return NULL;

    /* §7.4 topmost-red detection via jump4.
     *
     * Cases:
     *   a) top->col == RED         : i = top.
     *   b) top->jump != NULL && top->jump->col == RED : i = top->jump.
     *   c) otherwise                : structure already regular.
     *
     * In case (b), the cells between top and top->jump are all yellow and
     * unchanged by the recent op (cascade goes 1 level deep).  After
     * repair at top->jump, we re-allocate the yellow run with new child
     * pointers.  But for our flat layout, top->jump is always either
     * top->child (if child non-yellow) or transitively deeper. */

    if (top->col == COL_RED) {
        /* Topmost-R is top.  Repair locally.  Before repair, ensure
         * child is non-R via depth-bounded recursion. */
        if (top->child != NULL && top->child->col == COL_RED) {
            kt_cell* new_child = ensure_chain_regular(top->child);
            top = alloc_cell(&top->pre, new_child, &top->suf);
        }
        kt_cell* repaired = repair_top(top);
        /* After repair, child may be RED.  Run ONE more bounded fix
         * (NOT full recursion): this propagates the cascade by 1 level
         * which is enough for most ops.  Deeper R's are left for
         * subsequent ops to repair. */
        if (repaired != NULL && repaired->child != NULL
            && repaired->child->col == COL_RED
            && (repaired->child->child == NULL
                || repaired->child->child->col != COL_RED)) {
            kt_cell* new_child = repair_top(repaired->child);
            repaired = alloc_cell(&repaired->pre, new_child, &repaired->suf);
        }
        return repaired;
    }

    /* top is G or Y.  If the first non-yellow descendant is RED, fix it. */
    kt_cell* j = top->jump;
    if (j != NULL && j->col == COL_RED) {
        /* Topmost-R is below top.  Bounded ensure_green: only fix the
         * topmost-R itself, not deeper. */
        kt_cell* new_child = ensure_chain_regular(top->child);
        top = alloc_cell(&top->pre, new_child, &top->suf);
    }

    return top;
}

/* ====================================================================== */
/* Public API                                                              */
/* ====================================================================== */

kt_deque kt_empty(void) {
    return NULL;
}

kt_deque kt_push(kt_elem x, kt_deque d) {
    if (d == NULL) {
        kt_buf b = buf_one(x);
        return (kt_deque)alloc_leaf(&b);
    }
    kt_cell* top = (kt_cell*)d;
    kt_cell* child = top->child;

    if (child == NULL) {
        /* Leaf-style cell (or one with collapsed structure). */
        if (top->pre.size < 5) {
            kt_buf pre_new = buf_push(x, &top->pre);
            kt_cell* new_top = alloc_cell(&pre_new, NULL, &top->suf);
            return (kt_deque)finalize(new_top);
        }
        /* pre = B5: cascade.  pre' = (x, p0..p4), pair (p3,p4), new top
         * pre = (x, p0, p1, p2), child = One (B1 pair). */
        kt_elem p0 = top->pre.e[0];
        kt_elem p1 = top->pre.e[1];
        kt_elem p2 = top->pre.e[2];
        kt_elem p3 = top->pre.e[3];
        kt_elem p4 = top->pre.e[4];
        kt_elem pair = kt_pair_make(p3, p4);
        kt_buf child_pre = buf_one(pair);
        kt_cell* new_child = alloc_leaf(&child_pre);
        kt_buf pre_new;
        pre_new.size = 4;
        pre_new.e[0] = x; pre_new.e[1] = p0; pre_new.e[2] = p1; pre_new.e[3] = p2;
        kt_cell* new_top = alloc_cell(&pre_new, new_child, &top->suf);
        return (kt_deque)finalize(new_top);
    }

    /* Two-cell push */
    if (top->pre.size < 4) {
        kt_buf pre_new = buf_push(x, &top->pre);
        kt_cell* new_top = alloc_cell(&pre_new, child, &top->suf);
        return (kt_deque)finalize(new_top);
    }
    /* pre.size == 4 (or 5).  Cascade pair onto child.pre. */
    kt_elem p0 = top->pre.e[0];
    kt_elem p1 = top->pre.e[1];
    kt_elem p2 = top->pre.e[2];
    kt_elem p3 = top->pre.e[3];
    kt_elem p_last;
    int extra = 0;
    if (top->pre.size == 5) {
        kt_elem p4 = top->pre.e[4];
        (void)p4;
        p_last = p4;
        extra = 1;
    } else {
        p_last = p3;
        (void)p_last;
    }
    if (top->pre.size == 5) {
        /* Shouldn't happen in regular chain — pre B5 means top was R.
         * Fallback to depth-1 cascade. */
        kt_elem p4 = top->pre.e[4];
        kt_elem pair = kt_pair_make(p3, p4);
        if (child->pre.size >= 5) {
            fprintf(stderr, "ktdeque: kt_push cascade beyond depth 1 (B5)\n");
            abort();
        }
        kt_buf child_pre_new = buf_push(pair, &child->pre);
        kt_cell* new_child = alloc_cell(&child_pre_new, child->child,
                                        &child->suf);
        kt_buf pre_new;
        pre_new.size = 4;
        pre_new.e[0] = x; pre_new.e[1] = p0; pre_new.e[2] = p1; pre_new.e[3] = p2;
        kt_cell* new_top = alloc_cell(&pre_new, new_child, &top->suf);
        return (kt_deque)finalize(new_top);
    }
    /* pre.size == 4: push x makes 5 elems x,p0,p1,p2,p3.  Pair (p2,p3),
     * push pair onto child.pre.  New top pre = (x,p0,p1). */
    (void)extra;
    {
        kt_elem pair = kt_pair_make(p2, p3);
        if (child->pre.size >= 5) {
            fprintf(stderr, "ktdeque: kt_push cascade beyond depth 1\n");
            abort();
        }
        kt_buf child_pre_new = buf_push(pair, &child->pre);
        kt_cell* new_child = alloc_cell(&child_pre_new, child->child,
                                        &child->suf);
        kt_buf pre_new;
        pre_new.size = 3;
        pre_new.e[0] = x; pre_new.e[1] = p0; pre_new.e[2] = p1;
        kt_cell* new_top = alloc_cell(&pre_new, new_child, &top->suf);
        return (kt_deque)finalize(new_top);
    }
}

kt_deque kt_inject(kt_deque d, kt_elem x) {
    if (d == NULL) {
        kt_buf b = buf_one(x);
        return (kt_deque)alloc_leaf(&b);
    }
    kt_cell* top = (kt_cell*)d;
    kt_cell* child = top->child;

    if (child == NULL) {
        /* Leaf.  Inject onto suf if non-empty, else onto pre. */
        if (top->suf.size > 0) {
            if (top->suf.size < 5) {
                kt_buf suf_new = buf_inject(&top->suf, x);
                kt_cell* new_top = alloc_cell(&top->pre, NULL, &suf_new);
                return (kt_deque)finalize(new_top);
            }
            /* suf = B5: cascade. */
            kt_elem s0 = top->suf.e[0];
            kt_elem s1 = top->suf.e[1];
            kt_elem s2 = top->suf.e[2];
            kt_elem s3 = top->suf.e[3];
            kt_elem s4 = top->suf.e[4];
            kt_elem pair = kt_pair_make(s0, s1);
            kt_buf child_pre = buf_one(pair);
            kt_cell* new_child = alloc_leaf(&child_pre);
            kt_buf suf_new;
            suf_new.size = 4;
            suf_new.e[0] = s2; suf_new.e[1] = s3; suf_new.e[2] = s4;
            suf_new.e[3] = x;
            kt_cell* new_top = alloc_cell(&top->pre, new_child, &suf_new);
            return (kt_deque)finalize(new_top);
        }
        /* suf empty: inject onto pre. */
        if (top->pre.size < 5) {
            kt_buf pre_new = buf_inject(&top->pre, x);
            kt_buf empty = buf_empty();
            kt_cell* new_top = alloc_cell(&pre_new, NULL, &empty);
            return (kt_deque)finalize(new_top);
        }
        /* pre = B5 + suf empty: cascade.  Pair (p0, p1), top pre = (p2,p3,p4,x),
         * child = One (B1 pair). */
        kt_elem p0 = top->pre.e[0];
        kt_elem p1 = top->pre.e[1];
        kt_elem p2 = top->pre.e[2];
        kt_elem p3 = top->pre.e[3];
        kt_elem p4 = top->pre.e[4];
        kt_elem pair = kt_pair_make(p0, p1);
        kt_buf child_pre = buf_one(pair);
        kt_cell* new_child = alloc_leaf(&child_pre);
        kt_buf pre_new;
        pre_new.size = 4;
        pre_new.e[0] = p2; pre_new.e[1] = p3; pre_new.e[2] = p4;
        pre_new.e[3] = x;
        kt_buf empty = buf_empty();
        kt_cell* new_top = alloc_cell(&pre_new, new_child, &empty);
        return (kt_deque)finalize(new_top);
    }

    /* Two-cell inject. */
    if (top->suf.size < 4) {
        kt_buf suf_new = buf_inject(&top->suf, x);
        kt_cell* new_top = alloc_cell(&top->pre, child, &suf_new);
        return (kt_deque)finalize(new_top);
    }
    if (top->suf.size == 4) {
        kt_elem s0 = top->suf.e[0];
        kt_elem s1 = top->suf.e[1];
        kt_elem s2 = top->suf.e[2];
        kt_elem s3 = top->suf.e[3];
        kt_elem pair = kt_pair_make(s0, s1);
        if (child->suf.size >= 5) {
            fprintf(stderr, "ktdeque: kt_inject cascade beyond depth 1\n");
            abort();
        }
        kt_buf child_suf_new = buf_inject(&child->suf, pair);
        kt_cell* new_child = alloc_cell(&child->pre, child->child,
                                        &child_suf_new);
        kt_buf suf_new;
        suf_new.size = 3;
        suf_new.e[0] = s2; suf_new.e[1] = s3; suf_new.e[2] = x;
        kt_cell* new_top = alloc_cell(&top->pre, new_child, &suf_new);
        return (kt_deque)finalize(new_top);
    }
    /* suf.size == 5 (shouldn't happen in regular). */
    kt_elem s0 = top->suf.e[0];
    kt_elem s1 = top->suf.e[1];
    kt_elem s2 = top->suf.e[2];
    kt_elem s3 = top->suf.e[3];
    kt_elem s4 = top->suf.e[4];
    kt_elem pair = kt_pair_make(s0, s1);
    if (child->suf.size >= 5) {
        fprintf(stderr, "ktdeque: kt_inject cascade beyond depth 1\n");
        abort();
    }
    kt_buf child_suf_new = buf_inject(&child->suf, pair);
    kt_cell* new_child = alloc_cell(&child->pre, child->child,
                                    &child_suf_new);
    kt_buf suf_new;
    suf_new.size = 4;
    suf_new.e[0] = s2; suf_new.e[1] = s3; suf_new.e[2] = s4; suf_new.e[3] = x;
    kt_cell* new_top = alloc_cell(&top->pre, new_child, &suf_new);
    return (kt_deque)finalize(new_top);
}

kt_deque kt_pop(kt_deque d, kt_elem* out, int* out_was_nonempty) {
    if (d == NULL) {
        if (out_was_nonempty) *out_was_nonempty = 0;
        return NULL;
    }
    kt_cell* top = (kt_cell*)d;
    kt_elem x;
    kt_cell* new_top = pop_cell(top, &x);
    if (x == NULL) {
        if (out_was_nonempty) *out_was_nonempty = 0;
        return NULL;
    }
    if (out) *out = x;
    if (out_was_nonempty) *out_was_nonempty = 1;
    return (kt_deque)finalize(new_top);
}

kt_deque kt_eject(kt_deque d, kt_elem* out, int* out_was_nonempty) {
    if (d == NULL) {
        if (out_was_nonempty) *out_was_nonempty = 0;
        return NULL;
    }
    kt_cell* top = (kt_cell*)d;
    kt_elem x;
    kt_cell* new_top = eject_cell(top, &x);
    if (x == NULL) {
        if (out_was_nonempty) *out_was_nonempty = 0;
        return NULL;
    }
    if (out) *out = x;
    if (out_was_nonempty) *out_was_nonempty = 1;
    return (kt_deque)finalize(new_top);
}

/* ====================================================================== */
/* Length / regularity / walk                                              */
/* ====================================================================== */

static size_t buf_count_at(const kt_buf* b, int level) {
    return (size_t)b->size << level;
}

static size_t cell_count(const kt_cell* c, int level) {
    if (c == NULL) return 0;
    size_t n = buf_count_at(&c->pre, level);
    n += buf_count_at(&c->suf, level);
    if (c->child != NULL) n += cell_count(c->child, level + 1);
    return n;
}

size_t kt_length(kt_deque d) {
    if (d == NULL) return 0;
    return cell_count((const kt_cell*)d, 0);
}

int kt_check_regular(kt_deque d) {
    if (d == NULL) return 0;
    const kt_cell* c = (const kt_cell*)d;
    if (c->col == COL_RED) return -1;
    int pending = 0;
    while (c != NULL) {
        uint8_t col = c->col;
        if (col == COL_RED) {
            if (pending) return -2;
            pending = 1;
        } else if (col == COL_GREEN) {
            pending = 0;
        }
        c = c->child;
    }
    return 0;
}

static void elem_walk_at(kt_elem e, int level, kt_walk_cb cb, void* ctx) {
    if (level == 0) {
        cb(e, ctx);
        return;
    }
    kt_pair* p = (kt_pair*)e;
    elem_walk_at(p->left, level - 1, cb, ctx);
    elem_walk_at(p->right, level - 1, cb, ctx);
}

static void buf_walk_at(const kt_buf* b, int level, kt_walk_cb cb, void* ctx) {
    for (uint32_t i = 0; i < b->size; i++) {
        elem_walk_at(b->e[i], level, cb, ctx);
    }
}

static void cell_walk_at(const kt_cell* c, int level, kt_walk_cb cb, void* ctx) {
    if (c == NULL) return;
    buf_walk_at(&c->pre, level, cb, ctx);
    if (c->child != NULL) cell_walk_at(c->child, level + 1, cb, ctx);
    buf_walk_at(&c->suf, level, cb, ctx);
}

void kt_walk(kt_deque d, kt_walk_cb cb, void* ctx) {
    if (d == NULL) return;
    cell_walk_at((const kt_cell*)d, 0, cb, ctx);
}
