/* ====================================================================== *
 * ktcadeque.c - KT99 §6 catenable deque, C port (Phase 1: foundations).   *
 * ====================================================================== *
 *
 * Mirrors rocq/KTDeque/Catenable/FlatChain.v + FlatOps.v branch for
 * branch.  Naming map (Rocq -> C):
 *
 *   fstored        -> kc_sh handle (ground unboxed; small/big boxed)   (FGround/FSmall/FBig = SK_GROUND/SMALL/BIG)
 *   fnode          -> kc_node     (FNode k pre suf)
 *   fbody          -> kc_body     (FHole = NULL; FBSingle/FBPairY/FBPairO)
 *   fchain         -> kc_chain    (FEmpty/FFlat/FSingle/FPair)
 *   buffer (Buf5)  -> kc_buf      (size-tracked §4 deque, = OCaml Fastbuf)
 *
 * The §6 prefix/suffix buffers are §4 deques (ktdeque.h) storing
 * kc_sh handles, exactly as the extracted OCaml artifact's buffers
 * are the verified §4 chain (ocaml/extracted/fastbuf.ml).
 *
 * Allocation: spine nodes and stored cells use malloc for now; the
 * arena/compaction integration is a Phase-5 performance decision (see
 * the C COMPARISON doc).  Values are persistent and immutable, so
 * nothing is freed mid-run.
 */

#include "ktcadeque.h"
#include <stdlib.h>
#include <string.h>
#include <assert.h>

/* Allocation seam.  Default: malloc (persistent, never freed mid-run —
 * see the header).  KC_BUMP: a simple never-compacting bump arena, used
 * only to MEASURE the malloc overhead (it leaks unboundedly, so it is
 * not a production allocator — the real arena/compaction integration is
 * tracked as future work in c/COMPARISON.md). */
#ifdef KC_BUMP
static char*  kc_bump_ptr = NULL;
static char*  kc_bump_end = NULL;
static void*  kc_alloc(size_t sz) {
    sz = (sz + 15) & ~(size_t)15;
    if (kc_bump_ptr + sz > kc_bump_end) {
        size_t chunk = 1u << 26;            /* 64 MiB chunks */
        if (sz > chunk) chunk = sz;
        kc_bump_ptr = (char*)malloc(chunk);
        kc_bump_end = kc_bump_ptr + chunk;
    }
    void* p = kc_bump_ptr; kc_bump_ptr += sz; return p;
}
#define KC_MALLOC(sz) kc_alloc(sz)
#else
#define KC_MALLOC(sz) malloc(sz)
#endif

/* ====================================================================== *
 * Size-tracked buffer (kc_buf) = §4 deque + O(1) element count.           *
 *                                                                          *
 * The §6 colour tests compare buffer sizes against the constants 5/6/7/8 *
 * on every operation, so an O(1) size is mandatory; the §4 deque only    *
 * offers O(N) kt_length.  This wrapper is the C analogue of the OCaml    *
 * Fastbuf's fused size field (DequePtr/SizedChain.v).                     *
 * ====================================================================== */

typedef struct {
    kt_deque d;   /* §4 deque of kc_sh handles */
    uint32_t n;   /* element count (O(1)) */
} kc_buf;

static inline kc_buf cbuf_empty(void) {
    kc_buf b; b.d = kt_empty(); b.n = 0; return b;
}
static inline uint32_t cbuf_size(kc_buf b) { return b.n; }
static inline int cbuf_is_empty(kc_buf b) { return b.n == 0; }

static inline kc_buf cbuf_push(void* x, kc_buf b) {
    kc_buf r; r.d = kt_push((kt_elem)x, b.d); r.n = b.n + 1; return r;
}
static inline kc_buf cbuf_inject(kc_buf b, void* x) {
    kc_buf r; r.d = kt_inject(b.d, (kt_elem)x); r.n = b.n + 1; return r;
}
/* pop: returns 1 and writes *out_x, *out_rest on nonempty; else 0. */
static inline int cbuf_pop(kc_buf b, void** out_x, kc_buf* out_rest) {
    kt_elem x; int ok;
    kt_deque d2 = kt_pop(b.d, &x, &ok);
    if (!ok) return 0;
    *out_x = (void*)x;
    out_rest->d = d2; out_rest->n = b.n - 1;
    return 1;
}
static inline int cbuf_eject(kc_buf b, kc_buf* out_rest, void** out_x) {
    kt_elem x; int ok;
    kt_deque d2 = kt_eject(b.d, &x, &ok);
    if (!ok) return 0;
    *out_x = (void*)x;
    out_rest->d = d2; out_rest->n = b.n - 1;
    return 1;
}

/* singletons / small literals (mirror BufPrims b1/b2/b3) */
static inline kc_buf cbuf_b1(void* x) { return cbuf_push(x, cbuf_empty()); }
static inline kc_buf cbuf_b2(void* x, void* y) {
    return cbuf_push(x, cbuf_b1(y));
}
static inline kc_buf cbuf_b3(void* x, void* y, void* z) {
    return cbuf_push(x, cbuf_b2(y, z));
}

/* append: fold the smaller side into the larger via push/inject.  Every
 * §6 call site has a constant-bounded side under the invariant J
 * (Catenable/Cost.v), so each reachable call is O(1). */
static kc_buf cbuf_append(kc_buf a, kc_buf b) {
    if (a.n == 0) return b;
    if (b.n == 0) return a;
    if (a.n <= b.n) {
        /* inject each of a (front->back) onto the front of b: eject a
         * back-to-front and push onto b. */
        kc_buf acc = b;
        kc_buf rest = a;
        void* x;
        while (cbuf_eject(rest, &rest, &x)) acc = cbuf_push(x, acc);
        return acc;
    } else {
        kc_buf acc = a;
        kc_buf rest = b;
        void* x;
        /* pop each of b front-to-back and inject onto a's back; to keep
         * order, pop from the front of b repeatedly. */
        /* We need b's elements appended in order; pop front gives them
         * front-to-back, inject preserves that order. */
        while (cbuf_pop(rest, &x, &rest)) acc = cbuf_inject(acc, x);
        return acc;
    }
}

/* ====================================================================== *
 * Stored cells: a tagged handle [kc_sh] (the §6 analogue of the OCaml      *
 * Sraw zero-box carrier).                                                  *
 *   ground a   -> the user element ITSELF, unboxed (no allocation)         *
 *   small  b   -> a malloc'd kc_box, tagged in bit 63                      *
 *   big  p c q -> a malloc'd kc_box, tagged in bit 63                      *
 *                                                                          *
 * Ground is the common, hot case (every pushed element); it carries no box *
 * and no per-element malloc.  The "boxed" tag rides in bit 63 — NOT the    *
 * low bits — so it survives the §4 buffer's slot-0 size tag (which masks   *
 * the low 3 bits).  User elements must be canonical low-half pointers /    *
 * 8-aligned scalars (the same contract as the §4 deque), so bit 63 is free.*
 * ====================================================================== */

typedef struct kc_chain kc_chain;   /* forward */

enum { SK_SMALL = 1, SK_BIG = 2 };  /* box kinds (ground is never boxed) */

typedef struct kc_box {
    uint8_t kind;                       /* SK_SMALL | SK_BIG */
    union {
        kc_buf  small;
        struct { kc_buf p; kc_chain* c; kc_buf q; } big;
    } u;
} kc_box;

typedef void* kc_sh;   /* stored handle: ground element, or box | bit 63 */

#define KC_BOXBIT  ((uintptr_t)1 << 63)
#define sh_is_ground(h)  (((uintptr_t)(h) & KC_BOXBIT) == 0)
#define sh_ground(h)     ((kt_elem)(h))
#define sh_box(h)        ((kc_box*)((uintptr_t)(h) & ~KC_BOXBIT))
#define sh_kind(h)       (sh_box(h)->kind)

static inline kc_sh mk_ground(kt_elem a) { return (kc_sh)a; }  /* no malloc */
static kc_sh mk_small(kc_buf b) {
    kc_box* s = (kc_box*)KC_MALLOC(sizeof(kc_box));
    s->kind = SK_SMALL; s->u.small = b;
    return (kc_sh)((uintptr_t)s | KC_BOXBIT);
}
static kc_sh mk_big(kc_buf p, kc_chain* c, kc_buf q) {
    kc_box* s = (kc_box*)KC_MALLOC(sizeof(kc_box));
    s->kind = SK_BIG; s->u.big.p = p; s->u.big.c = c; s->u.big.q = q;
    return (kc_sh)((uintptr_t)s | KC_BOXBIT);
}

/* ====================================================================== *
 * Node / body / chain spine (mirror FlatChain).                           *
 * ====================================================================== */

enum { CK_ONLY = 0, CK_LEFT = 1, CK_RIGHT = 2 };  /* kind */

typedef struct {
    uint8_t k;     /* CK_ONLY / CK_LEFT / CK_RIGHT */
    kc_buf  pre;
    kc_buf  suf;
} kc_node;

/* body: FHole is represented as a NULL kc_body*; the others are tagged. */
enum { CB_BSINGLE = 0, CB_BPAIRY = 1, CB_BPAIRO = 2 };

typedef struct kc_body {
    uint8_t tag;
    kc_node node;       /* head node of the preferred path */
    union {
        struct { struct kc_body* body; } bsingle;
        struct { struct kc_body* body; kc_chain* rc; } bpairy;
        struct { kc_chain* lc; struct kc_body* body; } bpairo;
    } u;
} kc_body;

/* chain: FEmpty (NULL), FFlat (cell, body=NULL), FSingle (cell, body!=NULL),
 * FPair.  FEmpty is represented as a NULL kc_chain*. */
enum { CC_CELL = 0, CC_PAIR = 1 };

struct kc_chain {
    uint8_t tag;
    union {
        /* CC_CELL: FFlat (body==NULL) or FSingle (body!=NULL).
         * FFlat k p s rest = { body=NULL, node=(k,p,s), rest }.
         * FSingle b n rest = { body=b, node=n, rest }. */
        struct { kc_body* body; kc_node node; struct kc_chain* rest; } cell;
        struct { struct kc_chain* left; struct kc_chain* right; } pair;
    } u;
};

/* ---- constructors ---- */

static kc_node node_make(uint8_t k, kc_buf pre, kc_buf suf) {
    kc_node n; n.k = k; n.pre = pre; n.suf = suf; return n;
}

static kc_body* body_bsingle(kc_node n, kc_body* b) {
    kc_body* r = (kc_body*)KC_MALLOC(sizeof(kc_body));
    r->tag = CB_BSINGLE; r->node = n; r->u.bsingle.body = b; return r;
}
static kc_body* body_bpairy(kc_node n, kc_body* b, kc_chain* rc) {
    kc_body* r = (kc_body*)KC_MALLOC(sizeof(kc_body));
    r->tag = CB_BPAIRY; r->node = n; r->u.bpairy.body = b; r->u.bpairy.rc = rc;
    return r;
}
static kc_body* body_bpairo(kc_node n, kc_chain* lc, kc_body* b) {
    kc_body* r = (kc_body*)KC_MALLOC(sizeof(kc_body));
    r->tag = CB_BPAIRO; r->node = n; r->u.bpairo.lc = lc; r->u.bpairo.body = b;
    return r;
}

/* chain cell with explicit body (NULL = FFlat) */
static kc_chain* chain_cell(kc_body* body, kc_node node, kc_chain* rest) {
    kc_chain* c = (kc_chain*)KC_MALLOC(sizeof(kc_chain));
    c->tag = CC_CELL;
    c->u.cell.body = body; c->u.cell.node = node; c->u.cell.rest = rest;
    return c;
}
/* FFlat k p s rest */
static kc_chain* chain_flat(uint8_t k, kc_buf p, kc_buf s, kc_chain* rest) {
    return chain_cell(NULL, node_make(k, p, s), rest);
}
static kc_chain* chain_pair(kc_chain* l, kc_chain* r) {
    kc_chain* c = (kc_chain*)KC_MALLOC(sizeof(kc_chain));
    c->tag = CC_PAIR; c->u.pair.left = l; c->u.pair.right = r;
    return c;
}

/* fsingle: smart constructor keeping hole-bodied cells in FFlat form
 * (mirror FlatChain.fsingle). */
static kc_chain* chain_single(kc_body* b, kc_node n, kc_chain* rest) {
    if (b == NULL) return chain_flat(n.k, n.pre, n.suf, rest);
    return chain_cell(b, n, rest);
}

/* ====================================================================== *
 * Buffer option helpers (mirror BufPrims bpop2/beject2/beject3).          *
 * ====================================================================== */

/* bpop2: first two (front). */
static int cbuf_pop2(kc_buf b, void** x, void** y, kc_buf* rest) {
    kc_buf t;
    if (!cbuf_pop(b, x, &t)) return 0;
    if (!cbuf_pop(t, y, rest)) return 0;
    return 1;
}
/* beject2: last two; result (rest, y, z) with z=last, y=2nd-last. */
static int cbuf_eject2(kc_buf b, kc_buf* rest, void** y, void** z) {
    kc_buf t;
    if (!cbuf_eject(b, &t, z)) return 0;
    if (!cbuf_eject(t, rest, y)) return 0;
    return 1;
}
/* beject3: last three; result (rest, a, bb, c) with c=last. */
static int cbuf_eject3(kc_buf b, kc_buf* rest, void** a, void** bb, void** c) {
    kc_buf t, u;
    if (!cbuf_eject(b, &t, c)) return 0;
    if (!cbuf_eject(t, &u, bb)) return 0;
    if (!cbuf_eject(u, rest, a)) return 0;
    return 1;
}

/* ====================================================================== *
 * Decomposition: fcell + root_and_child_x (mirror FlatOps).               *
 * ====================================================================== */

/* fcell c -> 1 + (body,node,rest) for a cell (FFlat: body=NULL); 0 for
 * FEmpty/FPair. */
static int fcell(kc_chain* c, kc_body** body, kc_node* node, kc_chain** rest) {
    if (c == NULL || c->tag != CC_CELL) return 0;
    *body = c->u.cell.body;
    *node = c->u.cell.node;
    *rest = c->u.cell.rest;
    return 1;
}

/* root_and_child_x: (body,node,rest) -> (out_node, returned child). */
static kc_chain* root_and_child_x(kc_body* b, kc_node n, kc_chain* rest,
                                  kc_node* out_node) {
    if (b == NULL) { *out_node = n; return rest; }  /* FHole */
    *out_node = b->node;
    switch (b->tag) {
        case CB_BSINGLE:
            return chain_single(b->u.bsingle.body, n, rest);
        case CB_BPAIRY:
            return chain_pair(chain_single(b->u.bpairy.body, n, rest),
                              b->u.bpairy.rc);
        case CB_BPAIRO:
            return chain_pair(b->u.bpairo.lc,
                              chain_single(b->u.bpairo.body, n, rest));
        default: assert(0); return NULL;
    }
}

/* ====================================================================== *
 * Node colour + tree_of (rebundling).                                     *
 * ====================================================================== */

enum { CG = 0, CY = 1, CO = 2, CR = 3 };  /* gyor */

static int node_color_x(int has_child, kc_node n) {
    if (!has_child) return CG;
    uint32_t m;
    switch (n.k) {
        case CK_LEFT:  m = cbuf_size(n.pre); break;
        case CK_RIGHT: m = cbuf_size(n.suf); break;
        default: {  /* CK_ONLY */
            uint32_t a = cbuf_size(n.pre), b = cbuf_size(n.suf);
            m = a < b ? a : b;
        }
    }
    if (m >= 8) return CG;
    if (m == 7) return CY;
    if (m == 6) return CO;
    return CR;
}

static kc_chain* tree_of_x(kc_node n, kc_chain* child) {
    int col = node_color_x(child != NULL, n);
    kc_body* cb; kc_node cn; kc_chain* cr;
    switch (col) {
        case CG: case CR:
            return chain_single(NULL, n, child);
        case CY:
            if (fcell(child, &cb, &cn, &cr))
                return chain_single(body_bsingle(n, cb), cn, cr);
            if (child != NULL && child->tag == CC_PAIR &&
                fcell(child->u.pair.left, &cb, &cn, &cr))
                return chain_single(body_bpairy(n, cb, child->u.pair.right),
                                    cn, cr);
            return chain_single(NULL, n, child);
        case CO:
            if (fcell(child, &cb, &cn, &cr))
                return chain_single(body_bsingle(n, cb), cn, cr);
            if (child != NULL && child->tag == CC_PAIR &&
                fcell(child->u.pair.right, &cb, &cn, &cr))
                return chain_single(body_bpairo(n, child->u.pair.left, cb),
                                    cn, cr);
            return chain_single(NULL, n, child);
        default: assert(0); return NULL;
    }
}

/* ====================================================================== *
 * Push / inject.                                                          *
 * ====================================================================== */

static kc_node node_push_x(kc_sh s, kc_node n) {
    if (cbuf_is_empty(n.pre))
        return node_make(n.k, n.pre, cbuf_push(s, n.suf));
    return node_make(n.k, cbuf_push(s, n.pre), n.suf);
}
static kc_node node_inject_x(kc_node n, kc_sh s) {
    if (cbuf_is_empty(n.suf))
        return node_make(n.k, cbuf_inject(n.pre, s), n.suf);
    return node_make(n.k, n.pre, cbuf_inject(n.suf, s));
}

/* upd kind: 0 = push s ; 1 = inject s.  (No closures in C.) */
typedef struct { int op; kc_sh s; } updspec;
static kc_node upd_apply(updspec u, kc_node n) {
    return u.op == 0 ? node_push_x(u.s, n) : node_inject_x(n, u.s);
}

static kc_chain* upd_flat_x(updspec u, uint8_t k, kc_buf p, kc_buf s,
                            kc_chain* rest) {
    return tree_of_x(upd_apply(u, node_make(k, p, s)), rest);
}

static kc_chain* upd_single_x(updspec u, kc_body* b, kc_node n,
                              kc_chain* rest) {
    if (b == NULL) return tree_of_x(upd_apply(u, n), rest);  /* FHole */
    kc_node hn2 = upd_apply(u, b->node);
    int col = node_color_x(1, hn2);
    switch (b->tag) {
        case CB_BSINGLE: {
            kc_body* bp = b->u.bsingle.body;
            if (col == CG || col == CR)
                return chain_single(NULL, hn2, chain_single(bp, n, rest));
            /* CY | CO */
            return chain_single(body_bsingle(hn2, bp), n, rest);
        }
        case CB_BPAIRY: {
            kc_body* bp = b->u.bpairy.body;
            kc_chain* rc = b->u.bpairy.rc;
            if (col == CG || col == CR)
                return chain_single(NULL, hn2,
                    chain_pair(chain_single(bp, n, rest), rc));
            if (col == CY)
                return chain_single(body_bpairy(hn2, bp, rc), n, rest);
            /* CO */
            { kc_body* rb; kc_node rn; kc_chain* rr;
              if (fcell(rc, &rb, &rn, &rr))
                  return chain_single(
                      body_bpairo(hn2, chain_single(bp, n, rest), rb), rn, rr);
              return chain_single(NULL, hn2,
                  chain_pair(chain_single(bp, n, rest), rc)); }
        }
        case CB_BPAIRO: {
            kc_chain* lc = b->u.bpairo.lc;
            kc_body* bp = b->u.bpairo.body;
            if (col == CG || col == CR)
                return chain_single(NULL, hn2,
                    chain_pair(lc, chain_single(bp, n, rest)));
            if (col == CO)
                return chain_single(body_bpairo(hn2, lc, bp), n, rest);
            /* CY */
            { kc_body* lb; kc_node ln; kc_chain* lr;
              if (fcell(lc, &lb, &ln, &lr))
                  return chain_single(
                      body_bpairy(hn2, lb, chain_single(bp, n, rest)), ln, lr);
              return chain_single(NULL, hn2,
                  chain_pair(lc, chain_single(bp, n, rest))); }
        }
        default: assert(0); return NULL;
    }
}

static kc_chain* push_chain_x(kc_sh s, kc_chain* c) {
    if (c == NULL)  /* FEmpty */
        return chain_flat(CK_ONLY, cbuf_b1(s), cbuf_empty(), NULL);
    if (c->tag == CC_PAIR)
        return chain_pair(push_chain_x(s, c->u.pair.left), c->u.pair.right);
    /* CC_CELL */
    updspec u = { 0, s };
    if (c->u.cell.body == NULL)
        return upd_flat_x(u, c->u.cell.node.k, c->u.cell.node.pre,
                          c->u.cell.node.suf, c->u.cell.rest);
    return upd_single_x(u, c->u.cell.body, c->u.cell.node, c->u.cell.rest);
}

static kc_chain* inject_chain_x(kc_chain* c, kc_sh s) {
    if (c == NULL)
        return chain_flat(CK_ONLY, cbuf_empty(), cbuf_b1(s), NULL);
    if (c->tag == CC_PAIR)
        return chain_pair(c->u.pair.left, inject_chain_x(c->u.pair.right, s));
    updspec u = { 1, s };
    if (c->u.cell.body == NULL)
        return upd_flat_x(u, c->u.cell.node.k, c->u.cell.node.pre,
                          c->u.cell.node.suf, c->u.cell.rest);
    return upd_single_x(u, c->u.cell.body, c->u.cell.node, c->u.cell.rest);
}

/* ====================================================================== *
 * Concat (mirror cad_concat_x and its web).  Internal helpers return a    *
 * kc_chain* with the KC_NONE sentinel for the option's None; FEmpty is    *
 * NULL (a valid chain).  The keystone proves Some on regular inputs, so   *
 * kc_concat asserts the result is not KC_NONE.                            *
 * ====================================================================== */

static kc_chain kc_none_sentinel;
#define KC_NONE (&kc_none_sentinel)

/* degenerate_buf_x: a childless KOnly hole-cell with one empty side.
 * Returns 1 and writes *out when degenerate; else 0. */
static int degenerate_buf_x(kc_chain* d, kc_buf* out) {
    if (d == NULL || d->tag != CC_CELL) return 0;
    if (d->u.cell.body != NULL) return 0;       /* must be FFlat / hole */
    if (d->u.cell.rest != NULL) return 0;       /* rest = FEmpty */
    kc_node n = d->u.cell.node;
    if (n.k != CK_ONLY) return 0;
    if (cbuf_is_empty(n.pre)) { *out = n.suf; return 1; }
    if (cbuf_is_empty(n.suf)) { *out = n.pre; return 1; }
    return 0;
}

static kc_chain* make_left_only_x(kc_buf p1, kc_chain* d1, kc_buf s1) {
    if (d1 == NULL) {  /* FEmpty */
        if (cbuf_size(s1) <= 8) {
            kc_buf s1r; void *y, *z;
            if (!cbuf_eject2(s1, &s1r, &y, &z)) return KC_NONE;
            return tree_of_x(node_make(CK_LEFT, cbuf_append(p1, s1r),
                                       cbuf_b2(y, z)), NULL);
        } else {
            void *a, *b, *cc; kc_buf t1, t2, srest;
            if (!cbuf_pop(s1, &a, &t1)) return KC_NONE;
            if (!cbuf_pop(t1, &b, &t2)) return KC_NONE;
            if (!cbuf_pop(t2, &cc, &srest)) return KC_NONE;
            kc_buf smid; void *y, *z;
            if (!cbuf_eject2(srest, &smid, &y, &z)) return KC_NONE;
            kc_chain* ch = push_chain_x(mk_small(smid), NULL);
            return tree_of_x(node_make(CK_LEFT,
                       cbuf_append(p1, cbuf_b3(a, b, cc)), cbuf_b2(y, z)), ch);
        }
    } else {
        kc_buf s1r; void *y, *z;
        if (!cbuf_eject2(s1, &s1r, &y, &z)) return KC_NONE;
        return tree_of_x(node_make(CK_LEFT, p1, cbuf_b2(y, z)),
                         inject_chain_x(d1, mk_small(s1r)));
    }
}

static kc_chain* make_left_x(kc_chain* d) {
    if (d == NULL) return KC_NONE;
    if (d->tag == CC_PAIR) {
        kc_body *bl, *br; kc_node nl, nr; kc_chain *rl, *rr;
        if (!fcell(d->u.pair.left, &bl, &nl, &rl)) return KC_NONE;
        if (!fcell(d->u.pair.right, &br, &nr, &rr)) return KC_NONE;
        kc_node n1, n2; kc_chain* d1 = root_and_child_x(bl, nl, rl, &n1);
        kc_chain* d2 = root_and_child_x(br, nr, rr, &n2);
        kc_buf p1 = n1.pre, s1 = n1.suf, p2 = n2.pre, s2 = n2.suf;
        if (d1 == NULL)
            return make_left_only_x(cbuf_append(p1, cbuf_append(s1, p2)),
                                    d2, s2);
        kc_buf s2r; void *y, *z;
        if (!cbuf_eject2(s2, &s2r, &y, &z)) return KC_NONE;
        return tree_of_x(node_make(CK_LEFT, p1, cbuf_b2(y, z)),
            inject_chain_x(d1, mk_big(cbuf_append(s1, p2), d2, s2r)));
    }
    kc_body* b; kc_node n; kc_chain* rest;
    if (!fcell(d, &b, &n, &rest)) return KC_NONE;
    kc_node n1; kc_chain* d1 = root_and_child_x(b, n, rest, &n1);
    return make_left_only_x(n1.pre, d1, n1.suf);
}

static kc_chain* make_right_only_x(kc_buf p1, kc_chain* d1, kc_buf s1) {
    if (d1 == NULL) {
        if (cbuf_size(p1) <= 8) {
            void *x, *y; kc_buf p1r;
            if (!cbuf_pop2(p1, &x, &y, &p1r)) return KC_NONE;
            return tree_of_x(node_make(CK_RIGHT, cbuf_b2(x, y),
                                       cbuf_append(p1r, s1)), NULL);
        } else {
            void *x, *y; kc_buf p1r;
            if (!cbuf_pop2(p1, &x, &y, &p1r)) return KC_NONE;
            kc_buf pmid; void *a, *b, *cc;
            if (!cbuf_eject3(p1r, &pmid, &a, &b, &cc)) return KC_NONE;
            kc_chain* ch = push_chain_x(mk_small(pmid), NULL);
            return tree_of_x(node_make(CK_RIGHT, cbuf_b2(x, y),
                       cbuf_append(cbuf_b3(a, b, cc), s1)), ch);
        }
    } else {
        void *x, *y; kc_buf p1r;
        if (!cbuf_pop2(p1, &x, &y, &p1r)) return KC_NONE;
        return tree_of_x(node_make(CK_RIGHT, cbuf_b2(x, y), s1),
                         push_chain_x(mk_small(p1r), d1));
    }
}

static kc_chain* make_right_x(kc_chain* e) {
    if (e == NULL) return KC_NONE;
    if (e->tag == CC_PAIR) {
        kc_body *bl, *br; kc_node nl, nr; kc_chain *rl, *rr;
        if (!fcell(e->u.pair.left, &bl, &nl, &rl)) return KC_NONE;
        if (!fcell(e->u.pair.right, &br, &nr, &rr)) return KC_NONE;
        kc_node n1, n2; kc_chain* d1 = root_and_child_x(bl, nl, rl, &n1);
        kc_chain* d2 = root_and_child_x(br, nr, rr, &n2);
        kc_buf p1 = n1.pre, s1 = n1.suf, p2 = n2.pre, s2 = n2.suf;
        if (d2 == NULL)
            return make_right_only_x(p1, d1,
                       cbuf_append(s1, cbuf_append(p2, s2)));
        void *x, *y; kc_buf p1r;
        if (!cbuf_pop2(p1, &x, &y, &p1r)) return KC_NONE;
        return tree_of_x(node_make(CK_RIGHT, cbuf_b2(x, y), s2),
            push_chain_x(mk_big(p1r, d1, cbuf_append(s1, p2)), d2));
    }
    kc_body* b; kc_node n; kc_chain* rest;
    if (!fcell(e, &b, &n, &rest)) return KC_NONE;
    kc_node n1; kc_chain* d1 = root_and_child_x(b, n, rest, &n1);
    return make_right_only_x(n1.pre, d1, n1.suf);
}

/* bfold_right push_chain_x e p : push each element of p onto e (rightmost
 * first), so the leftmost ends up outermost. */
static kc_chain* fold_push(kc_chain* e, kc_buf p) {
    kc_chain* acc = e;
    kc_buf rest = p; void* x;
    while (cbuf_eject(rest, &rest, &x))
        acc = push_chain_x((kc_sh)x, acc);
    return acc;
}
/* bfold_left inject_chain_x s d : inject each element of s onto d (leftmost
 * first). */
static kc_chain* fold_inject(kc_buf s, kc_chain* d) {
    kc_chain* acc = d;
    kc_buf rest = s; void* x;
    while (cbuf_pop(rest, &x, &rest))
        acc = inject_chain_x(acc, (kc_sh)x);
    return acc;
}

static kc_chain* concat_small_left_x(kc_buf p3, kc_chain* e) {
    if (cbuf_size(p3) < 8) return fold_push(e, p3);
    if (e == NULL) return KC_NONE;
    if (e->tag == CC_PAIR) {
        kc_body* bl; kc_node nl; kc_chain* rl;
        if (!fcell(e->u.pair.left, &bl, &nl, &rl)) return KC_NONE;
        kc_node n2; kc_chain* d2 = root_and_child_x(bl, nl, rl, &n2);
        return chain_pair(
            tree_of_x(node_make(CK_LEFT, p3, n2.suf),
                      push_chain_x(mk_small(n2.pre), d2)),
            e->u.pair.right);
    }
    kc_body* b; kc_node n; kc_chain* rest;
    if (!fcell(e, &b, &n, &rest)) return KC_NONE;
    kc_node n2; kc_chain* d2 = root_and_child_x(b, n, rest, &n2);
    kc_buf p2 = n2.pre, s2 = n2.suf;
    if (d2 == NULL) {
        kc_buf p2r; void *y, *z;
        if (!cbuf_eject2(p2, &p2r, &y, &z)) return KC_NONE;
        return tree_of_x(node_make(CK_ONLY, p3, cbuf_push(y, cbuf_push(z, s2))),
                         push_chain_x(mk_small(p2r), NULL));
    }
    return tree_of_x(node_make(CK_ONLY, p3, s2), push_chain_x(mk_small(p2), d2));
}

static kc_chain* concat_small_right_x(kc_chain* d, kc_buf s3) {
    if (cbuf_size(s3) < 8) return fold_inject(s3, d);
    if (d == NULL) return KC_NONE;
    if (d->tag == CC_PAIR) {
        kc_body* br; kc_node nr; kc_chain* rr;
        if (!fcell(d->u.pair.right, &br, &nr, &rr)) return KC_NONE;
        kc_node n1; kc_chain* d1 = root_and_child_x(br, nr, rr, &n1);
        return chain_pair(d->u.pair.left,
            tree_of_x(node_make(CK_RIGHT, n1.pre, s3),
                      inject_chain_x(d1, mk_small(n1.suf))));
    }
    kc_body* b; kc_node n; kc_chain* rest;
    if (!fcell(d, &b, &n, &rest)) return KC_NONE;
    kc_node n1; kc_chain* d1 = root_and_child_x(b, n, rest, &n1);
    kc_buf p1 = n1.pre, s1 = n1.suf;
    if (d1 == NULL) {
        void *x, *y; kc_buf s1r;
        if (!cbuf_pop2(s1, &x, &y, &s1r)) return KC_NONE;
        return tree_of_x(node_make(CK_ONLY, cbuf_inject(cbuf_inject(p1, x), y),
                                   s3),
                         push_chain_x(mk_small(s1r), NULL));
    }
    return tree_of_x(node_make(CK_ONLY, p1, s3), inject_chain_x(d1, mk_small(s1)));
}

static kc_chain* cad_concat_x(kc_chain* d, kc_chain* e) {
    if (d == NULL) return e;
    if (e == NULL) return d;
    kc_buf pp, ss;
    int dgd = degenerate_buf_x(d, &pp);
    int dge = degenerate_buf_x(e, &ss);
    if (dgd && dge) {
        if (cbuf_size(pp) < 8 || cbuf_size(ss) < 8)
            return chain_flat(CK_ONLY, cbuf_append(pp, ss), cbuf_empty(), NULL);
        return chain_flat(CK_ONLY, pp, ss, NULL);
    }
    if (dgd) return concat_small_left_x(pp, e);
    if (dge) return concat_small_right_x(d, ss);
    kc_chain* t = make_left_x(d);
    if (t == KC_NONE) return KC_NONE;
    kc_chain* u = make_right_x(e);
    if (u == KC_NONE) return KC_NONE;
    return chain_pair(t, u);
}

/* ====================================================================== *
 * Pop / eject + repair web (mirror FlatOps Phase-3 functions).            *
 * Cells are the uniform box, so cell_case_ground/cell_case_struct become  *
 * plain kind inspections.                                                 *
 * ====================================================================== */

/* node_pop_x: pop from pre, else suf.  1 + (cell, node') / 0. */
static int node_pop_x(kc_node n, kc_sh* cell, kc_node* out) {
    void* x; kc_buf rest;
    if (cbuf_pop(n.pre, &x, &rest)) {
        *cell = (kc_sh)x; *out = node_make(n.k, rest, n.suf); return 1;
    }
    if (cbuf_pop(n.suf, &x, &rest)) {
        *cell = (kc_sh)x; *out = node_make(n.k, n.pre, rest); return 1;
    }
    return 0;
}
/* node_eject_x: eject from suf, else pre (then suffix becomes empty). */
static int node_eject_x(kc_node n, kc_node* out, kc_sh* cell) {
    void* x; kc_buf rest;
    if (cbuf_eject(n.suf, &rest, &x)) {
        *out = node_make(n.k, n.pre, rest); *cell = (kc_sh)x; return 1;
    }
    if (cbuf_eject(n.pre, &rest, &x)) {
        *out = node_make(n.k, rest, cbuf_empty()); *cell = (kc_sh)x;
        return 1;
    }
    return 0;
}

static kc_chain* rebuild_childless_x(kc_node n) {
    if (cbuf_is_empty(n.pre) && cbuf_is_empty(n.suf)) return NULL;  /* FEmpty */
    if (n.k == CK_ONLY) {
        if (cbuf_is_empty(n.pre) || cbuf_is_empty(n.suf))
            return chain_flat(n.k, n.pre, n.suf, NULL);
        if (cbuf_size(n.pre) < 5 || cbuf_size(n.suf) < 5)
            return chain_flat(CK_ONLY, cbuf_append(n.pre, n.suf),
                              cbuf_empty(), NULL);
        return chain_flat(n.k, n.pre, n.suf, NULL);
    }
    return chain_flat(n.k, n.pre, n.suf, NULL);
}

/* A cell is the degenerate childless-flat shape iff CC_CELL with no body
 * and empty rest (the smart constructor keeps both Rocq forms here). */
static int is_degenerate(kc_chain* c, kc_buf* lp, kc_buf* ls) {
    if (c == NULL || c->tag != CC_CELL) return 0;
    if (c->u.cell.body != NULL || c->u.cell.rest != NULL) return 0;
    *lp = c->u.cell.node.pre; *ls = c->u.cell.node.suf; return 1;
}

/* forward */
static kc_chain* cad_concat_internal(kc_chain* d, kc_chain* e);

static int pop_raw_x(kc_chain* c, kc_sh* cell, kc_chain** out) {
    if (c == NULL) return 0;
    if (c->tag == CC_CELL) {
        kc_node n0; kc_chain* child;
        if (c->u.cell.body == NULL) { n0 = c->u.cell.node; child = c->u.cell.rest; }
        else child = root_and_child_x(c->u.cell.body, c->u.cell.node,
                                      c->u.cell.rest, &n0);
        kc_node n2;
        if (!node_pop_x(n0, cell, &n2)) return 0;
        *out = (child == NULL) ? rebuild_childless_x(n2) : tree_of_x(n2, child);
        return 1;
    }
    /* CC_PAIR */
    kc_chain* lp;
    if (!pop_raw_x(c->u.pair.left, cell, &lp)) return 0;
    kc_chain* r = c->u.pair.right;
    kc_buf lpb, lsb;
    if (lp == NULL) { *out = r; return 1; }
    if (is_degenerate(lp, &lpb, &lsb) && cbuf_size(lpb) < 5) {
        kc_body* br; kc_node nr; kc_chain* rr;
        if (!fcell(r, &br, &nr, &rr)) return 0;
        kc_node n2; kc_chain* d2 = root_and_child_x(br, nr, rr, &n2);
        *out = tree_of_x(node_make(CK_ONLY,
                   cbuf_append(lpb, cbuf_append(lsb, n2.pre)), n2.suf), d2);
        return 1;
    }
    *out = chain_pair(lp, r);
    return 1;
}

static int eject_raw_x(kc_chain* c, kc_chain** out, kc_sh* cell) {
    if (c == NULL) return 0;
    if (c->tag == CC_CELL) {
        kc_node n0; kc_chain* child;
        if (c->u.cell.body == NULL) { n0 = c->u.cell.node; child = c->u.cell.rest; }
        else child = root_and_child_x(c->u.cell.body, c->u.cell.node,
                                      c->u.cell.rest, &n0);
        kc_node n2;
        if (!node_eject_x(n0, &n2, cell)) return 0;
        *out = (child == NULL) ? rebuild_childless_x(n2) : tree_of_x(n2, child);
        return 1;
    }
    /* CC_PAIR */
    kc_chain* rp;
    if (!eject_raw_x(c->u.pair.right, &rp, cell)) return 0;
    kc_chain* l = c->u.pair.left;
    kc_buf rpb, rsb;
    if (rp == NULL) { *out = l; return 1; }
    if (is_degenerate(rp, &rpb, &rsb) && cbuf_size(rsb) < 5) {
        kc_body* bl; kc_node nl; kc_chain* rl;
        if (!fcell(l, &bl, &nl, &rl)) return 0;
        kc_node n1; kc_chain* d1 = root_and_child_x(bl, nl, rl, &n1);
        *out = tree_of_x(node_make(CK_ONLY, n1.pre,
                   cbuf_append(n1.suf, cbuf_append(rpb, rsb))), d1);
        return 1;
    }
    *out = chain_pair(l, rp);
    return 1;
}

static kc_chain* repair_front_x(uint8_t k, kc_body* body, kc_buf p1, kc_buf s1,
                                kc_chain* rest) {
    kc_sh cell; kc_chain* d1p;
    if (!pop_raw_x(rest, &cell, &d1p)) return KC_NONE;
    if ((!sh_is_ground(cell) && sh_kind(cell) == SK_SMALL))
        return chain_single(body,
                   node_make(k, cbuf_append(p1, sh_box(cell)->u.small), s1), d1p);
    if ((!sh_is_ground(cell) && sh_kind(cell) == SK_BIG)) {
        kc_chain* d3 = cad_concat_internal(sh_box(cell)->u.big.c,
                           push_chain_x(mk_small(sh_box(cell)->u.big.q), d1p));
        if (d3 == KC_NONE) return KC_NONE;
        return chain_single(body,
                   node_make(k, cbuf_append(p1, sh_box(cell)->u.big.p), s1), d3);
    }
    return KC_NONE;  /* ground: cell_case_struct's None arm */
}

static kc_chain* repair_back_x(uint8_t k, kc_body* body, kc_buf p1, kc_buf s1,
                               kc_chain* rest) {
    kc_sh cell; kc_chain* d1p;
    if (!eject_raw_x(rest, &d1p, &cell)) return KC_NONE;
    if ((!sh_is_ground(cell) && sh_kind(cell) == SK_SMALL))
        return chain_single(body,
                   node_make(k, p1, cbuf_append(sh_box(cell)->u.small, s1)), d1p);
    if ((!sh_is_ground(cell) && sh_kind(cell) == SK_BIG)) {
        kc_chain* d3 = cad_concat_internal(
                           inject_chain_x(d1p, mk_small(sh_box(cell)->u.big.p)),
                           sh_box(cell)->u.big.c);
        if (d3 == KC_NONE) return KC_NONE;
        return chain_single(body,
                   node_make(k, p1, cbuf_append(sh_box(cell)->u.big.q, s1)), d3);
    }
    return KC_NONE;
}

/* drain_both result: ok=0 means the whole option is None. */
typedef struct {
    int ok;
    kc_sh cellF;
    int has_back;
    kc_sh cellB;
    kc_chain* mid;
} drain_res;

static drain_res drain_both_x(kc_chain* rest) {
    drain_res R = { 0, NULL, 0, NULL, NULL };
    if (rest == NULL) return R;
    if (rest->tag == CC_PAIR) {
        kc_sh cellF, cellB; kc_chain *lp, *rp;
        if (!pop_raw_x(rest->u.pair.left, &cellF, &lp)) return R;
        if (!eject_raw_x(rest->u.pair.right, &rp, &cellB)) return R;
        R.ok = 1; R.cellF = cellF; R.has_back = 1; R.cellB = cellB;
        kc_buf lpb, lsb, rpb, rsb;
        int dl = is_degenerate(lp, &lpb, &lsb);
        int dr = is_degenerate(rp, &rpb, &rsb);
        if (dl && dr) {
            if (cbuf_size(lpb) < 5 || cbuf_size(rsb) < 5)
                R.mid = chain_flat(CK_ONLY, cbuf_append(lpb, lsb),
                                   cbuf_append(rpb, rsb), NULL);
            else R.mid = chain_pair(lp, rp);
        } else if (dl) {
            if (cbuf_size(lpb) < 5) {
                kc_body* br; kc_node nr; kc_chain* rr;
                if (fcell(rp, &br, &nr, &rr)) {
                    kc_node n2; kc_chain* d2 = root_and_child_x(br, nr, rr, &n2);
                    R.mid = tree_of_x(node_make(CK_ONLY,
                        cbuf_append(lpb, cbuf_append(lsb, n2.pre)), n2.suf), d2);
                } else R.mid = chain_pair(lp, rp);
            } else R.mid = chain_pair(lp, rp);
        } else if (dr) {
            if (cbuf_size(rsb) < 5) {
                kc_body* bl; kc_node nl; kc_chain* rl;
                if (fcell(lp, &bl, &nl, &rl)) {
                    kc_node n2; kc_chain* d2 = root_and_child_x(bl, nl, rl, &n2);
                    R.mid = tree_of_x(node_make(CK_ONLY, n2.pre,
                        cbuf_append(n2.suf, cbuf_append(rpb, rsb))), d2);
                } else R.mid = chain_pair(lp, rp);
            } else R.mid = chain_pair(lp, rp);
        } else {
            R.mid = chain_pair(lp, rp);
        }
        return R;
    }
    /* single cell */
    kc_body* b; kc_node n; kc_chain* r0;
    if (!fcell(rest, &b, &n, &r0)) return R;
    kc_node n0; kc_chain* dd = root_and_child_x(b, n, r0, &n0);
    kc_sh cellF; kc_node n1;
    if (!node_pop_x(n0, &cellF, &n1)) return R;
    kc_node n2; kc_sh cellB;
    if (node_eject_x(n1, &n2, &cellB)) {
        R.ok = 1; R.cellF = cellF; R.has_back = 1; R.cellB = cellB;
        R.mid = (dd == NULL) ? rebuild_childless_x(n2) : tree_of_x(n2, dd);
        return R;
    }
    if (dd == NULL) {
        R.ok = 1; R.cellF = cellF; R.has_back = 0; R.cellB = NULL; R.mid = NULL;
        return R;
    }
    return R;  /* None */
}

static kc_chain* repair_both_x(kc_body* body, kc_buf p1, kc_buf s1,
                               kc_chain* rest) {
    drain_res R = drain_both_x(rest);
    if (!R.ok) return KC_NONE;
    if (!R.has_back) {
        kc_sh cF = R.cellF;
        if ((!sh_is_ground(cF) && sh_kind(cF) == SK_SMALL))
            return chain_single(body,
                node_make(CK_ONLY, cbuf_append(p1, sh_box(cF)->u.small), s1), NULL);
        if ((!sh_is_ground(cF) && sh_kind(cF) == SK_BIG))
            return chain_single(body,
                node_make(CK_ONLY, cbuf_append(p1, sh_box(cF)->u.big.p),
                          cbuf_append(sh_box(cF)->u.big.q, s1)), sh_box(cF)->u.big.c);
        return KC_NONE;
    }
    /* front (pf, d4) from cellF */
    kc_buf pf; kc_chain* d4;
    kc_sh cF = R.cellF;
    if ((!sh_is_ground(cF) && sh_kind(cF) == SK_SMALL)) { pf = sh_box(cF)->u.small; d4 = R.mid; }
    else if ((!sh_is_ground(cF) && sh_kind(cF) == SK_BIG)) {
        kc_chain* tmp = cad_concat_internal(sh_box(cF)->u.big.c,
                            push_chain_x(mk_small(sh_box(cF)->u.big.q), R.mid));
        if (tmp == KC_NONE) return KC_NONE;
        pf = sh_box(cF)->u.big.p; d4 = tmp;
    } else return KC_NONE;
    /* back from cellB */
    kc_sh cB = R.cellB;
    if ((!sh_is_ground(cB) && sh_kind(cB) == SK_SMALL))
        return chain_single(body,
            node_make(CK_ONLY, cbuf_append(p1, pf),
                      cbuf_append(sh_box(cB)->u.small, s1)), d4);
    if ((!sh_is_ground(cB) && sh_kind(cB) == SK_BIG)) {
        kc_chain* d5 = cad_concat_internal(
                           inject_chain_x(d4, mk_small(sh_box(cB)->u.big.p)),
                           sh_box(cB)->u.big.c);
        if (d5 == KC_NONE) return KC_NONE;
        return chain_single(body,
            node_make(CK_ONLY, cbuf_append(p1, pf),
                      cbuf_append(sh_box(cB)->u.big.q, s1)), d5);
    }
    return KC_NONE;
}

static kc_chain* repair_packet_x(kc_body* body, kc_node n, kc_chain* rest) {
    int col = node_color_x(rest != NULL, n);
    if (col != CR) return chain_single(body, n, rest);
    if (n.k == CK_LEFT)  return repair_front_x(CK_LEFT, body, n.pre, n.suf, rest);
    if (n.k == CK_RIGHT) return repair_back_x(CK_RIGHT, body, n.pre, n.suf, rest);
    if (cbuf_size(n.suf) >= 8) return repair_front_x(CK_ONLY, body, n.pre, n.suf, rest);
    if (cbuf_size(n.pre) >= 8) return repair_back_x(CK_ONLY, body, n.pre, n.suf, rest);
    return repair_both_x(body, n.pre, n.suf, rest);
}

static kc_chain* repair_pop_side_x(kc_chain* c) {
    if (c == NULL) return NULL;  /* Some FEmpty */
    if (c->tag == CC_CELL)
        return repair_packet_x(c->u.cell.body, c->u.cell.node, c->u.cell.rest);
    /* CC_PAIR: repair left */
    kc_body* bl; kc_node nl; kc_chain* rl;
    if (!fcell(c->u.pair.left, &bl, &nl, &rl)) return KC_NONE;
    kc_chain* lp = repair_packet_x(bl, nl, rl);
    if (lp == KC_NONE) return KC_NONE;
    return chain_pair(lp, c->u.pair.right);
}

static kc_chain* repair_eject_side_x(kc_chain* c) {
    if (c == NULL) return NULL;
    if (c->tag == CC_CELL)
        return repair_packet_x(c->u.cell.body, c->u.cell.node, c->u.cell.rest);
    kc_body* br; kc_node nr; kc_chain* rr;
    if (!fcell(c->u.pair.right, &br, &nr, &rr)) return KC_NONE;
    kc_chain* rp = repair_packet_x(br, nr, rr);
    if (rp == KC_NONE) return KC_NONE;
    return chain_pair(c->u.pair.left, rp);
}

/* fused removal + repair (mirror tree_repair_x). */
static kc_chain* tree_repair_x(kc_node n, kc_chain* child) {
    int col = node_color_x(child != NULL, n);
    if (col == CG) return chain_single(NULL, n, child);
    if (col == CR) {
        if (n.k == CK_LEFT)  return repair_front_x(CK_LEFT, NULL, n.pre, n.suf, child);
        if (n.k == CK_RIGHT) return repair_back_x(CK_RIGHT, NULL, n.pre, n.suf, child);
        if (cbuf_size(n.suf) >= 8) return repair_front_x(CK_ONLY, NULL, n.pre, n.suf, child);
        if (cbuf_size(n.pre) >= 8) return repair_back_x(CK_ONLY, NULL, n.pre, n.suf, child);
        return repair_both_x(NULL, n.pre, n.suf, child);
    }
    kc_body* cb; kc_node cn; kc_chain* cr;
    if (col == CY) {
        if (fcell(child, &cb, &cn, &cr))
            return repair_packet_x(body_bsingle(n, cb), cn, cr);
        if (child != NULL && child->tag == CC_PAIR &&
            fcell(child->u.pair.left, &cb, &cn, &cr))
            return repair_packet_x(body_bpairy(n, cb, child->u.pair.right), cn, cr);
        return chain_single(NULL, n, child);
    }
    /* CO */
    if (fcell(child, &cb, &cn, &cr))
        return repair_packet_x(body_bsingle(n, cb), cn, cr);
    if (child != NULL && child->tag == CC_PAIR &&
        fcell(child->u.pair.right, &cb, &cn, &cr))
        return repair_packet_x(body_bpairo(n, child->u.pair.left, cb), cn, cr);
    return chain_single(NULL, n, child);
}

/* expose concat to the repair web (defined above as cad_concat_x). */
static kc_chain* cad_concat_internal(kc_chain* d, kc_chain* e) {
    return cad_concat_x(d, e);
}

static int cad_pop_x(kc_chain* d, kt_elem* out_x, kc_chain** out) {
    if (d == NULL) return 0;
    if (d->tag == CC_CELL) {
        kc_node n0; kc_chain* child;
        if (d->u.cell.body == NULL) { n0 = d->u.cell.node; child = d->u.cell.rest; }
        else child = root_and_child_x(d->u.cell.body, d->u.cell.node,
                                      d->u.cell.rest, &n0);
        kc_sh cell; kc_node n2;
        if (!node_pop_x(n0, &cell, &n2)) return 0;
        if (!sh_is_ground(cell)) return 0;
        *out_x = sh_ground(cell);
        if (child == NULL) { *out = rebuild_childless_x(n2); return 1; }
        kc_chain* dd = tree_repair_x(n2, child);
        if (dd == KC_NONE) return 0;
        *out = dd; return 1;
    }
    kc_sh cell; kc_chain* dp;
    if (!pop_raw_x(d, &cell, &dp)) return 0;
    if (!sh_is_ground(cell)) return 0;
    kc_chain* dd = repair_pop_side_x(dp);
    if (dd == KC_NONE) return 0;
    *out_x = sh_ground(cell); *out = dd; return 1;
}

static int cad_eject_x(kc_chain* d, kc_chain** out, kt_elem* out_x) {
    if (d == NULL) return 0;
    if (d->tag == CC_CELL) {
        kc_node n0; kc_chain* child;
        if (d->u.cell.body == NULL) { n0 = d->u.cell.node; child = d->u.cell.rest; }
        else child = root_and_child_x(d->u.cell.body, d->u.cell.node,
                                      d->u.cell.rest, &n0);
        kc_node n2; kc_sh cell;
        if (!node_eject_x(n0, &n2, &cell)) return 0;
        if (!sh_is_ground(cell)) return 0;
        if (child == NULL) { *out = rebuild_childless_x(n2); *out_x = sh_ground(cell); return 1; }
        kc_chain* dd = tree_repair_x(n2, child);
        if (dd == KC_NONE) return 0;
        *out = dd; *out_x = sh_ground(cell); return 1;
    }
    kc_chain* dp; kc_sh cell;
    if (!eject_raw_x(d, &dp, &cell)) return 0;
    if (!sh_is_ground(cell)) return 0;
    kc_chain* dd = repair_eject_side_x(dp);
    if (dd == KC_NONE) return 0;
    *out = dd; *out_x = sh_ground(cell); return 1;
}

/* ====================================================================== *
 * Sequence read (kc_to_list / kc_walk): mirror cchain_seq from Model.v.   *
 *   cnode_seq (Node _ p q) mid = buf(p) ++ mid ++ buf(q)                  *
 *   cbody_seq threads the inner through the preferred path                *
 *   stored_seq (SGround a)=[a]; (SSmall b)=buf(b); (SBig p c q)=...       *
 * Order matters; implemented as structured recursion (no continuations:  *
 * each node case emits pre, then the inner work inline, then suf). *)     *
 * ====================================================================== */

typedef struct { kc_walk_cb cb; void* ctx; } walk_env;

static void stored_emit(kc_sh s, walk_env* w);
static void chain_emit(kc_chain* c, walk_env* w);

/* emit every stored cell of a buffer, front to back */
static void buf_emit(kc_buf b, walk_env* w) {
    /* walk the §4 deque in order; each element is a kc_sh */
    void* x; kc_buf rest = b;
    while (cbuf_pop(rest, &x, &rest)) stored_emit((kc_sh)x, w);
}

static void stored_emit(kc_sh s, walk_env* w) {
    if (sh_is_ground(s)) { w->cb(sh_ground(s), w->ctx); return; }
    switch (sh_kind(s)) {
        case SK_SMALL:  buf_emit(sh_box(s)->u.small, w); break;
        case SK_BIG:
            buf_emit(sh_box(s)->u.big.p, w);
            chain_emit(sh_box(s)->u.big.c, w);
            buf_emit(sh_box(s)->u.big.q, w);
            break;
        default: assert(0);
    }
}

/* emit cbody_seq(body, cnode_seq(terminal, cchain_seq(rest))).
 * body==NULL means BHole: inner = cnode_seq(terminal, chain(rest)). */
static void body_emit(kc_body* body, kc_node terminal, kc_chain* rest,
                      walk_env* w) {
    if (body == NULL) {
        buf_emit(terminal.pre, w);
        chain_emit(rest, w);
        buf_emit(terminal.suf, w);
        return;
    }
    kc_node n = body->node;
    buf_emit(n.pre, w);
    switch (body->tag) {
        case CB_BSINGLE:
            body_emit(body->u.bsingle.body, terminal, rest, w);
            break;
        case CB_BPAIRY:
            body_emit(body->u.bpairy.body, terminal, rest, w);
            chain_emit(body->u.bpairy.rc, w);
            break;
        case CB_BPAIRO:
            chain_emit(body->u.bpairo.lc, w);
            body_emit(body->u.bpairo.body, terminal, rest, w);
            break;
        default: assert(0);
    }
    buf_emit(n.suf, w);
}

static void chain_emit(kc_chain* c, walk_env* w) {
    if (c == NULL) return;  /* FEmpty */
    switch (c->tag) {
        case CC_CELL:
            body_emit(c->u.cell.body, c->u.cell.node, c->u.cell.rest, w);
            break;
        case CC_PAIR:
            chain_emit(c->u.pair.left, w);
            chain_emit(c->u.pair.right, w);
            break;
        default: assert(0);
    }
}

/* ====================================================================== *
 * Public surface (Phase 1: empty + read; ops land in Phases 2-3).         *
 * ====================================================================== */

kc_cadeque kc_empty(void) { return (kc_cadeque)NULL; }  /* FEmpty */

kc_cadeque kc_push(kt_elem x, kc_cadeque d) {
    return (kc_cadeque)push_chain_x(mk_ground(x), (kc_chain*)d);
}

kc_cadeque kc_inject(kc_cadeque d, kt_elem x) {
    return (kc_cadeque)inject_chain_x((kc_chain*)d, mk_ground(x));
}

kc_cadeque kc_concat(kc_cadeque d, kc_cadeque e) {
    kc_chain* r = cad_concat_x((kc_chain*)d, (kc_chain*)e);
    assert(r != KC_NONE);  /* keystone: Some on regular inputs */
    return (kc_cadeque)r;
}

kc_cadeque kc_pop(kc_cadeque d, kt_elem* out, int* out_was_nonempty) {
    kt_elem x; kc_chain* r;
    if (cad_pop_x((kc_chain*)d, &x, &r)) {
        *out = x; *out_was_nonempty = 1; return (kc_cadeque)r;
    }
    /* on regular inputs, failure happens only for the empty deque */
    assert(d == NULL);
    *out_was_nonempty = 0; return d;
}

kc_cadeque kc_eject(kc_cadeque d, kt_elem* out, int* out_was_nonempty) {
    kt_elem x; kc_chain* r;
    if (cad_eject_x((kc_chain*)d, &r, &x)) {
        *out = x; *out_was_nonempty = 1; return (kc_cadeque)r;
    }
    assert(d == NULL);
    *out_was_nonempty = 0; return d;
}

void kc_walk(kc_cadeque d, kc_walk_cb cb, void* ctx) {
    walk_env w = { cb, ctx };
    chain_emit((kc_chain*)d, &w);
}

static void count_cb(kt_elem e, void* ctx) { (void)e; (*(size_t*)ctx)++; }

size_t kc_length(kc_cadeque d) {
    size_t n = 0;
    kc_walk(d, count_cb, &n);
    return n;
}

/* ====================================================================== *
 * Arena compaction: copy-forward all live §4 buffers (the §6 analogue of  *
 * kt_arena_compact).  Collect the address of every kc_buf.d field         *
 * reachable from the roots — outer node buffers plus the buffers nested   *
 * inside SSmall/SBig stored cells (recursively, and the SBig sub-chain)   *
 * — hand the §4-deque values to kt_arena_compact (which relocates them    *
 * and rewrites the array), then scatter the relocated pointers back into  *
 * the .d fields in place.  The §6 spine nodes (malloc) are not relocated; *
 * only their embedded §4 buffers move.                                    *
 * ====================================================================== */

typedef struct { kt_deque** a; size_t n, cap; } fldvec;
static void fv_add(fldvec* v, kt_deque* f) {
    if (v->n == v->cap) {
        v->cap = v->cap ? 2 * v->cap : 256;
        v->a = (kt_deque**)realloc(v->a, v->cap * sizeof(kt_deque*));
    }
    v->a[v->n++] = f;
}

static void collect_chain(kc_chain* c, fldvec* v);
static void collect_buf(kc_buf* b, fldvec* v);

static void collect_stored_cb(kt_elem e, void* ctx) {
    kc_sh s = (kc_sh)e;
    fldvec* v = (fldvec*)ctx;
    if (sh_is_ground(s)) return;
    switch (sh_kind(s)) {
        case SK_SMALL: collect_buf(&sh_box(s)->u.small, v); break;
        case SK_BIG:
            collect_buf(&sh_box(s)->u.big.p, v);
            collect_chain(sh_box(s)->u.big.c, v);
            collect_buf(&sh_box(s)->u.big.q, v);
            break;
        default: assert(0);
    }
}

static void collect_buf(kc_buf* b, fldvec* v) {
    fv_add(v, &b->d);
    /* recurse into the stored cells held by this buffer: nested §4
     * deques live there as "user data" the §4 compactor won't follow */
    kt_walk(b->d, collect_stored_cb, v);
}

static void collect_body(kc_body* b, fldvec* v) {
    if (b == NULL) return;  /* FHole: no node, no buffers */
    collect_buf(&b->node.pre, v);
    collect_buf(&b->node.suf, v);
    switch (b->tag) {
        case CB_BSINGLE: collect_body(b->u.bsingle.body, v); break;
        case CB_BPAIRY:
            collect_body(b->u.bpairy.body, v);
            collect_chain(b->u.bpairy.rc, v);
            break;
        case CB_BPAIRO:
            collect_chain(b->u.bpairo.lc, v);
            collect_body(b->u.bpairo.body, v);
            break;
        default: assert(0);
    }
}

static void collect_chain(kc_chain* c, fldvec* v) {
    if (c == NULL) return;
    if (c->tag == CC_CELL) {
        collect_buf(&c->u.cell.node.pre, v);
        collect_buf(&c->u.cell.node.suf, v);
        if (c->u.cell.body != NULL) collect_body(c->u.cell.body, v);
        collect_chain(c->u.cell.rest, v);
    } else {  /* CC_PAIR */
        collect_chain(c->u.pair.left, v);
        collect_chain(c->u.pair.right, v);
    }
}

size_t kc_arena_compact(kc_cadeque* roots, size_t n_roots) {
    fldvec v = { NULL, 0, 0 };
    for (size_t i = 0; i < n_roots; i++)
        collect_chain((kc_chain*)roots[i], &v);
    if (v.n == 0) { free(v.a); return 0; }
    kt_deque* vals = (kt_deque*)malloc(v.n * sizeof(kt_deque));
    for (size_t i = 0; i < v.n; i++) vals[i] = *v.a[i];
    size_t reclaimed = kt_arena_compact(vals, v.n);
    for (size_t i = 0; i < v.n; i++) *v.a[i] = vals[i];
    free(vals);
    free(v.a);
    return reclaimed;
}

/* ====================================================================== *
 * Phase-2 smoke test (compiled only under KC_PHASE2_SMOKE): push/inject/  *
 * concat against a plain dynamic-array oracle.                            *
 * ====================================================================== */
#if defined(KC_PHASE2_SMOKE) || defined(KC_PHASE3_SMOKE)
#include <stdio.h>

/* collect into a vector */
typedef struct { long* a; size_t n, cap; } vec;
static void vpush(vec* v, long x) {
    if (v->n == v->cap) { v->cap = v->cap ? 2*v->cap : 16;
        v->a = realloc(v->a, v->cap*sizeof(long)); }
    v->a[v->n++] = x;
}
static void collect_cb(kt_elem e, void* ctx) { vpush((vec*)ctx, ((long)(intptr_t)e>>3)); }
#endif  /* shared smoke helpers */

#ifdef KC_PHASE2_SMOKE
static int vec_eq(vec* v, long* exp, size_t n) {
    if (v->n != n) return 0;
    for (size_t i = 0; i < n; i++) if (v->a[i] != exp[i]) return 0;
    return 1;
}
#endif
#ifdef KC_PHASE2_SMOKE
static int check(const char* name, kc_cadeque d, long* exp, size_t n) {
    vec v = {0,0,0};
    kc_walk(d, collect_cb, &v);
    int ok = vec_eq(&v, exp, n);
    printf("%-28s len=%zu %s\n", name, v.n, ok ? "OK" : "*** FAIL ***");
    if (!ok) {
        printf("  got: "); for (size_t i=0;i<v.n;i++) printf("%ld ", v.a[i]);
        printf("\n  exp: "); for (size_t i=0;i<n;i++) printf("%ld ", exp[i]);
        printf("\n");
    }
    free(v.a);
    return ok;
}

int main(void) {
    int fails = 0;
    /* push 1..20 -> [20,19,...,1] */
    kc_cadeque d = kc_empty();
    for (int i = 1; i <= 20; i++) d = kc_push((kt_elem)(intptr_t)((long)i<<3), d);
    long exp1[20]; for (int i=0;i<20;i++) exp1[i] = 20-i;
    fails += !check("push 1..20", d, exp1, 20);

    /* inject 1..20 -> [1,2,...,20] */
    kc_cadeque e = kc_empty();
    for (int i = 1; i <= 20; i++) e = kc_inject(e, (kt_elem)(intptr_t)((long)i<<3));
    long exp2[20]; for (int i=0;i<20;i++) exp2[i] = i+1;
    fails += !check("inject 1..20", e, exp2, 20);

    /* concat: push-built [20..1] ++ inject-built [1..20] */
    kc_cadeque c = kc_concat(d, e);
    long exp3[40];
    for (int i=0;i<20;i++) exp3[i] = 20-i;
    for (int i=0;i<20;i++) exp3[20+i] = i+1;
    fails += !check("concat", c, exp3, 40);

    /* fold-concat: 64 blocks of 64 injected elements */
    kc_cadeque acc = kc_empty();
    long expf[64*64]; size_t fn = 0;
    for (int blk = 0; blk < 64; blk++) {
        kc_cadeque b = kc_empty();
        for (int i = 0; i < 64; i++) {
            long v = blk*64 + i;
            b = kc_inject(b, (kt_elem)(intptr_t)((long)v<<3));
            expf[fn++] = v;
        }
        acc = kc_concat(acc, b);
    }
    fails += !check("concat-fold 64x64", acc, expf, fn);

    printf(fails ? "SMOKE FAILED (%d)\n" : "ALL OK\n", fails);
    return fails ? 1 : 0;
}
#endif

#ifdef KC_PHASE3_SMOKE
/* Deterministic mixed workload (push/inject/pop/eject/concat) against a
 * doubly-ended array oracle.  Checks the full sequence after each op. */
typedef struct { long* a; size_t lo, hi, cap; } dq;  /* elements in [lo,hi) */
static dq dq_new(void) { dq d; d.cap=1024; d.a=malloc(d.cap*sizeof(long));
    d.lo=d.hi=d.cap/2; return d; }
static void dq_grow(dq* d) {
    size_t n=d->hi-d->lo, ncap=d->cap*4;
    long* na=malloc(ncap*sizeof(long));
    size_t nlo=ncap/2 - n/2;
    memcpy(na+nlo, d->a+d->lo, n*sizeof(long));
    free(d->a); d->a=na; d->cap=ncap; d->lo=nlo; d->hi=nlo+n;
}
static void dq_push(dq* d, long x){ if(d->lo==0) dq_grow(d); d->a[--d->lo]=x; }
static void dq_inject(dq* d, long x){ if(d->hi==d->cap) dq_grow(d); d->a[d->hi++]=x; }

static uint64_t xs;
static uint64_t xnext(void){ uint64_t x=xs; x^=x<<13; x^=x>>7; x^=x<<17; xs=x; return x; }

static int cmp_seq(kc_cadeque c, dq* o, const char* where) {
    vec v={0,0,0}; kc_walk(c, collect_cb, &v);
    size_t n=o->hi-o->lo;
    int ok = (v.n==n);
    for (size_t i=0; ok && i<n; i++) if (v.a[i]!=o->a[o->lo+i]) ok=0;
    if (!ok) {
        printf("MISMATCH at %s: clen=%zu olen=%zu\n", where, v.n, n);
        printf(" c: "); for(size_t i=0;i<v.n && i<30;i++) printf("%ld ",v.a[i]);
        printf("\n o: "); for(size_t i=0;i<n && i<30;i++) printf("%ld ",o->a[o->lo+i]);
        printf("\n");
    }
    free(v.a);
    return ok;
}

int main(int argc, char** argv) {
    long N = argc>1 ? atol(argv[1]) : 200000;
    xs = argc>2 ? strtoull(argv[2],0,16) : 0x9e3779b97f4a7c15ULL;
    long ctr = 1;

    /* single-deque mixed workload */
    kc_cadeque c = kc_empty();
    dq o = dq_new();
    for (long i=0;i<N;i++){
        int op = xnext()%4;
        if (op==0){ long x=ctr++; c=kc_push((kt_elem)(intptr_t)((long)x<<3),c); dq_push(&o,x); }
        else if (op==1){ long x=ctr++; c=kc_inject(c,(kt_elem)(intptr_t)((long)x<<3)); dq_inject(&o,x); }
        else if (op==2){ kt_elem e;int ok; c=kc_pop(c,&e,&ok);
            if (o.lo<o.hi){ assert(ok && ((long)(intptr_t)e>>3)==o.a[o.lo]); o.lo++; }
            else assert(!ok); }
        else { kt_elem e;int ok; c=kc_eject(c,&e,&ok);
            if (o.lo<o.hi){ assert(ok && ((long)(intptr_t)e>>3)==o.a[o.hi-1]); o.hi--; }
            else assert(!ok); }
    }
    int ok1 = cmp_seq(c, &o, "mixed-final");
    printf("mixed N=%ld: %s (len=%zu)\n", N, ok1?"OK":"FAIL", o.hi-o.lo);

    /* concat workload: build many blocks, concat-fold, then drain-check */
    kc_cadeque acc = kc_empty();
    dq oa = dq_new();
    for (int blk=0; blk<300; blk++){
        int blen = 1 + (int)(xnext()%40);
        kc_cadeque b = kc_empty();
        for (int i=0;i<blen;i++){ long x=ctr++;
            if (xnext()&1){ b=kc_push((kt_elem)(intptr_t)((long)x<<3),b);
                /* prepend to a temp then... easier: track via temp deque */ }
            else b=kc_inject(b,(kt_elem)(intptr_t)((long)x<<3));
        }
        /* recompute block's true sequence by walking b */
        vec bv={0,0,0}; kc_walk(b, collect_cb, &bv);
        if (xnext()&1){ acc=kc_concat(acc,b); for(size_t i=0;i<bv.n;i++) dq_inject(&oa,bv.a[i]); }
        else { acc=kc_concat(b,acc);
            /* prepend block before acc: shift — rebuild oa */
            dq no=dq_new(); for(size_t i=0;i<bv.n;i++) dq_inject(&no,bv.a[i]);
            for(size_t i=oa.lo;i<oa.hi;i++) dq_inject(&no,oa.a[i]);
            free(oa.a); oa=no; }
        free(bv.a);
    }
    int ok2 = cmp_seq(acc, &oa, "concat-final");
    printf("concat blocks: %s (len=%zu)\n", ok2?"OK":"FAIL", oa.hi-oa.lo);

    /* drain acc front and back alternately, checking each element */
    int ok3=1; size_t guard=0;
    while (acc != NULL) {
        kt_elem e; int ok;
        if (xnext()&1){ acc=kc_pop(acc,&e,&ok);
            if(!(ok && ((long)(intptr_t)e>>3)==oa.a[oa.lo])){ok3=0;break;} oa.lo++; }
        else { acc=kc_eject(acc,&e,&ok);
            if(!(ok && ((long)(intptr_t)e>>3)==oa.a[oa.hi-1])){ok3=0;break;} oa.hi--; }
        if (++guard > 1000000) { ok3=0; break; }
    }
    if (oa.lo!=oa.hi) ok3=0;
    printf("drain: %s\n", ok3?"OK":"FAIL");

    int fails = !ok1 + !ok2 + !ok3;
    printf(fails ? "PHASE3 FAILED (%d)\n" : "PHASE3 ALL OK\n", fails);
    return fails?1:0;
}
#endif
