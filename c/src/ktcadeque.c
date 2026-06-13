/* ====================================================================== *
 * ktcadeque.c - KT99 §6 catenable deque, C port (Phase 1: foundations).   *
 * ====================================================================== *
 *
 * Mirrors rocq/KTDeque/Catenable/FlatChain.v + FlatOps.v branch for
 * branch.  Naming map (Rocq -> C):
 *
 *   fstored        -> kc_stored   (FGround/FSmall/FBig = SK_GROUND/SMALL/BIG)
 *   fnode          -> kc_node     (FNode k pre suf)
 *   fbody          -> kc_body     (FHole = NULL; FBSingle/FBPairY/FBPairO)
 *   fchain         -> kc_chain    (FEmpty/FFlat/FSingle/FPair)
 *   buffer (Buf5)  -> kc_buf      (size-tracked §4 deque, = OCaml Fastbuf)
 *
 * The §6 prefix/suffix buffers are §4 deques (ktdeque.h) storing
 * kc_stored* handles, exactly as the extracted OCaml artifact's buffers
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

/* ====================================================================== *
 * Size-tracked buffer (kc_buf) = §4 deque + O(1) element count.           *
 *                                                                          *
 * The §6 colour tests compare buffer sizes against the constants 5/6/7/8 *
 * on every operation, so an O(1) size is mandatory; the §4 deque only    *
 * offers O(N) kt_length.  This wrapper is the C analogue of the OCaml    *
 * Fastbuf's fused size field (DequePtr/SizedChain.v).                     *
 * ====================================================================== */

typedef struct {
    kt_deque d;   /* §4 deque of kc_stored* handles */
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
 * Stored cells (kc_stored): the uniform 2-word box.                       *
 *   SK_GROUND a       -> a user element                                   *
 *   SK_SMALL  b       -> one §6 buffer of stored cells                    *
 *   SK_BIG    p c q   -> buffer, chain, buffer                            *
 * ====================================================================== */

typedef struct kc_chain kc_chain;   /* forward */

enum { SK_GROUND = 0, SK_SMALL = 1, SK_BIG = 2 };

typedef struct kc_stored {
    uint8_t kind;
    union {
        kt_elem ground;
        kc_buf  small;
        struct { kc_buf p; kc_chain* c; kc_buf q; } big;
    } u;
} kc_stored;

static kc_stored* mk_ground(kt_elem a) {
    kc_stored* s = (kc_stored*)malloc(sizeof(kc_stored));
    s->kind = SK_GROUND; s->u.ground = a; return s;
}
static kc_stored* mk_small(kc_buf b) {
    kc_stored* s = (kc_stored*)malloc(sizeof(kc_stored));
    s->kind = SK_SMALL; s->u.small = b; return s;
}
static kc_stored* mk_big(kc_buf p, kc_chain* c, kc_buf q) {
    kc_stored* s = (kc_stored*)malloc(sizeof(kc_stored));
    s->kind = SK_BIG; s->u.big.p = p; s->u.big.c = c; s->u.big.q = q;
    return s;
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
    kc_body* r = (kc_body*)malloc(sizeof(kc_body));
    r->tag = CB_BSINGLE; r->node = n; r->u.bsingle.body = b; return r;
}
static kc_body* body_bpairy(kc_node n, kc_body* b, kc_chain* rc) {
    kc_body* r = (kc_body*)malloc(sizeof(kc_body));
    r->tag = CB_BPAIRY; r->node = n; r->u.bpairy.body = b; r->u.bpairy.rc = rc;
    return r;
}
static kc_body* body_bpairo(kc_node n, kc_chain* lc, kc_body* b) {
    kc_body* r = (kc_body*)malloc(sizeof(kc_body));
    r->tag = CB_BPAIRO; r->node = n; r->u.bpairo.lc = lc; r->u.bpairo.body = b;
    return r;
}

/* chain cell with explicit body (NULL = FFlat) */
static kc_chain* chain_cell(kc_body* body, kc_node node, kc_chain* rest) {
    kc_chain* c = (kc_chain*)malloc(sizeof(kc_chain));
    c->tag = CC_CELL;
    c->u.cell.body = body; c->u.cell.node = node; c->u.cell.rest = rest;
    return c;
}
/* FFlat k p s rest */
static kc_chain* chain_flat(uint8_t k, kc_buf p, kc_buf s, kc_chain* rest) {
    return chain_cell(NULL, node_make(k, p, s), rest);
}
static kc_chain* chain_pair(kc_chain* l, kc_chain* r) {
    kc_chain* c = (kc_chain*)malloc(sizeof(kc_chain));
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

static kc_node node_push_x(kc_stored* s, kc_node n) {
    if (cbuf_is_empty(n.pre))
        return node_make(n.k, n.pre, cbuf_push(s, n.suf));
    return node_make(n.k, cbuf_push(s, n.pre), n.suf);
}
static kc_node node_inject_x(kc_node n, kc_stored* s) {
    if (cbuf_is_empty(n.suf))
        return node_make(n.k, cbuf_inject(n.pre, s), n.suf);
    return node_make(n.k, n.pre, cbuf_inject(n.suf, s));
}

/* upd kind: 0 = push s ; 1 = inject s.  (No closures in C.) */
typedef struct { int op; kc_stored* s; } updspec;
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

static kc_chain* push_chain_x(kc_stored* s, kc_chain* c) {
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

static kc_chain* inject_chain_x(kc_chain* c, kc_stored* s) {
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
        acc = push_chain_x((kc_stored*)x, acc);
    return acc;
}
/* bfold_left inject_chain_x s d : inject each element of s onto d (leftmost
 * first). */
static kc_chain* fold_inject(kc_buf s, kc_chain* d) {
    kc_chain* acc = d;
    kc_buf rest = s; void* x;
    while (cbuf_pop(rest, &x, &rest))
        acc = inject_chain_x(acc, (kc_stored*)x);
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
 * Sequence read (kc_to_list / kc_walk): mirror cchain_seq from Model.v.   *
 *   cnode_seq (Node _ p q) mid = buf(p) ++ mid ++ buf(q)                  *
 *   cbody_seq threads the inner through the preferred path                *
 *   stored_seq (SGround a)=[a]; (SSmall b)=buf(b); (SBig p c q)=...       *
 * Order matters; implemented as structured recursion (no continuations:  *
 * each node case emits pre, then the inner work inline, then suf). *)     *
 * ====================================================================== */

typedef struct { kc_walk_cb cb; void* ctx; } walk_env;

static void stored_emit(kc_stored* s, walk_env* w);
static void chain_emit(kc_chain* c, walk_env* w);

/* emit every stored cell of a buffer, front to back */
static void buf_emit(kc_buf b, walk_env* w) {
    /* walk the §4 deque in order; each element is a kc_stored* */
    void* x; kc_buf rest = b;
    while (cbuf_pop(rest, &x, &rest)) stored_emit((kc_stored*)x, w);
}

static void stored_emit(kc_stored* s, walk_env* w) {
    switch (s->kind) {
        case SK_GROUND: w->cb(s->u.ground, w->ctx); break;
        case SK_SMALL:  buf_emit(s->u.small, w); break;
        case SK_BIG:
            buf_emit(s->u.big.p, w);
            chain_emit(s->u.big.c, w);
            buf_emit(s->u.big.q, w);
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
 * Phase-2 smoke test (compiled only under KC_PHASE2_SMOKE): push/inject/  *
 * concat against a plain dynamic-array oracle.                            *
 * ====================================================================== */
#ifdef KC_PHASE2_SMOKE
#include <stdio.h>

/* collect into a vector */
typedef struct { long* a; size_t n, cap; } vec;
static void vpush(vec* v, long x) {
    if (v->n == v->cap) { v->cap = v->cap ? 2*v->cap : 16;
        v->a = realloc(v->a, v->cap*sizeof(long)); }
    v->a[v->n++] = x;
}
static void collect_cb(kt_elem e, void* ctx) { vpush((vec*)ctx, (long)(intptr_t)e); }
static int vec_eq(vec* v, long* exp, size_t n) {
    if (v->n != n) return 0;
    for (size_t i = 0; i < n; i++) if (v->a[i] != exp[i]) return 0;
    return 1;
}
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
    for (int i = 1; i <= 20; i++) d = kc_push((kt_elem)(intptr_t)i, d);
    long exp1[20]; for (int i=0;i<20;i++) exp1[i] = 20-i;
    fails += !check("push 1..20", d, exp1, 20);

    /* inject 1..20 -> [1,2,...,20] */
    kc_cadeque e = kc_empty();
    for (int i = 1; i <= 20; i++) e = kc_inject(e, (kt_elem)(intptr_t)i);
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
            b = kc_inject(b, (kt_elem)(intptr_t)v);
            expf[fn++] = v;
        }
        acc = kc_concat(acc, b);
    }
    fails += !check("concat-fold 64x64", acc, expf, fn);

    printf(fails ? "SMOKE FAILED (%d)\n" : "ALL OK\n", fails);
    return fails ? 1 : 0;
}
#endif
