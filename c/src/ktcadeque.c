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
 * Phase-1 smoke test (compiled only under KC_PHASE1_SMOKE).               *
 * ====================================================================== */
#ifdef KC_PHASE1_SMOKE
#include <stdio.h>
static void print_cb(kt_elem e, void* ctx) {
    (void)ctx; printf("%ld ", (long)(intptr_t)e);
}
int main(void) {
    /* empty reads [] */
    kc_cadeque e = kc_empty();
    printf("len(empty)=%zu\n", kc_length(e));

    /* hand-built singleton: FFlat KOnly [ground 7] [] FEmpty  -> [7] */
    kc_buf pre = cbuf_b1(mk_ground((kt_elem)(intptr_t)7));
    kc_chain* one = chain_flat(CK_ONLY, pre, cbuf_empty(), NULL);
    printf("len(one)=%zu seq= ", kc_length(one));
    kc_walk(one, print_cb, NULL); printf("\n");

    /* hand-built FFlat KOnly [g1;g2] [g3] FEmpty -> [1 2 3] */
    kc_buf p2 = cbuf_b2(mk_ground((kt_elem)(intptr_t)1),
                        mk_ground((kt_elem)(intptr_t)2));
    kc_buf s2 = cbuf_b1(mk_ground((kt_elem)(intptr_t)3));
    kc_chain* three = chain_flat(CK_ONLY, p2, s2, NULL);
    printf("len(three)=%zu seq= ", kc_length(three));
    kc_walk(three, print_cb, NULL); printf("\n");

    /* a pair of the two cells -> [7] ++ [1 2 3] = [7 1 2 3] */
    kc_chain* pr = chain_pair(one, three);
    printf("len(pair)=%zu seq= ", kc_length(pr));
    kc_walk(pr, print_cb, NULL); printf("\n");
    return 0;
}
#endif
