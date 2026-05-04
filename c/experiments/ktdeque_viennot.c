/* ktdeque.c — Section-4 deque with worst-case O(1) per op.
 *
 * Translation of Viennot/VWGP's GADT (bench/viennot/deque_core.ml) into C
 * with tagged-pointer chain encoding.  Algorithmic structure: KT99 §4.1
 * stack-of-substacks (a.k.a. packets-and-chains).
 *
 *   chain  ::= Ending(buffer)            -- low bit 1 of kt_chain
 *            | Chain(reg, packet, chain) -- low bit 0 of kt_chain (-> kt_link*)
 *   packet ::= Hole                      -- pkt = NULL
 *            | Packet(buffer, packet, buffer)   -- nested yellow inside one
 *                                                    chain link's packet field
 *
 * Color tag encoding (in low 2 bits of kt_link.packet pointer):
 *   00 = green (G), 01 = yellow (Y), 10 = red (R)
 *
 * Worst-case-O(1):
 *   - push/inject/pop/eject touch only the topmost chain link's outer buffer
 *     (Hole or yellow nested packet's outer buffer), then call ensure_green
 *     on the *following* chain link.
 *   - ensure_green is identity on green / Ending links, and runs green_of_red
 *     on a red link.  green_of_red rewires at most the one red link plus its
 *     immediate successor (or, if the successor is Ending, runs make_small on
 *     just the red link's contents).
 *   - The regularity invariant `(R | Y) -> G` ensures green_of_red's
 *     successor is always green: a single bounded chain rewrite, no cascade.
 */

#include "ktdeque.h"

#include <stdlib.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>

/* ===================================================================== */
/* Buffers — variable-size, stored as { size, e[size] }                  */
/* ===================================================================== */

/* A buffer is a heap object holding 0..5 elements.  We allocate a single
 * struct of size sizeof(kt_buf) since elements are 0..5; the size field tells
 * us how many are valid. */
typedef struct kt_buf {
    uint32_t size;            /* 0..5 */
    kt_elem  e[5];
} kt_buf;

/* ===================================================================== */
/* Packets — recursive structure                                          */
/* ===================================================================== */

/* A packet (Viennot's `('a, 'b, c) packet`) is either Hole (= NULL) or a
 * triple (prefix, inner_packet, suffix) where inner_packet is a yellow
 * packet (or Hole).  The outer chain link's regularity tag (G/Y/R) is the
 * color of the *outer* buffers prefix and suffix; inner packets are always
 * yellow. */
typedef struct kt_packet {
    kt_buf*           pre;
    struct kt_packet* inner;   /* NULL = Hole */
    kt_buf*           suf;
} kt_packet;

/* ===================================================================== */
/* Chains — alternating G/Y/R, with regularity Y->G and R->G              */
/* ===================================================================== */

/* Color/regularity tags. */
typedef enum { CG = 0, CY = 1, CR = 2 } kt_col;

/* A chain link.  `packet` is a tagged pointer:
 *   low 2 bits = color tag (CG | CY | CR)
 *   upper bits = pointer to kt_packet
 * `next` is a tagged kt_chain pointer (low bit = ending? — see below). */
typedef struct kt_link {
    uintptr_t   packet_tagged;
    void*       next_chain;     /* tagged: low bit 0 = kt_link*, 1 = ending kt_buf* */
} kt_link;

/* kt_chain encoding helpers.  A kt_chain (= void*) is either:
 *   - low bit 1 -> pointer to kt_buf (ending), with bit cleared
 *   - low bit 0 -> pointer to kt_link, used as-is */

#define CHAIN_TAG_ENDING    1u

static inline int chain_is_ending(void* c) { return ((uintptr_t)c & 1u) != 0; }
static inline kt_buf* chain_ending_buf(void* c) {
    return (kt_buf*)((uintptr_t)c & ~(uintptr_t)1u);
}
static inline void* chain_make_ending(kt_buf* b) {
    return (void*)((uintptr_t)b | CHAIN_TAG_ENDING);
}
static inline kt_link* chain_link(void* c) {
    /* c is not ending */
    return (kt_link*)c;
}
static inline void* chain_make_link(kt_link* l) { return (void*)l; }

/* link.packet_tagged helpers. */
#define PKT_COL_MASK  ((uintptr_t)0x3)
static inline kt_packet* link_packet(const kt_link* l) {
    return (kt_packet*)(l->packet_tagged & ~PKT_COL_MASK);
}
static inline kt_col link_col(const kt_link* l) {
    return (kt_col)(l->packet_tagged & PKT_COL_MASK);
}
static inline uintptr_t make_tagged_packet(kt_packet* p, kt_col c) {
    return (uintptr_t)p | (uintptr_t)c;
}

/* ===================================================================== */
/* Bump arena allocators                                                   */
/* ===================================================================== */

#define REGION_CHUNK  (8 * 1024 * 1024)

static char* link_top  = NULL; static char* link_end  = NULL;
static char* pkt_top   = NULL; static char* pkt_end   = NULL;
static char* buf_top   = NULL; static char* buf_end   = NULL;
static char* pair_top  = NULL; static char* pair_end  = NULL;

#ifdef KT_PROFILE
static size_t total_links = 0;
static size_t total_pkts  = 0;
static size_t total_bufs  = 0;
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

static inline kt_link* alloc_link(void) {
#ifdef KT_PROFILE
    total_links++;
#endif
    return (kt_link*)region_bump(&link_top, &link_end, sizeof(kt_link));
}

static inline kt_packet* alloc_packet(void) {
#ifdef KT_PROFILE
    total_pkts++;
#endif
    return (kt_packet*)region_bump(&pkt_top, &pkt_end, sizeof(kt_packet));
}

static inline kt_buf* alloc_buf_raw(void) {
#ifdef KT_PROFILE
    total_bufs++;
#endif
    return (kt_buf*)region_bump(&buf_top, &buf_end, sizeof(kt_buf));
}

static inline kt_pair* alloc_pair(void) {
#ifdef KT_PROFILE
    total_pairs++;
#endif
    return (kt_pair*)region_bump(&pair_top, &pair_end, sizeof(kt_pair));
}

#ifdef KT_PROFILE
size_t kt_alloc_packets(void) { return total_pkts; }
size_t kt_alloc_chains(void)  { return total_links; }
size_t kt_alloc_pairs(void)   { return total_pairs; }
size_t kt_alloc_bufs(void)    { return total_bufs; }
void   kt_reset_alloc_counters(void) {
    total_links = total_pkts = total_bufs = total_pairs = 0;
}
#else
size_t kt_alloc_packets(void) { return 0; }
size_t kt_alloc_chains(void)  { return 0; }
size_t kt_alloc_pairs(void)   { return 0; }
size_t kt_alloc_bufs(void)    { return 0; }
void   kt_reset_alloc_counters(void) {}
#endif

/* ===================================================================== */
/* Pair helpers                                                           */
/* ===================================================================== */

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

static inline kt_elem pair_make(kt_elem x, kt_elem y) {
    return kt_pair_make(x, y);
}
static inline void pair_split(kt_elem e, kt_elem* x, kt_elem* y) {
    kt_pair* p = (kt_pair*)e;
    *x = p->left;
    *y = p->right;
}

/* ===================================================================== */
/* Buffer constructors                                                    */
/* ===================================================================== */

static inline kt_buf* mk_buf0(void) {
    kt_buf* b = alloc_buf_raw(); b->size = 0; return b;
}
static inline kt_buf* mk_buf1(kt_elem a) {
    kt_buf* b = alloc_buf_raw(); b->size = 1; b->e[0] = a; return b;
}
static inline kt_buf* mk_buf2(kt_elem a, kt_elem b) {
    kt_buf* r = alloc_buf_raw(); r->size = 2; r->e[0] = a; r->e[1] = b; return r;
}
static inline kt_buf* mk_buf3(kt_elem a, kt_elem b, kt_elem c) {
    kt_buf* r = alloc_buf_raw(); r->size = 3;
    r->e[0] = a; r->e[1] = b; r->e[2] = c; return r;
}
static inline kt_buf* mk_buf4(kt_elem a, kt_elem b, kt_elem c, kt_elem d) {
    kt_buf* r = alloc_buf_raw(); r->size = 4;
    r->e[0] = a; r->e[1] = b; r->e[2] = c; r->e[3] = d; return r;
}
static inline kt_buf* mk_buf5(kt_elem a, kt_elem b, kt_elem c, kt_elem d, kt_elem e) {
    kt_buf* r = alloc_buf_raw(); r->size = 5;
    r->e[0] = a; r->e[1] = b; r->e[2] = c; r->e[3] = d; r->e[4] = e; return r;
}

/* Color of a buffer by its size (KT99 §4.1):
 *   B0, B5 -> red ; B1, B4 -> yellow ; B2, B3 -> green. */
static inline kt_col buf_col(const kt_buf* b) {
    switch (b->size) {
    case 0: case 5: return CR;
    case 1: case 4: return CY;
    default:        return CG;
    }
}

/* Outer-link color: max of pre and suf colors (manual §5.5). */
static inline kt_col link_col_of_bufs(const kt_buf* p, const kt_buf* s) {
    kt_col cp = buf_col(p);
    kt_col cs = buf_col(s);
    return cp > cs ? cp : cs;
}

/* ===================================================================== */
/* Buffer ops (push/inject/pop/eject) — return new buffers                */
/* ===================================================================== */

/* Push x onto the left of b.  b->size must be < 5. */
static inline kt_buf* buf_push(kt_elem x, const kt_buf* b) {
    kt_buf* r = alloc_buf_raw();
    r->size = b->size + 1;
    r->e[0] = x;
    for (uint32_t i = 0; i < b->size; i++) r->e[i+1] = b->e[i];
    return r;
}

/* Inject x onto the right of b.  b->size must be < 5. */
static inline kt_buf* buf_inject(const kt_buf* b, kt_elem x) {
    kt_buf* r = alloc_buf_raw();
    r->size = b->size + 1;
    for (uint32_t i = 0; i < b->size; i++) r->e[i] = b->e[i];
    r->e[b->size] = x;
    return r;
}

/* Pop from left of b — b->size > 0. Returns new buf and writes element. */
static inline kt_buf* buf_pop(const kt_buf* b, kt_elem* out) {
    *out = b->e[0];
    kt_buf* r = alloc_buf_raw();
    r->size = b->size - 1;
    for (uint32_t i = 0; i < r->size; i++) r->e[i] = b->e[i+1];
    return r;
}

/* Eject from right of b — b->size > 0. */
static inline kt_buf* buf_eject(const kt_buf* b, kt_elem* out) {
    *out = b->e[b->size - 1];
    kt_buf* r = alloc_buf_raw();
    r->size = b->size - 1;
    for (uint32_t i = 0; i < r->size; i++) r->e[i] = b->e[i];
    return r;
}

/* ===================================================================== */
/* Higher-order buffer transformations (Viennot deque_core.ml)           */
/* ===================================================================== */

/* Buffer push that may overflow: returns a new green chain.  Equivalent to
 * Viennot's buffer_push.  When b is B5, allocates a brand-new chain link.
 * Returns a kt_chain (tagged). */
static void* buffer_push_chain(kt_elem x, const kt_buf* b) {
    if (b->size < 5) {
        return chain_make_ending(buf_push(x, b));
    }
    /* B5: split into B3(x,a,b), pkt-hole, B3(c,d,e), Ending B0. */
    kt_buf* p1 = mk_buf3(x, b->e[0], b->e[1]);
    kt_buf* s1 = mk_buf3(b->e[2], b->e[3], b->e[4]);
    kt_packet* pkt = alloc_packet();
    pkt->pre = p1; pkt->inner = NULL; pkt->suf = s1;
    kt_link* lnk = alloc_link();
    lnk->packet_tagged = make_tagged_packet(pkt, CG);
    lnk->next_chain    = chain_make_ending(mk_buf0());
    return chain_make_link(lnk);
}

static void* buffer_inject_chain(const kt_buf* b, kt_elem x) {
    if (b->size < 5) {
        return chain_make_ending(buf_inject(b, x));
    }
    kt_buf* p1 = mk_buf3(b->e[0], b->e[1], b->e[2]);
    kt_buf* s1 = mk_buf3(b->e[3], b->e[4], x);
    kt_packet* pkt = alloc_packet();
    pkt->pre = p1; pkt->inner = NULL; pkt->suf = s1;
    kt_link* lnk = alloc_link();
    lnk->packet_tagged = make_tagged_packet(pkt, CG);
    lnk->next_chain    = chain_make_ending(mk_buf0());
    return chain_make_link(lnk);
}

/* ===================================================================== */
/* Decompose helpers (Viennot's prefix_decompose / suffix_decompose)      */
/* ===================================================================== */

typedef enum { DEC_UNDERFLOW, DEC_OK, DEC_OVERFLOW } dec_kind;

typedef struct {
    dec_kind kind;
    /* Underflow: opt may be present (size 1) or absent (size 0). */
    int      opt_present;
    kt_elem  opt;
    /* Ok: green buffer (size 2 or 3). */
    /* Overflow: green buffer + a pair (xy.left, xy.right). */
    kt_buf*  green_buf;
    kt_elem  pair_x, pair_y;   /* for Overflow */
} decomp;

/* prefix_decompose: B4/B5 -> Overflow (last 2 elements paired). */
static decomp prefix_decompose(const kt_buf* b) {
    decomp r;
    switch (b->size) {
    case 0:
        r.kind = DEC_UNDERFLOW; r.opt_present = 0; break;
    case 1:
        r.kind = DEC_UNDERFLOW; r.opt_present = 1; r.opt = b->e[0]; break;
    case 2: case 3:
        r.kind = DEC_OK; r.green_buf = (kt_buf*)b; break;
    case 4:
        r.kind = DEC_OVERFLOW;
        r.green_buf = mk_buf2(b->e[0], b->e[1]);
        r.pair_x = b->e[2]; r.pair_y = b->e[3];
        break;
    case 5:
        r.kind = DEC_OVERFLOW;
        r.green_buf = mk_buf3(b->e[0], b->e[1], b->e[2]);
        r.pair_x = b->e[3]; r.pair_y = b->e[4];
        break;
    default:
        assert(0); r.kind = DEC_OK; r.green_buf = NULL;
    }
    return r;
}

/* suffix_decompose: B4/B5 -> Overflow (FIRST 2 elements paired). */
static decomp suffix_decompose(const kt_buf* b) {
    decomp r;
    switch (b->size) {
    case 0:
        r.kind = DEC_UNDERFLOW; r.opt_present = 0; break;
    case 1:
        r.kind = DEC_UNDERFLOW; r.opt_present = 1; r.opt = b->e[0]; break;
    case 2: case 3:
        r.kind = DEC_OK; r.green_buf = (kt_buf*)b; break;
    case 4:
        r.kind = DEC_OVERFLOW;
        r.green_buf = mk_buf2(b->e[2], b->e[3]);
        r.pair_x = b->e[0]; r.pair_y = b->e[1];
        break;
    case 5:
        r.kind = DEC_OVERFLOW;
        r.green_buf = mk_buf3(b->e[2], b->e[3], b->e[4]);
        r.pair_x = b->e[0]; r.pair_y = b->e[1];
        break;
    default:
        assert(0); r.kind = DEC_OK; r.green_buf = NULL;
    }
    return r;
}

/* prefix23 opt (b, c) -> B2 or B3 */
static kt_buf* prefix23(int opt_present, kt_elem opt, kt_elem b, kt_elem c) {
    return opt_present ? mk_buf3(opt, b, c) : mk_buf2(b, c);
}

/* suffix23 (a, b) opt -> B2 or B3 */
static kt_buf* suffix23(kt_elem a, kt_elem b, int opt_present, kt_elem opt) {
    return opt_present ? mk_buf3(a, b, opt) : mk_buf2(a, b);
}

/* suffix12 x opt -> B1 or B2 */
static kt_buf* suffix12(kt_elem x, int opt_present, kt_elem opt) {
    return opt_present ? mk_buf2(x, opt) : mk_buf1(x);
}

/* ===================================================================== */
/* Sandwich (Viennot's buffer_unsandwich)                                 */
/* ===================================================================== */

typedef struct {
    int     is_alone;         /* 1 = alone, 0 = sandwich */
    /* Alone case: optional element. */
    int     alone_present;
    kt_elem alone;
    /* Sandwich case: x, middle buffer (0..3), y. */
    kt_elem x, y;
    kt_buf* mid;
} sandwich;

static sandwich buffer_unsandwich(const kt_buf* b) {
    sandwich r;
    switch (b->size) {
    case 0:
        r.is_alone = 1; r.alone_present = 0; break;
    case 1:
        r.is_alone = 1; r.alone_present = 1; r.alone = b->e[0]; break;
    case 2:
        r.is_alone = 0; r.x = b->e[0]; r.mid = mk_buf0(); r.y = b->e[1]; break;
    case 3:
        r.is_alone = 0; r.x = b->e[0]; r.mid = mk_buf1(b->e[1]); r.y = b->e[2]; break;
    case 4:
        r.is_alone = 0; r.x = b->e[0]; r.mid = mk_buf2(b->e[1], b->e[2]);
        r.y = b->e[3]; break;
    case 5:
        r.is_alone = 0; r.x = b->e[0]; r.mid = mk_buf3(b->e[1], b->e[2], b->e[3]);
        r.y = b->e[4]; break;
    default:
        assert(0); r.is_alone = 1; r.alone_present = 0;
    }
    return r;
}

/* ===================================================================== */
/* buffer_halve: convert a buffer of A's into a buffer of pairs of A's.   */
/* ===================================================================== */

typedef struct {
    int      opt_present;     /* a leftover odd element? */
    kt_elem  opt;
    kt_buf*  pairs;           /* pairs are kt_pair*; stored as kt_elem[] */
} halve_result;

static halve_result buffer_halve(const kt_buf* b) {
    halve_result r;
    switch (b->size) {
    case 0:
        r.opt_present = 0; r.pairs = mk_buf0(); break;
    case 1:
        r.opt_present = 1; r.opt = b->e[0]; r.pairs = mk_buf0(); break;
    case 2:
        r.opt_present = 0;
        r.pairs = mk_buf1(pair_make(b->e[0], b->e[1])); break;
    case 3:
        r.opt_present = 1; r.opt = b->e[0];
        r.pairs = mk_buf1(pair_make(b->e[1], b->e[2])); break;
    case 4:
        r.opt_present = 0;
        r.pairs = mk_buf2(pair_make(b->e[0], b->e[1]),
                          pair_make(b->e[2], b->e[3])); break;
    case 5:
        r.opt_present = 1; r.opt = b->e[0];
        r.pairs = mk_buf2(pair_make(b->e[1], b->e[2]),
                          pair_make(b->e[3], b->e[4])); break;
    default:
        assert(0); r.opt_present = 0; r.pairs = mk_buf0();
    }
    return r;
}

/* ===================================================================== */
/* Rotations: prefix_rot / suffix_rot                                     */
/* ===================================================================== */

/* prefix_rot x b -> (b', y) where b' has the same size as b, x is pushed,
 * the rightmost was ejected as y. */
typedef struct { kt_buf* buf; kt_elem yielded; } rot_result;

static rot_result prefix_rot(kt_elem x, const kt_buf* b) {
    rot_result r;
    switch (b->size) {
    case 0:
        r.buf = mk_buf0(); r.yielded = x; break;
    case 1:
        r.buf = mk_buf1(x); r.yielded = b->e[0]; break;
    case 2:
        r.buf = mk_buf2(x, b->e[0]); r.yielded = b->e[1]; break;
    case 3:
        r.buf = mk_buf3(x, b->e[0], b->e[1]); r.yielded = b->e[2]; break;
    case 4:
        r.buf = mk_buf4(x, b->e[0], b->e[1], b->e[2]); r.yielded = b->e[3]; break;
    case 5:
        r.buf = mk_buf5(x, b->e[0], b->e[1], b->e[2], b->e[3]);
        r.yielded = b->e[4]; break;
    default: assert(0); r.buf = NULL; r.yielded = NULL;
    }
    return r;
}

/* suffix_rot b x -> (y, b') where b' has the same size as b, x is injected,
 * the leftmost was popped as y. */
static rot_result suffix_rot(const kt_buf* b, kt_elem x) {
    rot_result r;
    switch (b->size) {
    case 0:
        r.yielded = x; r.buf = mk_buf0(); break;
    case 1:
        r.yielded = b->e[0]; r.buf = mk_buf1(x); break;
    case 2:
        r.yielded = b->e[0]; r.buf = mk_buf2(b->e[1], x); break;
    case 3:
        r.yielded = b->e[0]; r.buf = mk_buf3(b->e[1], b->e[2], x); break;
    case 4:
        r.yielded = b->e[0]; r.buf = mk_buf4(b->e[1], b->e[2], b->e[3], x); break;
    case 5:
        r.yielded = b->e[0];
        r.buf = mk_buf5(b->e[1], b->e[2], b->e[3], b->e[4], x); break;
    default: assert(0); r.buf = NULL; r.yielded = NULL;
    }
    return r;
}

/* ===================================================================== */
/* make_small (Viennot deque_core.ml line 345) — handle small chain      */
/* ===================================================================== */

/* Inputs: prefix p1, child buffer b2, suffix s1.  Returns a green chain. */
static void* make_small(const kt_buf* p1, const kt_buf* b2, const kt_buf* s1) {
    decomp dp = prefix_decompose(p1);
    decomp ds = suffix_decompose(s1);

    if (dp.kind == DEC_UNDERFLOW && ds.kind == DEC_UNDERFLOW) {
        sandwich sw = buffer_unsandwich(b2);
        if (sw.is_alone) {
            /* Combine p1.opt, sw.alone (a pair), s1.opt -> 0..4 elements. */
            kt_buf* result;
            int p_present = dp.opt_present, s_present = ds.opt_present;
            if (sw.alone_present) {
                kt_elem ax, ay;
                pair_split(sw.alone, &ax, &ay);
                if (p_present && s_present) {
                    /* p, ax, ay, s -> B4 */
                    result = mk_buf4(dp.opt, ax, ay, ds.opt);
                } else if (p_present) {
                    /* p, ax, ay -> B3 */
                    result = mk_buf3(dp.opt, ax, ay);
                } else if (s_present) {
                    /* ax, ay, s -> B3 */
                    result = mk_buf3(ax, ay, ds.opt);
                } else {
                    /* ax, ay -> B2 */
                    result = mk_buf2(ax, ay);
                }
            } else {
                if (p_present && s_present) {
                    result = mk_buf2(dp.opt, ds.opt);
                } else if (p_present) {
                    result = mk_buf1(dp.opt);
                } else if (s_present) {
                    result = mk_buf1(ds.opt);
                } else {
                    result = mk_buf0();
                }
            }
            return chain_make_ending(result);
        } else {
            /* Sandwich (ab, rest, cd) — ab and cd are pairs of A's.  rest is
             * the pair-buffer.  Build:
             *   Chain(G, Packet(prefix23 p1 ab, Hole, suffix23 cd s1),
             *         Ending rest) */
            kt_elem ab_x, ab_y, cd_x, cd_y;
            pair_split(sw.x, &ab_x, &ab_y);
            pair_split(sw.y, &cd_x, &cd_y);
            kt_buf* new_pre = prefix23(dp.opt_present, dp.opt, ab_x, ab_y);
            kt_buf* new_suf = suffix23(cd_x, cd_y, ds.opt_present, ds.opt);
            kt_packet* pkt = alloc_packet();
            pkt->pre = new_pre; pkt->inner = NULL; pkt->suf = new_suf;
            kt_link* lnk = alloc_link();
            lnk->packet_tagged = make_tagged_packet(pkt, CG);
            lnk->next_chain    = chain_make_ending(sw.mid);
            return chain_make_link(lnk);
        }
    }

    if (dp.kind == DEC_UNDERFLOW && ds.kind == DEC_OK) {
        /* | Underflow p1, Ok s1 -> match buffer_pop b2, p1 with ... */
        if (b2->size == 0) {
            if (!dp.opt_present) {
                return chain_make_ending(ds.green_buf);
            } else {
                return buffer_push_chain(dp.opt, ds.green_buf);
            }
        } else {
            /* buffer_pop b2 = Some (cd, rest) — cd is a level-(i+1) pair */
            kt_elem cd; kt_buf* rest = buf_pop(b2, &cd);
            kt_elem cd_x, cd_y; pair_split(cd, &cd_x, &cd_y);
            kt_buf* new_pre = prefix23(dp.opt_present, dp.opt, cd_x, cd_y);
            kt_packet* pkt = alloc_packet();
            pkt->pre = new_pre; pkt->inner = NULL; pkt->suf = ds.green_buf;
            kt_link* lnk = alloc_link();
            lnk->packet_tagged = make_tagged_packet(pkt, CG);
            lnk->next_chain    = chain_make_ending(rest);
            return chain_make_link(lnk);
        }
    }

    if (dp.kind == DEC_UNDERFLOW && ds.kind == DEC_OVERFLOW) {
        /* | Underflow p1, Overflow (s1, ab) ->
         *     let cd, center = suffix_rot b2 ab in
         *     Chain(G, Packet(prefix23 p1 cd, Hole, s1), Ending center) */
        kt_elem ab = pair_make(ds.pair_x, ds.pair_y);
        rot_result rr = suffix_rot(b2, ab);
        kt_elem cd_x, cd_y; pair_split(rr.yielded, &cd_x, &cd_y);
        kt_buf* new_pre = prefix23(dp.opt_present, dp.opt, cd_x, cd_y);
        kt_packet* pkt = alloc_packet();
        pkt->pre = new_pre; pkt->inner = NULL; pkt->suf = ds.green_buf;
        kt_link* lnk = alloc_link();
        lnk->packet_tagged = make_tagged_packet(pkt, CG);
        lnk->next_chain    = chain_make_ending(rr.buf);
        return chain_make_link(lnk);
    }

    if (dp.kind == DEC_OK && ds.kind == DEC_UNDERFLOW) {
        if (b2->size == 0) {
            if (!ds.opt_present) {
                return chain_make_ending(dp.green_buf);
            } else {
                return buffer_inject_chain(dp.green_buf, ds.opt);
            }
        } else {
            kt_elem ab; kt_buf* rest = buf_eject(b2, &ab);
            kt_elem ab_x, ab_y; pair_split(ab, &ab_x, &ab_y);
            kt_buf* new_suf = suffix23(ab_x, ab_y, ds.opt_present, ds.opt);
            kt_packet* pkt = alloc_packet();
            pkt->pre = dp.green_buf; pkt->inner = NULL; pkt->suf = new_suf;
            kt_link* lnk = alloc_link();
            lnk->packet_tagged = make_tagged_packet(pkt, CG);
            lnk->next_chain    = chain_make_ending(rest);
            return chain_make_link(lnk);
        }
    }

    if (dp.kind == DEC_OK && ds.kind == DEC_OK) {
        kt_packet* pkt = alloc_packet();
        pkt->pre = dp.green_buf; pkt->inner = NULL; pkt->suf = ds.green_buf;
        kt_link* lnk = alloc_link();
        lnk->packet_tagged = make_tagged_packet(pkt, CG);
        /* Ending b2 — b2 is a buffer of pairs.  We re-use the buffer pointer. */
        lnk->next_chain    = chain_make_ending((kt_buf*)b2);
        return chain_make_link(lnk);
    }

    if (dp.kind == DEC_OK && ds.kind == DEC_OVERFLOW) {
        /* let c2 = buffer_inject b2 ab in
         * Chain(G, Packet(p1, Hole, s1), c2) */
        kt_elem ab = pair_make(ds.pair_x, ds.pair_y);
        void* c2 = buffer_inject_chain(b2, ab);
        kt_packet* pkt = alloc_packet();
        pkt->pre = dp.green_buf; pkt->inner = NULL; pkt->suf = ds.green_buf;
        kt_link* lnk = alloc_link();
        lnk->packet_tagged = make_tagged_packet(pkt, CG);
        lnk->next_chain    = c2;
        return chain_make_link(lnk);
    }

    if (dp.kind == DEC_OVERFLOW && ds.kind == DEC_UNDERFLOW) {
        kt_elem cd = pair_make(dp.pair_x, dp.pair_y);
        rot_result rr = prefix_rot(cd, b2);
        kt_elem ab_x, ab_y; pair_split(rr.yielded, &ab_x, &ab_y);
        kt_buf* new_suf = suffix23(ab_x, ab_y, ds.opt_present, ds.opt);
        kt_packet* pkt = alloc_packet();
        pkt->pre = dp.green_buf; pkt->inner = NULL; pkt->suf = new_suf;
        kt_link* lnk = alloc_link();
        lnk->packet_tagged = make_tagged_packet(pkt, CG);
        lnk->next_chain    = chain_make_ending(rr.buf);
        return chain_make_link(lnk);
    }

    if (dp.kind == DEC_OVERFLOW && ds.kind == DEC_OK) {
        kt_elem cd = pair_make(dp.pair_x, dp.pair_y);
        void* c2 = buffer_push_chain(cd, b2);
        kt_packet* pkt = alloc_packet();
        pkt->pre = dp.green_buf; pkt->inner = NULL; pkt->suf = ds.green_buf;
        kt_link* lnk = alloc_link();
        lnk->packet_tagged = make_tagged_packet(pkt, CG);
        lnk->next_chain    = c2;
        return chain_make_link(lnk);
    }

    /* Both Overflow. */
    {
        /* let x, rest = buffer_halve b2 in
         * let p2 = suffix12 cd x in
         * Chain(G, Packet(p1, Packet(p2, Hole, B1 ab), s1), Ending rest) */
        halve_result hr = buffer_halve(b2);
        kt_elem cd = pair_make(dp.pair_x, dp.pair_y);
        kt_elem ab = pair_make(ds.pair_x, ds.pair_y);
        kt_buf* p2 = suffix12(cd, hr.opt_present, hr.opt);
        kt_buf* s2_inner = mk_buf1(ab);
        kt_packet* inner_pkt = alloc_packet();
        inner_pkt->pre = p2; inner_pkt->inner = NULL; inner_pkt->suf = s2_inner;
        kt_packet* outer_pkt = alloc_packet();
        outer_pkt->pre = dp.green_buf;
        outer_pkt->inner = inner_pkt;
        outer_pkt->suf = ds.green_buf;
        kt_link* lnk = alloc_link();
        lnk->packet_tagged = make_tagged_packet(outer_pkt, CG);
        lnk->next_chain    = chain_make_ending(hr.pairs);
        return chain_make_link(lnk);
    }
}

/* ===================================================================== */
/* Yellow / red buffer ops                                                */
/* ===================================================================== */

/* Yellow push: B1..B4 -> B2..B5 (note: B5 is red). */
static inline kt_buf* yellow_push(kt_elem x, const kt_buf* b) {
    return buf_push(x, b);
}
static inline kt_buf* yellow_inject(const kt_buf* b, kt_elem x) {
    return buf_inject(b, x);
}
static inline kt_buf* yellow_pop(const kt_buf* b, kt_elem* out) {
    return buf_pop(b, out);
}
static inline kt_buf* yellow_eject(const kt_buf* b, kt_elem* out) {
    return buf_eject(b, out);
}

/* Green push/inject/pop/eject — same physical operation; identical to buf_*. */

/* ===================================================================== */
/* Concat helpers (Viennot's prefix_concat / suffix_concat / green_*)     */
/* ===================================================================== */

/* prefix_concat (b1: any color) (b2: yellow buf of pairs) -> (green, any) */
static void prefix_concat(const kt_buf* b1, const kt_buf* b2,
                          kt_buf** out_p1, kt_buf** out_p2) {
    decomp dp = prefix_decompose(b1);
    if (dp.kind == DEC_UNDERFLOW) {
        /* yellow_pop b2 -> (ab, b2'); prefix23 opt ab ; b2' */
        kt_elem ab; kt_buf* b2p = yellow_pop(b2, &ab);
        kt_elem ab_x, ab_y; pair_split(ab, &ab_x, &ab_y);
        *out_p1 = prefix23(dp.opt_present, dp.opt, ab_x, ab_y);
        *out_p2 = b2p;
    } else if (dp.kind == DEC_OK) {
        *out_p1 = dp.green_buf;
        /* to_red b2: b2 buffer pointer is already a buffer of any color. */
        *out_p2 = (kt_buf*)b2;
    } else {
        /* Overflow (b1', ab): yellow_push ab b2 -> red */
        kt_elem ab = pair_make(dp.pair_x, dp.pair_y);
        *out_p1 = dp.green_buf;
        *out_p2 = yellow_push(ab, b2);
    }
}

static void suffix_concat(const kt_buf* b1, const kt_buf* b2,
                          kt_buf** out_p1, kt_buf** out_p2) {
    decomp ds = suffix_decompose(b2);
    if (ds.kind == DEC_UNDERFLOW) {
        /* yellow_eject b1 -> (b1', ab); b1', suffix23 ab opt */
        kt_elem ab; kt_buf* b1p = yellow_eject(b1, &ab);
        kt_elem ab_x, ab_y; pair_split(ab, &ab_x, &ab_y);
        *out_p1 = b1p;
        *out_p2 = suffix23(ab_x, ab_y, ds.opt_present, ds.opt);
    } else if (ds.kind == DEC_OK) {
        *out_p1 = (kt_buf*)b1;
        *out_p2 = ds.green_buf;
    } else {
        kt_elem ab = pair_make(ds.pair_x, ds.pair_y);
        *out_p1 = yellow_inject(b1, ab);
        *out_p2 = ds.green_buf;
    }
}

/* green_prefix_concat: (any) buf -> (green) pair-buf -> (green, yellow) */
static void green_prefix_concat(const kt_buf* b1, const kt_buf* b2,
                                kt_buf** out_p1, kt_buf** out_p2) {
    decomp dp = prefix_decompose(b1);
    if (dp.kind == DEC_UNDERFLOW) {
        /* green_pop b2 -> (ab, b2') */
        kt_elem ab; kt_buf* b2p = buf_pop(b2, &ab);
        kt_elem ab_x, ab_y; pair_split(ab, &ab_x, &ab_y);
        *out_p1 = prefix23(dp.opt_present, dp.opt, ab_x, ab_y);
        *out_p2 = b2p;
    } else if (dp.kind == DEC_OK) {
        *out_p1 = dp.green_buf;
        *out_p2 = (kt_buf*)b2;  /* to_yellow b2; physically same buffer */
    } else {
        kt_elem ab = pair_make(dp.pair_x, dp.pair_y);
        *out_p1 = dp.green_buf;
        *out_p2 = buf_push(ab, b2); /* green_push */
    }
}

static void green_suffix_concat(const kt_buf* b1, const kt_buf* b2,
                                kt_buf** out_p1, kt_buf** out_p2) {
    decomp ds = suffix_decompose(b2);
    if (ds.kind == DEC_UNDERFLOW) {
        kt_elem ab; kt_buf* b1p = buf_eject(b1, &ab);
        kt_elem ab_x, ab_y; pair_split(ab, &ab_x, &ab_y);
        *out_p1 = b1p;
        *out_p2 = suffix23(ab_x, ab_y, ds.opt_present, ds.opt);
    } else if (ds.kind == DEC_OK) {
        *out_p1 = (kt_buf*)b1;  /* to_yellow */
        *out_p2 = ds.green_buf;
    } else {
        kt_elem ab = pair_make(ds.pair_x, ds.pair_y);
        *out_p1 = buf_inject(b1, ab); /* green_inject */
        *out_p2 = ds.green_buf;
    }
}

/* ===================================================================== */
/* green_of_red (Viennot deque_core.ml line 425)                          */
/* ===================================================================== */

/* Input: a red link (low 2 bits = CR).  Returns: a green chain (kt_chain). */
static void* green_of_red(kt_link* red_link) {
    kt_packet* p = link_packet(red_link);
    kt_buf* p1 = p->pre;
    kt_buf* s1 = p->suf;
    kt_packet* inner = p->inner;

    if (inner == NULL) {
        /* Hole inner — split on next_chain. */
        if (chain_is_ending(red_link->next_chain)) {
            /* Chain(R, Packet(p1, Hole, s1), Ending buf) -> make_small p1 buf s1 */
            kt_buf* buf = chain_ending_buf(red_link->next_chain);
            return make_small(p1, buf, s1);
        }
        kt_link* next = chain_link(red_link->next_chain);
        /* Following spec: Chain(R, Packet(p1, Hole, s1),
         *                       Chain(G, Packet(p2, child, s2), c)) */
        assert(link_col(next) == CG);
        kt_packet* npkt = link_packet(next);
        kt_buf* p2 = npkt->pre;
        kt_buf* s2 = npkt->suf;
        kt_packet* child = npkt->inner;

        kt_buf *gp1, *yp2;
        green_prefix_concat(p1, p2, &gp1, &yp2);
        kt_buf *ys2, *gs1;
        green_suffix_concat(s2, s1, &ys2, &gs1);
        /* Now p2 (replaced by yp2) and s2 (replaced by ys2) are yellow.
         * Build: Chain(G, Packet(gp1, Packet(yp2, child, ys2), gs1), c) */
        kt_packet* inner_pkt = alloc_packet();
        inner_pkt->pre = yp2; inner_pkt->inner = child; inner_pkt->suf = ys2;
        kt_packet* outer_pkt = alloc_packet();
        outer_pkt->pre = gp1; outer_pkt->inner = inner_pkt; outer_pkt->suf = gs1;
        kt_link* new_link = alloc_link();
        new_link->packet_tagged = make_tagged_packet(outer_pkt, CG);
        new_link->next_chain    = next->next_chain;  /* c */
        return chain_make_link(new_link);
    } else {
        /* Inner is a yellow nested packet (inner.pre, inner.inner, inner.suf).
         * Chain(R, Packet(p1, Packet(p2, child, s2), s1), c) ->
         *   let p1, p2 = prefix_concat p1 (to_yellow p2) in
         *   let s2, s1 = suffix_concat (to_yellow s2) s1 in
         *   Chain(G, Packet(p1, Hole, s1), Chain(R, Packet(p2, child, s2), c)) */
        kt_buf* p2 = inner->pre;
        kt_buf* s2 = inner->suf;
        kt_packet* child = inner->inner;

        kt_buf *new_p1, *new_p2;
        prefix_concat(p1, p2, &new_p1, &new_p2);
        kt_buf *new_s2, *new_s1;
        suffix_concat(s2, s1, &new_s2, &new_s1);

        /* Inner red packet: (new_p2, child, new_s2). */
        kt_packet* red_pkt = alloc_packet();
        red_pkt->pre = new_p2; red_pkt->inner = child; red_pkt->suf = new_s2;
        kt_link* new_red = alloc_link();
        new_red->packet_tagged = make_tagged_packet(red_pkt, CR);
        new_red->next_chain    = red_link->next_chain;

        /* Outer green packet: (new_p1, Hole, new_s1). */
        kt_packet* g_pkt = alloc_packet();
        g_pkt->pre = new_p1; g_pkt->inner = NULL; g_pkt->suf = new_s1;
        kt_link* new_green = alloc_link();
        new_green->packet_tagged = make_tagged_packet(g_pkt, CG);
        new_green->next_chain    = chain_make_link(new_red);
        return chain_make_link(new_green);
    }
}

/* ensure_green: identity on green / Ending; green_of_red on red.  Note
 * the input is restricted by the regularity invariant to be green or red
 * (never yellow at this position). */
static void* ensure_green(void* c) {
    if (chain_is_ending(c)) return c;
    kt_link* l = chain_link(c);
    kt_col col = link_col(l);
    if (col == CG) return c;
    if (col == CR) return green_of_red(l);
    /* Yellow at this position would violate the regularity invariant.  In
     * practice we never see it because make_yellow always feeds a green/red
     * chain into ensure_green. */
    assert(0);
    return c;
}

/* make_yellow: build a Y packet with non-red outer buffers, and the
 * following chain made green. */
static void* make_yellow(kt_buf* p1, kt_packet* child, kt_buf* s1, void* c) {
    void* g = ensure_green(c);
    kt_packet* pkt = alloc_packet();
    pkt->pre = p1; pkt->inner = child; pkt->suf = s1;
    kt_link* lnk = alloc_link();
    lnk->packet_tagged = make_tagged_packet(pkt, CY);
    lnk->next_chain    = g;
    return chain_make_link(lnk);
}

/* make_red: build an R packet wrapped in green_of_red, returning a green
 * chain. */
static void* make_red(kt_buf* p1, kt_packet* child, kt_buf* s1, void* c) {
    kt_packet* pkt = alloc_packet();
    pkt->pre = p1; pkt->inner = child; pkt->suf = s1;
    kt_link* red_link = alloc_link();
    red_link->packet_tagged = make_tagged_packet(pkt, CR);
    red_link->next_chain    = c;
    return green_of_red(red_link);
}

/* ===================================================================== */
/* Public ops                                                             */
/* ===================================================================== */

kt_deque kt_empty(void) {
    return NULL;
}

/* Normalize: if c is `Ending(B0)`, return NULL (canonical empty).  This is
 * the only place we collapse the empty-buffer state.  All other Ending
 * states are kept as-is to preserve the chain structure. */
static inline void* normalize_empty(void* c) {
    if (c != NULL && chain_is_ending(c)) {
        kt_buf* b = chain_ending_buf(c);
        if (b->size == 0) return NULL;
    }
    return c;
}

kt_deque kt_push(kt_elem x, kt_deque d) {
    void* c = (void*)d;
    if (c == NULL) {
        return chain_make_ending(mk_buf1(x));
    }
    if (chain_is_ending(c)) {
        kt_buf* b = chain_ending_buf(c);
        return buffer_push_chain(x, b);
    }
    kt_link* l = chain_link(c);
    kt_packet* pkt = link_packet(l);
    kt_col col = link_col(l);

    if (col == CG) {
        kt_buf* new_pre = buf_push(x, pkt->pre);
        return make_yellow(new_pre, pkt->inner, pkt->suf, l->next_chain);
    }
    kt_buf* new_pre = buf_push(x, pkt->pre);
    return make_red(new_pre, pkt->inner, pkt->suf, l->next_chain);
}

kt_deque kt_inject(kt_deque d, kt_elem x) {
    void* c = (void*)d;
    if (c == NULL) {
        return chain_make_ending(mk_buf1(x));
    }
    if (chain_is_ending(c)) {
        kt_buf* b = chain_ending_buf(c);
        return buffer_inject_chain(b, x);
    }
    kt_link* l = chain_link(c);
    kt_packet* pkt = link_packet(l);
    kt_col col = link_col(l);

    if (col == CG) {
        kt_buf* new_suf = buf_inject(pkt->suf, x);
        return make_yellow(pkt->pre, pkt->inner, new_suf, l->next_chain);
    }
    kt_buf* new_suf = buf_inject(pkt->suf, x);
    return make_red(pkt->pre, pkt->inner, new_suf, l->next_chain);
}

kt_deque kt_pop(kt_deque d, kt_elem* out, int* out_was_nonempty) {
    void* c = (void*)d;
    if (c == NULL) {
        if (out_was_nonempty) *out_was_nonempty = 0;
        return NULL;
    }
    if (chain_is_ending(c)) {
        kt_buf* b = chain_ending_buf(c);
        if (b->size == 0) {
            if (out_was_nonempty) *out_was_nonempty = 0;
            return NULL;
        }
        kt_elem y; kt_buf* nb = buf_pop(b, &y);
        *out = y;
        if (out_was_nonempty) *out_was_nonempty = 1;
        return normalize_empty(chain_make_ending(nb));
    }
    kt_link* l = chain_link(c);
    kt_packet* pkt = link_packet(l);
    kt_col col = link_col(l);

    if (col == CG) {
        kt_elem y; kt_buf* new_pre = buf_pop(pkt->pre, &y);
        *out = y;
        if (out_was_nonempty) *out_was_nonempty = 1;
        return normalize_empty(make_yellow(new_pre, pkt->inner, pkt->suf, l->next_chain));
    }
    kt_elem y; kt_buf* new_pre = buf_pop(pkt->pre, &y);
    *out = y;
    if (out_was_nonempty) *out_was_nonempty = 1;
    return normalize_empty(make_red(new_pre, pkt->inner, pkt->suf, l->next_chain));
}

kt_deque kt_eject(kt_deque d, kt_elem* out, int* out_was_nonempty) {
    void* c = (void*)d;
    if (c == NULL) {
        if (out_was_nonempty) *out_was_nonempty = 0;
        return NULL;
    }
    if (chain_is_ending(c)) {
        kt_buf* b = chain_ending_buf(c);
        if (b->size == 0) {
            if (out_was_nonempty) *out_was_nonempty = 0;
            return NULL;
        }
        kt_elem y; kt_buf* nb = buf_eject(b, &y);
        *out = y;
        if (out_was_nonempty) *out_was_nonempty = 1;
        return normalize_empty(chain_make_ending(nb));
    }
    kt_link* l = chain_link(c);
    kt_packet* pkt = link_packet(l);
    kt_col col = link_col(l);

    if (col == CG) {
        kt_elem y; kt_buf* new_suf = buf_eject(pkt->suf, &y);
        *out = y;
        if (out_was_nonempty) *out_was_nonempty = 1;
        return normalize_empty(make_yellow(pkt->pre, pkt->inner, new_suf, l->next_chain));
    }
    kt_elem y; kt_buf* new_suf = buf_eject(pkt->suf, &y);
    *out = y;
    if (out_was_nonempty) *out_was_nonempty = 1;
    return normalize_empty(make_red(pkt->pre, pkt->inner, new_suf, l->next_chain));
}

/* ===================================================================== */
/* Length / regularity / walk                                              */
/* ===================================================================== */

/* Walk chain: each level in the chain is a packet at level L (where L is the
 * current "scaling" — 1 at the top, 2 inside one nested yellow, 4 inside two,
 * etc.).  The pair-tree depth is multiplicative. */

static size_t buf_count_at(const kt_buf* b, int log_level) {
    /* Each element at this level represents 2^log_level base elements. */
    return ((size_t)b->size) << log_level;
}

static size_t packet_count(const kt_packet* p, int log_level);
static size_t chain_count(void* c, int log_level);

static size_t packet_count(const kt_packet* p, int log_level) {
    size_t n = buf_count_at(p->pre, log_level);
    n += buf_count_at(p->suf, log_level);
    if (p->inner != NULL) {
        n += packet_count(p->inner, log_level + 1);
    }
    return n;
}

static size_t chain_count(void* c, int log_level) {
    if (chain_is_ending(c)) {
        return buf_count_at(chain_ending_buf(c), log_level);
    }
    kt_link* l = chain_link(c);
    kt_packet* pkt = link_packet(l);
    /* Outer packet contributes pre+suf at log_level, inner at log_level+1.
     * The next chain link's elements live at log_level + (1 + depth(inner)). */
    size_t n = buf_count_at(pkt->pre, log_level);
    n += buf_count_at(pkt->suf, log_level);
    int next_log_level = log_level + 1;
    if (pkt->inner != NULL) {
        n += packet_count(pkt->inner, log_level + 1);
        /* count inner depth */
        const kt_packet* p = pkt->inner;
        while (p != NULL) {
            next_log_level++;
            p = p->inner;
        }
    }
    n += chain_count(l->next_chain, next_log_level);
    return n;
}

size_t kt_length(kt_deque d) {
    if (d == NULL) return 0;
    return chain_count((void*)d, 0);
}

/* kt_check_regular: returns 0 if the regularity invariant holds.
 * Invariant: chain colors form an alternating G+/Y* pattern with the
 * Y -> G and R -> G constraints. */
int kt_check_regular(kt_deque d) {
    if (d == NULL) return 0;
    void* c = (void*)d;
    if (chain_is_ending(c)) return 0;
    kt_link* l = chain_link(c);
    kt_col col = link_col(l);
    /* Top must not be red. */
    if (col == CR) return -1;

    /* Walk the chain and check regularity. */
    while (!chain_is_ending(c)) {
        kt_link* lnk = chain_link(c);
        kt_col cur = link_col(lnk);
        void* nxt = lnk->next_chain;
        if (cur == CY || cur == CR) {
            /* Successor must be green (or ending counts as green per
             * Viennot's GADT — Ending is green-typed). */
            if (chain_is_ending(nxt)) {
                /* OK. */
            } else {
                kt_link* nl = chain_link(nxt);
                if (link_col(nl) != CG) return -2;
            }
        }
        c = nxt;
    }
    return 0;
}

/* ===================================================================== */
/* Walking — front-to-back element traversal                              */
/* ===================================================================== */

static void elem_walk_at(kt_elem e, int log_level, kt_walk_cb cb, void* ctx) {
    if (log_level == 0) {
        cb(e, ctx);
        return;
    }
    kt_pair* p = (kt_pair*)e;
    elem_walk_at(p->left,  log_level - 1, cb, ctx);
    elem_walk_at(p->right, log_level - 1, cb, ctx);
}

static void buf_walk_at(const kt_buf* b, int log_level, kt_walk_cb cb, void* ctx) {
    for (uint32_t i = 0; i < b->size; i++) {
        elem_walk_at(b->e[i], log_level, cb, ctx);
    }
}

/* Forward decls. */
static void packet_walk(const kt_packet* p, int log_level,
                        void* tail_chain, int tail_log_level,
                        kt_walk_cb cb, void* ctx);
static void chain_walk(void* c, int log_level, kt_walk_cb cb, void* ctx);

static void packet_walk(const kt_packet* p, int log_level,
                        void* tail_chain, int tail_log_level,
                        kt_walk_cb cb, void* ctx) {
    /* Front-to-back: pre, then deeper-level (inner packet, which itself
     * embeds the tail_chain at its bottom), then suf.  But the chain after
     * this packet appears between the inner depths and the suffix?  No —
     * read the OCaml fold_left_packet: pre, then recursively into pkt
     * (passing chain c), then suf.
     *
     * In our representation, the tail_chain belongs to the *outermost*
     * packet only.  An inner packet has no tail_chain of its own.  So we
     * walk: pre, then inner-packet-with-or-without-tail, then suf. */
    buf_walk_at(p->pre, log_level, cb, ctx);
    if (p->inner != NULL) {
        packet_walk(p->inner, log_level + 1, tail_chain, tail_log_level,
                    cb, ctx);
    } else if (tail_chain != NULL) {
        chain_walk(tail_chain, tail_log_level, cb, ctx);
    }
    buf_walk_at(p->suf, log_level, cb, ctx);
}

static void chain_walk(void* c, int log_level, kt_walk_cb cb, void* ctx) {
    if (chain_is_ending(c)) {
        buf_walk_at(chain_ending_buf(c), log_level, cb, ctx);
        return;
    }
    kt_link* l = chain_link(c);
    kt_packet* pkt = link_packet(l);
    /* The next chain (l->next_chain) lives at a deeper level: every nested
     * packet boxes pairs, so log_level+1 for the immediate inner, +1 more
     * per layer. */
    int next_log_level = log_level + 1;
    const kt_packet* ip = pkt->inner;
    while (ip != NULL) { next_log_level++; ip = ip->inner; }

    packet_walk(pkt, log_level, l->next_chain, next_log_level, cb, ctx);
}

void kt_walk(kt_deque d, kt_walk_cb cb, void* ctx) {
    if (d == NULL) return;
    chain_walk((void*)d, 0, cb, ctx);
}
