/* bench_wcet.c — worst-case per-operation timing probe for the C deques.
 *
 * The C analogue of ocaml/bench/wcet.ml.  For each operation, over a
 * battery of reachable states (op-histories + a seeded random walk; for
 * concat, operand pairs), report the worst-case ns/op: the MAX over
 * states of the MIN-over-trials mean at each state.  Timing uses
 * persistent re-execution (the op is applied to one saved state many
 * times; the state is immutable so every call repeats the same work).
 *
 * §4: the worst-case *allocation* bound is measured separately and is
 * flat across n — see tests/wc_test.c (<= 8 alloc objects/op).  This
 * binary covers timing.
 *
 * §6: the catenable port mallocs a spine node per op (the unified-arena
 * integration is future work; see COMPARISON.md), so its per-op cost
 * legitimately INCLUDES that malloc, and persistent re-execution leaks
 * the discarded spines.  We keep m modest for §6 and still compact the
 * §4 buffer arena (kc_arena_compact) between bursts.  The deterministic
 * §6 *work* bound is the proven primitive count (push/inject <= 4,
 * concat <= 43, pop/eject <= 145), not measured here.
 *
 * Measurement-based worst-case over an adversarial battery, not a sound
 * hardware WCET.  Driven from bench/wcet.sh.  Usage: [--m M] [--trials T]
 */

#include "ktdeque.h"
#include "ktcadeque.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <math.h>

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

/* One element pointer reused everywhere: structural shape depends on the
 * op sequence, not values.  static long is 8-aligned with bit 63 clear,
 * satisfying both the §4 and §6 element contracts. */
static long g_elt = 1;
#define ELT kt_base(&g_elt)

static const long SIZES[] = { 7,15,31,63,127,255,511,1023,4095,16383,131071 };
#define NSIZES ((int)(sizeof SIZES / sizeof SIZES[0]))

/* ---------------- stats ---------------- */
static int cmp_double(const void* a, const void* b) {
    double x = *(const double*)a, y = *(const double*)b;
    return (x < y) ? -1 : (x > y) ? 1 : 0;
}
static double median(double* xs, int n) {
    if (n == 0) return 0.0;
    qsort(xs, (size_t)n, sizeof(double), cmp_double);
    return (n & 1) ? xs[n / 2] : (xs[n / 2 - 1] + xs[n / 2]) / 2.0;
}
typedef struct { double worst; char label[64]; double vals[600]; int nvals; } opstat;
static void rec(opstat* st, double v, const char* label) {
    if (v > st->worst) { st->worst = v; snprintf(st->label, sizeof st->label, "%s", label); }
    if (st->nvals < (int)(sizeof st->vals / sizeof st->vals[0])) st->vals[st->nvals++] = v;
}
static void emit_row(const char* op, opstat* st) {
    printf("| `%s` | %.1f | %.1f | %s |\n", op, st->worst, median(st->vals, st->nvals), st->label);
}

/* ================= §4 deque ================= */

static kt_deque b4_push(long n)   { kt_deque d=kt_empty(); for(long i=0;i<n;i++) d=kt_push(ELT,d); return d; }
static kt_deque b4_inject(long n) { kt_deque d=kt_empty(); for(long i=0;i<n;i++) d=kt_inject(d,ELT); return d; }
static kt_deque b4_alt(long n)    { kt_deque d=kt_empty(); for(long i=0;i<n;i++) d=(i&1)?kt_inject(d,ELT):kt_push(ELT,d); return d; }
static kt_deque b4_churn(long n)  { kt_deque d=kt_empty(); long s=0; for(long i=0;i<n+n/2;i++){d=kt_push(ELT,d);s++;} kt_elem e;int ok; for(long i=0;i<n/2;i++) if(s>0){d=kt_pop(d,&e,&ok);s--;} return d; }
static kt_deque b4_random(unsigned seed,long n){ srand(seed); kt_deque d=kt_empty(); long s=0; for(long i=0;i<n;i++){d=kt_push(ELT,d);s++;} kt_elem e;int ok;
    for(long i=0;i<2*n;i++){ switch(rand()%4){case 0:d=kt_push(ELT,d);s++;break;case 1:d=kt_inject(d,ELT);s++;break;case 2:if(s>0){d=kt_pop(d,&e,&ok);s--;}break;default:if(s>0){d=kt_eject(d,&e,&ok);s--;}}} return d; }

static double time4(int opc, kt_deque* sp, long m, int trials) {
    const long CI=4096; double best=INFINITY;
    for(int tr=0;tr<trials;tr++){ double acc=0; long i=0;
        while(i<m){ long todo=m-i; if(todo>CI)todo=CI; double t0=now_sec();
            for(long j=0;j<todo;j++){ kt_elem o;int ok;kt_deque r;
                switch(opc){case 0:r=kt_push(ELT,*sp);break;case 1:r=kt_inject(*sp,ELT);break;
                    case 2:r=kt_pop(*sp,&o,&ok);break;default:r=kt_eject(*sp,&o,&ok);} (void)r; }
            acc+=now_sec()-t0; i+=todo; kt_arena_compact(sp,1); }
        double ns=acc*1e9/(double)m; if(ns<best)best=ns; }
    return best;
}

static opstat g4[4];
static const char* OP4[4] = { "push","inject","pop","eject" };

static void probe4(const char* label, kt_deque saved, long m, int trials) {
    for(int opc=0;opc<4;opc++){ double ns=time4(opc,&saved,m,trials); rec(&g4[opc],ns,label); }
    kt_deque none=kt_empty(); kt_arena_compact(&none,0); /* flush §4 arena */
}

static void run4(long m, int trials) {
    for(int i=0;i<4;i++){ g4[i].worst=0; g4[i].nvals=0; }
    char lab[64];
    for(int si=0;si<NSIZES;si++){ long n=SIZES[si]; kt_deque d;
        d=b4_push(n);   snprintf(lab,sizeof lab,"push^%ld",n);   probe4(lab,d,m,trials);
        d=b4_inject(n); snprintf(lab,sizeof lab,"inject^%ld",n); probe4(lab,d,m,trials);
        d=b4_alt(n);    snprintf(lab,sizeof lab,"alt^%ld",n);    probe4(lab,d,m,trials);
        d=b4_churn(n);  snprintf(lab,sizeof lab,"churn~%ld",n);  probe4(lab,d,m,trials); }
    long rs[]={127,4095,131071};
    for(int ri=0;ri<3;ri++) for(unsigned s=1;s<=3;s++){ kt_deque d=b4_random(s,rs[ri]);
        snprintf(lab,sizeof lab,"rand%u~%ld",s,rs[ri]); probe4(lab,d,m,trials); }
    printf("### §4 deque (C)\n\n");
    printf("| op | worst-case ns/op | median ns/op | worst-case state |\n|---|---:|---:|---|\n");
    for(int opc=0;opc<4;opc++) emit_row(OP4[opc],&g4[opc]);
}

/* ================= §6 catenable ================= */

static kc_cadeque b6_push(long n)   { kc_cadeque d=kc_empty(); for(long i=0;i<n;i++) d=kc_push(ELT,d); return d; }
static kc_cadeque b6_inject(long n) { kc_cadeque d=kc_empty(); for(long i=0;i<n;i++) d=kc_inject(d,ELT); return d; }
static kc_cadeque b6_churn(long n)  { kc_cadeque d=kc_empty(); long s=0; for(long i=0;i<n+n/2;i++){d=kc_push(ELT,d);s++;} kt_elem e;int ok; for(long i=0;i<n/2;i++) if(s>0){d=kc_pop(d,&e,&ok);s--;} return d; }
static kc_cadeque b6_random(unsigned seed,long n){ srand(seed); kc_cadeque d=kc_empty(); long s=0; for(long i=0;i<n;i++){d=kc_push(ELT,d);s++;} kt_elem e;int ok;
    for(long i=0;i<2*n;i++){ switch(rand()%4){case 0:d=kc_push(ELT,d);s++;break;case 1:d=kc_inject(d,ELT);s++;break;case 2:if(s>0){d=kc_pop(d,&e,&ok);s--;}break;default:if(s>0){d=kc_eject(d,&e,&ok);s--;}}} return d; }

static double time6(int opc, kc_cadeque* sp, long m, int trials) {
    const long CI=4096; double best=INFINITY;
    for(int tr=0;tr<trials;tr++){ double acc=0; long i=0;
        while(i<m){ long todo=m-i; if(todo>CI)todo=CI; double t0=now_sec();
            for(long j=0;j<todo;j++){ kt_elem o;int ok;kc_cadeque r;
                switch(opc){case 0:r=kc_push(ELT,*sp);break;case 1:r=kc_inject(*sp,ELT);break;
                    case 2:r=kc_pop(*sp,&o,&ok);break;default:r=kc_eject(*sp,&o,&ok);} (void)r; }
            acc+=now_sec()-t0; i+=todo; kc_arena_compact(sp,1); }
        double ns=acc*1e9/(double)m; if(ns<best)best=ns; }
    return best;
}

/* concat over a fixed operand pair (a,b), both kept live as roots. */
static double time6_concat(kc_cadeque* a, kc_cadeque* b, long m, int trials) {
    const long CI=4096; double best=INFINITY;
    for(int tr=0;tr<trials;tr++){ double acc=0; long i=0;
        while(i<m){ long todo=m-i; if(todo>CI)todo=CI; double t0=now_sec();
            for(long j=0;j<todo;j++){ kc_cadeque r=kc_concat(*a,*b); (void)r; }
            acc+=now_sec()-t0; i+=todo;
            kc_cadeque roots[2]={*a,*b}; kc_arena_compact(roots,2); *a=roots[0]; *b=roots[1]; }
        double ns=acc*1e9/(double)m; if(ns<best)best=ns; }
    return best;
}

static opstat g6[5];
static const char* OP6[5] = { "push","inject","pop","eject","concat" };

static void probe6(const char* label, kc_cadeque saved, long m, int trials) {
    for(int opc=0;opc<4;opc++){ double ns=time6(opc,&saved,m,trials); rec(&g6[opc],ns,label); }
    kc_cadeque none=kc_empty(); kc_arena_compact(&none,0); /* flush §4 buffer arena */
}

static void run6(long m, int trials) {
    for(int i=0;i<5;i++){ g6[i].worst=0; g6[i].nvals=0; }
    long m6 = (m > 20000) ? 20000 : m;  /* §6 leaks malloc'd spines; cap reps */
    char lab[64];
    for(int si=0;si<NSIZES;si++){ long n=SIZES[si]; kc_cadeque d;
        d=b6_push(n);   snprintf(lab,sizeof lab,"push^%ld",n);   probe6(lab,d,m6,trials);
        d=b6_inject(n); snprintf(lab,sizeof lab,"inject^%ld",n); probe6(lab,d,m6,trials);
        d=b6_churn(n);  snprintf(lab,sizeof lab,"churn~%ld",n);  probe6(lab,d,m6,trials); }
    long rs[]={127,4095,131071};
    for(int ri=0;ri<3;ri++) for(unsigned s=1;s<=2;s++){ kc_cadeque d=b6_random(s,rs[ri]);
        snprintf(lab,sizeof lab,"rand%u~%ld",s,rs[ri]); probe6(lab,d,m6,trials); }
    /* concat: operand-pair battery.  Include SMALL sizes 1..7 — §6 concat
       absorbs a small operand element-wise (bounded threshold), so the
       worst case is just below the threshold, not at large sizes. */
    struct { const char* name; int kind; long n; } OPS6[9] = {
        {"p1",0,1},{"p2",0,2},{"p3",0,3},{"p4",0,4},{"p5",0,5},
        {"p6",0,6},{"p7",0,7},{"p4095",0,4095},{"rand4095",1,4095}
    };
    for(int p=0;p<9;p++){
        for(int q=0;q<9;q++){
            /* rebuild both operands fresh (arena flushed between pairs) */
            kc_cadeque a = (OPS6[p].kind==0) ? b6_push(OPS6[p].n) : b6_random(1,OPS6[p].n);
            kc_cadeque b = (OPS6[q].kind==0) ? b6_push(OPS6[q].n) : b6_random(1,OPS6[q].n);
            double ns=time6_concat(&a,&b,m6,trials);
            snprintf(lab,sizeof lab,"%s++%s",OPS6[p].name,OPS6[q].name); rec(&g6[4],ns,lab);
            kc_cadeque none=kc_empty(); kc_arena_compact(&none,0);
        }
    }
    printf("\n### §6 catenable (C)\n\n");
    printf("| op | worst-case ns/op | median ns/op | worst-case state |\n|---|---:|---:|---|\n");
    for(int opc=0;opc<5;opc++) emit_row(OP6[opc],&g6[opc]);
}

int main(int argc, char** argv) {
    long m=80000; int trials=7;
    for(int i=1;i<argc;i++){
        if(!strcmp(argv[i],"--m")&&i+1<argc) m=strtol(argv[++i],NULL,10);
        else if(!strcmp(argv[i],"--trials")&&i+1<argc) trials=(int)strtol(argv[++i],NULL,10);
        else { fprintf(stderr,"usage: %s [--m M] [--trials T]\n",argv[0]); return 2; }
    }
    /* warm */
    { kt_deque w=b4_push(1000); kt_arena_compact(&w,1); (void)time4(0,&w,10000,1);
      kt_deque none=kt_empty(); kt_arena_compact(&none,0); }
    run4(m, trials);
    run6(m, trials);
    return 0;
}
