/* Protected AES-128 and modular exponentiation (plan R19b, claim P13 of the paper).
 *
 * The program shows the transformation of Section 5 (Figures 5(b) and 6(b)) with opaque conditions that are outputs of a
 * 2-SAT solver on a planted formula (Sections 3 and 3.1), applied to a portable AES-128 encryption and to a modular
 * exponentiation with a 32-bit modulus (the square-and-multiply kernel of RSA):
 *
 *   PROT5(L, S, T)      if (cond[1]) goto L; do { S; L: T; } while (cond[2]);       replaces   S; T;
 *   PROT6(L, C, S, T)   if (!(C)) goto L; do { S; L: T; } while (cond[1]);          replaces   if (C) S; T;
 *
 * `cond[k]` is the output of the solver for variable `k`; the planted formula forces it to the intended value 0, so the
 * loops of the protected code execute their body exactly once and the results are those of the plain code. The goto into
 * the loop body makes the loop an irreducible loop (two entries) in the control-flow graph of the source. What a given
 * compiler makes of the source is not claimed here (the compiler is a black box); the Lean development proves the
 * statements about the transformation on its model of flat code (lean/SmcIrred/Lang/Protect*.lean, Gen/Construct.lean).
 *
 * The self-test runs the plain and the protected functions on FIPS-197 and on random inputs, a known RSA vector, and checks
 * that the generator's formula is satisfied by the planted assignment and that the solver outputs are the planted values.
 * `protected --dump SEED` prints the planted specification of that seed (used by validation/protected_vectors.py).
 *
 * Portable C99; no inline assembly, no platform API, no self-modifying code (the x86 blueprint of selfmodgraph.cpp is the
 * self-modifying realization of the solver; here the solver is the plain Tarjan implementation). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ---------------------------------------------------------------- pseudo-random numbers (black box to the proofs) */

static uint64_t rng_state;
static uint32_t rng_next(void) {
    uint64_t x = rng_state;
    x ^= x >> 12; x ^= x << 25; x ^= x >> 27;
    rng_state = x;
    return (uint32_t)((x * 0x2545F4914F6CDD1DULL) >> 32);
}
static void rng_seed(uint64_t s) { rng_state = s ? s : 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 8; i++) rng_next(); }

/* ---------------------------------------------------------------- the planted 2-SAT generator (Section 3.1) */

#define MAXN 64          /* variables */
#define MAXIMP 1024      /* implications */
#define MAXMID 4         /* intermediate literals of a forcing chain */

/* A literal is (var, val): "variable var has the value val"; its node is 2*var + val. */
typedef struct { int pa, va, pb, vb; } Imp;       /* the implication (pa = va) => (pb = vb) */

typedef struct {
    int n;                      /* variables */
    int sigma[MAXN];            /* the planted (desired) assignment */
    int req[MAXN];              /* required variables: forced to sigma */
    int nspec;                  /* the forcing chains: variable and intermediate variables */
    int specx[MAXN];
    int specm[MAXN][MAXMID];
    int specr[MAXN];
    int nimp;
    Imp imps[MAXIMP];
} Planted;

static void add_imp(Planted *p, int pa, int va, int pb, int vb) {
    if (p->nimp < MAXIMP) { Imp e = {pa, va, pb, vb}; p->imps[p->nimp++] = e; }
}

static int holds(const Planted *p, int var, int val) { return p->sigma[var] == val; }

/* Generate: for every required variable x a chain (x,!sigma x) => (m1,sigma m1) => ... => (x,sigma x) of at most MAXMID
 * intermediate literals that hold under sigma (every implication then respects sigma), then `extra` random implications
 * that respect sigma. */
static void gen_planted(Planted *p, int n, const int *sigma, const int *req, int extra) {
    memset(p, 0, sizeof *p);
    p->n = n;
    for (int x = 0; x < n; x++) { p->sigma[x] = sigma[x]; p->req[x] = req[x]; }
    for (int x = 0; x < n; x++) {
        if (!req[x]) continue;
        int r = (int)(rng_next() % (MAXMID + 1));
        int k = p->nspec++;
        p->specx[k] = x; p->specr[k] = r;
        int pv = x, pval = !sigma[x];
        for (int i = 0; i < r; i++) {
            int m = (int)(rng_next() % (uint32_t)n);
            p->specm[k][i] = m;
            add_imp(p, pv, pval, m, sigma[m]);
            pv = m; pval = sigma[m];
        }
        add_imp(p, pv, pval, x, sigma[x]);
    }
    for (int tries = 0; tries < 8 * extra && extra > 0; tries++) {
        int a = (int)(rng_next() % (uint32_t)n), va = (int)(rng_next() & 1);
        int b = (int)(rng_next() % (uint32_t)n), vb = (int)(rng_next() & 1);
        if (holds(p, a, va) && !holds(p, b, vb)) continue;   /* does not respect sigma */
        add_imp(p, a, va, b, vb);
        if (--extra == 0) break;
    }
}

/* ---------------------------------------------------------------- the solver: strongly connected components (Tarjan) */

typedef struct {
    int nodes;
    int head[2 * MAXN], nxt[2 * MAXIMP], to[2 * MAXIMP], ne;
    int idx[2 * MAXN], low[2 * MAXN], comp[2 * MAXN], onstack[2 * MAXN], stack[2 * MAXN], sp, counter, ncomp;
} Graph;

static void g_edge(Graph *g, int a, int b) { g->to[g->ne] = b; g->nxt[g->ne] = g->head[a]; g->head[a] = g->ne++; }

static void scc(Graph *g, int v) {
    g->idx[v] = g->low[v] = ++g->counter;
    g->stack[g->sp++] = v; g->onstack[v] = 1;
    for (int e = g->head[v]; e >= 0; e = g->nxt[e]) {
        int w = g->to[e];
        if (!g->idx[w]) { scc(g, w); if (g->low[w] < g->low[v]) g->low[v] = g->low[w]; }
        else if (g->onstack[w] && g->idx[w] < g->low[v]) g->low[v] = g->idx[w];
    }
    if (g->low[v] == g->idx[v]) {
        int w;
        do { w = g->stack[--g->sp]; g->onstack[w] = 0; g->comp[w] = g->ncomp; } while (w != v);
        g->ncomp++;
    }
}

/* Solve the formula of the implications (each implication a => b is the clause (!a or b), i.e. also !b => !a): returns 1
 * and the assignment out[], or 0 if unsatisfiable. Node 2*var+1 is "var is true": the variable is true iff the component of its true node is completed first (Tarjan completes components in reverse topological order). */
static int solve(const Planted *p, int *out) {
    static Graph g;
    memset(&g, 0, sizeof g);
    g.nodes = 2 * p->n;
    for (int i = 0; i < g.nodes; i++) g.head[i] = -1;
    for (int i = 0; i < p->nimp; i++) {
        const Imp *e = &p->imps[i];
        int a = 2 * e->pa + e->va, b = 2 * e->pb + e->vb;
        g_edge(&g, a, b);
        g_edge(&g, b ^ 1, a ^ 1);
    }
    for (int v = 0; v < g.nodes; v++) if (!g.idx[v]) scc(&g, v);
    for (int x = 0; x < p->n; x++) {
        if (g.comp[2 * x] == g.comp[2 * x + 1]) return 0;
        out[x] = g.comp[2 * x + 1] < g.comp[2 * x];
    }
    return 1;
}

/* ---------------------------------------------------------------- the opaque conditions */

/* Read through a volatile array so that a compiler cannot fold the conditions: cond[k] is the solver's output k. */
static volatile unsigned char cond[MAXN];

#define CAT2(a, b) a##b
#define CAT(a, b) CAT2(a, b)

/* Figure 5(b): S; T;  ==>  if (cond[1]) goto L; do { S; L: T; } while (cond[2]); */
#define PROT5(L, S, T) { if (cond[1]) goto L; do { S; L: T; } while (cond[2]); }
/* Figure 6(b): if (C) S; T;  ==>  if (!(C)) goto L; do { S; L: T; } while (cond[1]); */
#define PROT6(L, C, S, T) { if (!(C)) goto L; do { S; L: T; } while (cond[1]); }

/* ---------------------------------------------------------------- AES-128 (portable) */

static uint8_t SBOX[256];
static void sbox_init(void) {
    uint8_t p = 1, q = 1;
    do {
        p = (uint8_t)(p ^ (uint8_t)(p << 1) ^ ((p & 0x80) ? 0x1B : 0));
        q ^= (uint8_t)(q << 1); q ^= (uint8_t)(q << 2); q ^= (uint8_t)(q << 4);
        if (q & 0x80) q ^= 0x09;
        uint8_t x = (uint8_t)(q ^ (uint8_t)((q << 1) | (q >> 7)) ^ (uint8_t)((q << 2) | (q >> 6)) ^
                              (uint8_t)((q << 3) | (q >> 5)) ^ (uint8_t)((q << 4) | (q >> 4)));
        SBOX[p] = (uint8_t)(x ^ 0x63);
    } while (p != 1);
    SBOX[0] = 0x63;
}

static uint8_t xtime(uint8_t x) { return (uint8_t)((x << 1) ^ ((x >> 7) * 0x1B)); }

static void key_expand(const uint8_t key[16], uint8_t rk[176]) {
    uint8_t rcon = 1;
    memcpy(rk, key, 16);
    for (int i = 16; i < 176; i += 4) {
        uint8_t t[4];
        memcpy(t, rk + i - 4, 4);
        if (i % 16 == 0) {
            uint8_t u = t[0];
            t[0] = (uint8_t)(SBOX[t[1]] ^ rcon); t[1] = SBOX[t[2]]; t[2] = SBOX[t[3]]; t[3] = SBOX[u];
            rcon = xtime(rcon);
        }
        for (int j = 0; j < 4; j++) rk[i + j] = (uint8_t)(rk[i - 16 + j] ^ t[j]);
    }
}

#define SUB(st) do { for (int i_ = 0; i_ < 16; i_++) (st)[i_] = SBOX[(st)[i_]]; } while (0)
#define SHIFT(st) do { uint8_t t_;                                                                              \
    t_ = (st)[1]; (st)[1] = (st)[5]; (st)[5] = (st)[9]; (st)[9] = (st)[13]; (st)[13] = t_;                       \
    t_ = (st)[2]; (st)[2] = (st)[10]; (st)[10] = t_; t_ = (st)[6]; (st)[6] = (st)[14]; (st)[14] = t_;           \
    t_ = (st)[15]; (st)[15] = (st)[11]; (st)[11] = (st)[7]; (st)[7] = (st)[3]; (st)[3] = t_; } while (0)
#define MIX(st) do { for (int c_ = 0; c_ < 16; c_ += 4) {                                                         \
    uint8_t a0 = (st)[c_], a1 = (st)[c_ + 1], a2 = (st)[c_ + 2], a3 = (st)[c_ + 3];                             \
    (st)[c_]     = (uint8_t)(xtime(a0) ^ (xtime(a1) ^ a1) ^ a2 ^ a3);                                          \
    (st)[c_ + 1] = (uint8_t)(a0 ^ xtime(a1) ^ (xtime(a2) ^ a2) ^ a3);                                          \
    (st)[c_ + 2] = (uint8_t)(a0 ^ a1 ^ xtime(a2) ^ (xtime(a3) ^ a3));                                          \
    (st)[c_ + 3] = (uint8_t)((xtime(a0) ^ a0) ^ a1 ^ a2 ^ xtime(a3)); } } while (0)
#define ADDK(st, rk, r) do { for (int i_ = 0; i_ < 16; i_++) (st)[i_] ^= (rk)[16 * (r) + i_]; } while (0)

static void aes_plain(const uint8_t key[16], const uint8_t in[16], uint8_t out[16]) {
    uint8_t rk[176], st[16];
    key_expand(key, rk);
    memcpy(st, in, 16);
    ADDK(st, rk, 0);
    for (int r = 1; r < 10; r++) { SUB(st); SHIFT(st); MIX(st); ADDK(st, rk, r); }
    SUB(st); SHIFT(st); ADDK(st, rk, 10);
    memcpy(out, st, 16);
}

/* Every pair of consecutive steps of a round is an irreducible loop: the pairs are protected inside the round loop. */
static void aes_protected(const uint8_t key[16], const uint8_t in[16], uint8_t out[16]) {
    uint8_t rk[176], st[16];
    int r;
    key_expand(key, rk);
    memcpy(st, in, 16);
    ADDK(st, rk, 0);
    for (r = 1; r < 10; r++) {
        PROT5(L_round_a, SUB(st), SHIFT(st));
        PROT5(L_round_b, MIX(st), ADDK(st, rk, r));
    }
    PROT5(L_last, SUB(st), SHIFT(st));
    ADDK(st, rk, 10);
    memcpy(out, st, 16);
}

/* ---------------------------------------------------------------- modular exponentiation with a 32-bit modulus */

static uint32_t modexp_plain(uint32_t m, uint32_t e, uint32_t n) {
    uint64_t acc = 1, base = m % n;
    for (int i = 0; i < 32; i++) {
        if ((e >> i) & 1) acc = acc * base % n;
        base = base * base % n;
    }
    return (uint32_t)acc;
}

static uint32_t modexp_protected(uint32_t m, uint32_t e, uint32_t n) {
    uint64_t acc = 1, base = m % n;
    int i;
    for (i = 0; i < 32; i++) {
        PROT6(L_mul, (e >> i) & 1, acc = acc * base % n, base = base * base % n);
    }
    return (uint32_t)acc;
}

/* ---------------------------------------------------------------- self-test */

static int failures;
static void check(int ok, const char *what) {
    if (!ok) { failures++; printf("FAIL %s\n", what); }
}

static void dump(uint64_t seed) {
    int n = 16, sigma[MAXN], req[MAXN];
    rng_seed(seed);
    for (int x = 0; x < n; x++) { sigma[x] = (int)(rng_next() & 1); req[x] = 0; }
    sigma[1] = 0; sigma[2] = 0; req[1] = 1; req[2] = 1;
    for (int x = 3; x < n; x++) req[x] = (int)(rng_next() & 1);
    static Planted p;
    gen_planted(&p, n, sigma, req, 12);
    printf("seed %llu n %d\nsigma", (unsigned long long)seed, n);
    for (int x = 0; x < n; x++) printf(" %d", p.sigma[x]);
    printf("\nreq");
    for (int x = 0; x < n; x++) printf(" %d", p.req[x]);
    printf("\n");
    for (int k = 0; k < p.nspec; k++) {
        printf("spec %d", p.specx[k]);
        for (int i = 0; i < p.specr[k]; i++) printf(" %d", p.specm[k][i]);
        printf("\n");
    }
    printf("imps %d\n", p.nimp);
    for (int i = 0; i < p.nimp; i++) printf("imp %d %d %d %d\n", p.imps[i].pa, p.imps[i].va, p.imps[i].pb, p.imps[i].vb);
    int out[MAXN];
    int sat = solve(&p, out);
    printf("sat %d\nout", sat);
    for (int x = 0; x < n; x++) printf(" %d", out[x]);
    printf("\n");
}

int main(int argc, char **argv) {
    sbox_init();
    if (argc == 3 && strcmp(argv[1], "--dump") == 0) { dump(strtoull(argv[2], 0, 10)); return 0; }

    /* the generator and the solver on many seeds: satisfiable, required outputs are the planted values */
    for (uint64_t seed = 1; seed <= 200; seed++) {
        int n = 16, sigma[MAXN], req[MAXN], out[MAXN];
        static Planted p;
        rng_seed(seed);
        for (int x = 0; x < n; x++) { sigma[x] = (int)(rng_next() & 1); req[x] = 0; }
        sigma[1] = 0; sigma[2] = 0; req[1] = 1; req[2] = 1;
        for (int x = 3; x < n; x++) req[x] = (int)(rng_next() & 1);
        gen_planted(&p, n, sigma, req, 12);
        int sat = solve(&p, out);
        check(sat, "planted formula satisfiable");
        for (int x = 0; sat && x < n; x++) if (req[x]) check(out[x] == sigma[x], "required output is planted value");
        for (int i = 0; i < p.nimp; i++) {
            const Imp *e = &p.imps[i];
            check(!(holds(&p, e->pa, e->va) && !holds(&p, e->pb, e->vb)), "implication respects the planted assignment");
        }
    }

    /* the conditions of the protected code are the outputs 1 and 2 of the solver on a planted formula */
    {
        int n = 16, sigma[MAXN], req[MAXN], out[MAXN];
        static Planted p;
        rng_seed(12345);
        for (int x = 0; x < n; x++) { sigma[x] = (int)(rng_next() & 1); req[x] = 0; }
        sigma[1] = 0; sigma[2] = 0; req[1] = 1; req[2] = 1;
        gen_planted(&p, n, sigma, req, 12);
        check(solve(&p, out), "solve for the conditions");
        for (int x = 0; x < n; x++) cond[x] = (unsigned char)out[x];
        check(cond[1] == 0 && cond[2] == 0, "conditions 1 and 2 are false");
        if (failures) { printf("protected: %d failures (not running the protected code)\n", failures); return 1; }
    }

    /* AES-128: FIPS-197 appendix C.1 */
    {
        uint8_t key[16], in[16], out[16], out2[16];
        static const uint8_t expect[16] = {0x69, 0xc4, 0xe0, 0xd8, 0x6a, 0x7b, 0x04, 0x30,
                                           0xd8, 0xcd, 0xb7, 0x80, 0x70, 0xb4, 0xc5, 0x5a};
        for (int i = 0; i < 16; i++) { key[i] = (uint8_t)i; in[i] = (uint8_t)(0x11 * i); }
        aes_plain(key, in, out);
        aes_protected(key, in, out2);
        check(memcmp(out, expect, 16) == 0, "AES-128 plain FIPS-197 C.1");
        check(memcmp(out2, expect, 16) == 0, "AES-128 protected FIPS-197 C.1");
        rng_seed(777);
        for (int t = 0; t < 2000; t++) {
            for (int i = 0; i < 16; i++) { key[i] = (uint8_t)rng_next(); in[i] = (uint8_t)rng_next(); }
            aes_plain(key, in, out);
            aes_protected(key, in, out2);
            check(memcmp(out, out2, 16) == 0, "AES-128 protected = plain on random input");
        }
    }

    /* modular exponentiation: a known RSA vector with a 32-bit modulus, and random agreement */
    {
        const uint32_t n = 4292870399u, e = 65537u, d = 1475213633u, m = 123456789u, c = 2081669972u;
        check(modexp_plain(m, e, n) == c, "modexp plain encrypt");
        check(modexp_protected(m, e, n) == c, "modexp protected encrypt");
        check(modexp_plain(c, d, n) == m, "modexp plain decrypt");
        check(modexp_protected(c, d, n) == m, "modexp protected decrypt");
        rng_seed(99);
        for (int t = 0; t < 2000; t++) {
            uint32_t x = rng_next(), y = rng_next();
            check(modexp_plain(x, y, n) == modexp_protected(x, y, n), "modexp protected = plain on random input");
        }
    }

    printf(failures ? "protected: %d failures\n" : "protected: all checks passed\n", failures);
    return failures != 0;
}
