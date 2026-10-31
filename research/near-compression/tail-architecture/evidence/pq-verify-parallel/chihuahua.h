#ifndef CHIHUAHUA_H
#define CHIHUAHUA_H

#include <stdint.h>
#include <stddef.h>
#include "poly.h"
#include "polx.h"
#include "polz.h"
#include "sparsemat.h"
#include "labrador.h"

/* A phi block handed over in the coefficient domain instead of as NTT images: element i
 * of the block is sum_{t<wid} c[i*wid + t] X^(off + t), with off + wid <= N. Aggregation
 * multiplies such a block by a quarternary challenge without ever forming its polx. */
typedef struct {
  const int16_t *c;  /* len*wid coefficients, element major; NULL: block is dense */
  size_t off;
  size_t wid;
} shortphi;

/* Aggregation's deferred short-macro contribution (verify path). Shared with
 * the parallel kernel in np_shortmac.h. */
typedef struct {
  size_t dst;            /* first destination element, indexed off ost->cnst->phi */
  const int16_t *c;      /* len*wid coefficients, element major */
  const int16_t *alpha;  /* N coefficients of the challenge */
  size_t len;
  size_t off;
  size_t wid;
} shortent;

#ifdef __AVX512VNNI__
#define DPWSSD(a,x,y) _mm512_dpwssd_epi32(a,x,y)
#else
#define DPWSSD(a,x,y) _mm512_add_epi32(a,_mm512_madd_epi16(x,y))
#endif

static inline int shortent_cmp(const void *x, const void *y) {
  const size_t a = ((const shortent*)x)->dst;
  const size_t b = ((const shortent*)y)->dst;
  return (a > b) - (a < b);
}
/* acc[i] += sum_t c[i*wid+t] X^(off+t) alpha over Z[X]/(X^N+1), int32 lanes.
 *
 * With C[m] = -alpha[m] for m < N and alpha[m-N] for m >= N, coefficient j of
 * X^k alpha is C[N + j - k], so every term is a shifted read of one 2N table. Terms are
 * taken two at a time and the table is stored as the interleaving D[2p] = C[p],
 * D[2p+1] = C[p-1], which turns a term pair into a single multiply-accumulate against a
 * broadcast of the two coefficients. */
static inline void shortmac(int32_t *acc, const shortent *e) {
  __attribute__((aligned(64)))
  int16_t D[4*N];
  size_t i,u,t;
  const size_t wid = e->wid;
  const int16_t *v = e->c;

  for(t=0;t<N;t++) {
    D[2*t] = -e->alpha[t];
    D[2*N+2*t] = e->alpha[t];
  }
  D[1] = 0;
  for(t=1;t<2*N;t++)
    D[2*t+1] = D[2*t-2];

  for(i=0;i<e->len;i++) {
    __m512i a0 = _mm512_load_si512((const __m512i*)&acc[0]);
    __m512i a1 = _mm512_load_si512((const __m512i*)&acc[16]);
    __m512i a2 = _mm512_load_si512((const __m512i*)&acc[32]);
    __m512i a3 = _mm512_load_si512((const __m512i*)&acc[48]);
    for(u=0;u<wid;u+=2) {
      uint32_t w = (uint16_t)v[u];
      if(u+1 < wid)
        w |= (uint32_t)(uint16_t)v[u+1] << 16;
      const __m512i vw = _mm512_set1_epi32((int32_t)w);
      const int16_t *d = &D[2*(N - e->off - u)];
      a0 = DPWSSD(a0,vw,_mm512_loadu_si512((const __m512i*)(d+0)));
      a1 = DPWSSD(a1,vw,_mm512_loadu_si512((const __m512i*)(d+32)));
      a2 = DPWSSD(a2,vw,_mm512_loadu_si512((const __m512i*)(d+64)));
      a3 = DPWSSD(a3,vw,_mm512_loadu_si512((const __m512i*)(d+96)));
    }
    _mm512_store_si512((__m512i*)&acc[0],a0);
    _mm512_store_si512((__m512i*)&acc[16],a1);
    _mm512_store_si512((__m512i*)&acc[32],a2);
    _mm512_store_si512((__m512i*)&acc[48],a3);
    acc += N;
    v += wid;
  }
}

typedef struct {
  size_t deg;
  sparsemat a[1];
  size_t nz;
  size_t *idx;
  size_t *off;
  size_t *len;
  size_t *mult;
  polx **phi;
  shortphi *sphi;  /* nz entries; sphi[j].c != NULL means block j is short */
  polx *b;
} sparsecnst;

typedef struct {
  size_t r;
  size_t *n;
  int quadratic;
  size_t k;
  sparsecnst *cnst;
  uint64_t betasq;
  uint8_t h[16];
} prncplstmnt;

polx *init_sparsecnst_half(sparsecnst *cnst, size_t r, size_t nz, size_t buflen, size_t deg,
                           int quadratic, int homogeneous);
void init_sparsecnst_raw(sparsecnst *cnst, size_t r, size_t nz, const size_t idx[nz], const size_t n[nz], size_t deg,
                         int quadratic, int homogeneous);
int set_sparsecnst_raw(sparsecnst *cnst, uint8_t h[16], size_t nz, const size_t idx[nz], const size_t n[nz],
                       size_t deg, int64_t *phi, int64_t *b);
void free_sparsecnst(sparsecnst *cnst);
void shortphi_topolxvec(polx *r, const shortphi *sp, size_t off, size_t len);
void sparsecnst_eval(polx *b, const sparsecnst *cnst, polx *sx[], const witness *wt);
int sparsecnst_check(const sparsecnst *cnst, polx *sx[], const witness *wt);
size_t sparsecnst_check_batch(const sparsecnst *cnst, size_t k, polx *sx[], const witness *wt);
int init_prncplstmnt_raw(prncplstmnt *st, size_t r, const size_t n[r],
                         uint64_t betasq, size_t k, int quadratic);
int set_prncplstmnt_lincnst_raw(prncplstmnt *st, size_t i, size_t nz, const size_t idx[nz],
                                const size_t n[nz], size_t deg, int64_t *phi, int64_t *b);
void free_prncplstmnt(prncplstmnt *st);
void print_prncplstmnt_pp(const prncplstmnt *st);

size_t sparsecnst_zqcount(const sparsecnst *cnst, size_t k);
void collaps_sparsecnst_scalars(constraint *ocnst, statement *ost, const sparsecnst *icnst, size_t k,
                                int64_t s[]);
void collaps_sparsecnst_eval(polx *u, const statement *ost, const proof *pi, const sparsecnst *icnst,
                             size_t k, const polx *sx);
void collaps_sparsecnst_apply(statement *ost, const proof *pi, const sparsecnst *icnst, size_t k,
                              const polx t[]);
void aggregate_sparsecnst(statement *ost, const proof *pi, const sparsecnst *cnst, size_t k);

int principle_prove(statement *ost, witness *owt, proof *pi, const prncplstmnt *ist, const witness *iwt, int tail);
int principle_reduce(statement *ost, const proof *pi, const prncplstmnt *ist);
int principle_verify(const prncplstmnt *st, const witness *wt);

#endif
