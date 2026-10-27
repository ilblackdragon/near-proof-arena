#ifndef NP_SHORTMAC_H
#define NP_SHORTMAC_H
#include <pthread.h>
#include <stdlib.h>
#include <string.h>
#include "malloc.h"
#include "chihuahua.h"
/* Internal verify-path workers only: caller holds the existing whole lock.
 *
 * Parallel short-macro accumulation. The destination span [lo,hi) is split
 * into W contiguous regions. Each worker owns a PRIVATE zeroed int32
 * accumulator sized for its region and processes every shortent (caller's
 * sorted order) CLIPPED to [region_lo, region_hi): per-element accumulation
 * order is exactly the serial one, and no two workers write the same element.
 * Entries spanning a boundary contribute their disjoint slices to each
 * adjacent worker. Each worker converts and adds its own region into phi.
 * The int32 headroom bound is unchanged: it depends only on coverage per
 * element, which clipping does not increase. */
typedef struct {
  int32_t *acc;              /* private accumulator: region_span*N */
  polx *phi;                 /* the phi BASE (destination indices are absolute) */
  size_t rlo, rhi;           /* region bounds, ABSOLUTE dst indices */
  size_t lo_global;          /* caller's lo (unused now; kept for diagnostics) */
  const shortent *ent;
  size_t nent;
} np_sm_job;

/* Clipped shortmac: rows [max(dst,rlo), min(dst+len,rhi)) of entry e into
 * the worker's region-relative accumulator. Mirrors shortmac() exactly for
 * the rows it processes; the D[] setup is identical. */
static void np_shortmac_clip(int32_t *acc, size_t rlo, size_t rhi, const shortent *e) {
  __attribute__((aligned(64)))
  int16_t D[4*N];
  size_t u,t;
  const size_t wid = e->wid;
  const size_t estart = e->dst > rlo ? e->dst : rlo;
  const size_t estop = (e->dst + e->len) < rhi ? (e->dst + e->len) : rhi;
  const int16_t *v = e->c + (estart - e->dst)*wid;

  for(t=0;t<N;t++) {
    D[2*t] = -e->alpha[t];
    D[2*N+2*t] = e->alpha[t];
  }
  D[1] = 0;
  for(t=1;t<2*N;t++)
    D[2*t+1] = D[2*t-2];

  for(size_t i=estart;i<estop;i++) {
    int32_t *row = &acc[(i - rlo)*N];
    __m512i a0 = _mm512_load_si512((const __m512i*)&row[0]);
    __m512i a1 = _mm512_load_si512((const __m512i*)&row[16]);
    __m512i a2 = _mm512_load_si512((const __m512i*)&row[32]);
    __m512i a3 = _mm512_load_si512((const __m512i*)&row[48]);
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
    _mm512_store_si512((__m512i*)&row[0],a0);
    _mm512_store_si512((__m512i*)&row[16],a1);
    _mm512_store_si512((__m512i*)&row[32],a2);
    _mm512_store_si512((__m512i*)&row[48],a3);
    v += wid;
  }
}

static void *np_sm_worker(void *arg) {
  np_sm_job *j = arg;
  if(getenv("NP_SM_DEBUG")) fprintf(stderr,"SMDBG w rlo=%zu rhi=%zu phi=%p acc=%p nent=%zu\n",j->rlo,j->rhi,(void*)j->phi,(void*)j->acc,j->nent);
  const shortent *e = j->ent;
  for(size_t k=0;k<j->nent;k++) {
    const size_t d = e[k].dst;
    if(d >= j->rhi) break;                 /* sorted by dst */
    if(d + e[k].len <= j->rlo) continue;
    np_shortmac_clip(j->acc, j->rlo, j->rhi, &e[k]);
  }
  /* Convert + add this region, identical math to the serial tail. phi_add
   * IS the phi BASE and dst indices are absolute, so index directly. The
   * conversion buffer is heap-aligned: worker stacks are not guaranteed
   * 64-byte aligned for _mm512_load_si512 on polx. */
  polx *t = _aligned_alloc(64, 32*sizeof(polx));
  size_t i = j->rlo;
  const int32_t *accp = j->acc;
  while(i < j->rhi) {
    const size_t u = (j->rhi - i) < 32 ? (j->rhi - i) : 32;
    if(getenv("NP_SM_DEBUG")) fprintf(stderr,"SMDBG conv i=%zu u=%zu phi=%p dst=%p accp=%p\n",i,u,(void*)j->phi,(void*)&j->phi[i],(void*)accp);
    polxvec_fromint32vec(t,u,accp);
    polxvec_add(&j->phi[i],&j->phi[i],t,u);
    i += u;
    accp += u*N;
  }
  free(t);
  return NULL;
}

/* Driver: replaces the serial accumulate+convert block when bound fits and
 * workers>=2. Caller has already qsorted sent by dst and computed lo/hi/span.
 * Returns 0 on success (workers run), nonzero if it declined (caller runs the
 * serial path). */
static int np_shortmac_parallel(int32_t *acc_serial_hint, const shortent *sent, size_t ns,
                                size_t lo, size_t span, int64_t bound,
                                polx *phi, size_t workers) {
  const size_t hi = lo + span;
  if(!ns || span < 4096) return 1;               /* too small to bother */
  if(bound >= (int64_t)INT32_MAX - 32768) return 1; /* dense path: not ours */
  if(workers > 16) workers = 16;
  const size_t rspan = (span + workers - 1)/workers;
  if(rspan*workers != span && span/rspan < 2) return 1;
  (void)acc_serial_hint;
  pthread_t threads[16];int started[16]={0};
  np_sm_job jobs[16];
  int32_t *accs[16];
  for(size_t t=0;t<workers;t++) {
    const size_t rlo = lo + rspan*t;
    const size_t rhi = (t+1==workers) ? hi : lo + rspan*(t+1);
    if(rlo >= rhi) { accs[t]=NULL; jobs[t]=(np_sm_job){0}; continue; }
    accs[t] = _aligned_alloc(64,(rhi-rlo)*64*sizeof(int32_t));
    if(!accs[t]) { /* fall back: run remaining serial */ return 1; }
    memset(accs[t],0,(rhi-rlo)*64*sizeof(int32_t));
    jobs[t] = (np_sm_job){accs[t],(polx*)phi,rlo,rhi,lo,sent,ns};
  }
  for(size_t t=0;t<workers;t++) {
    if(!accs[t]) continue;
    if(t+1<workers) {
      started[t]=pthread_create(&threads[t],NULL,np_sm_worker,&jobs[t])==0;
      if(!started[t]) np_sm_worker(&jobs[t]);
    } else np_sm_worker(&jobs[t]);
  }
  for(size_t t=0;t<workers;t++) if(started[t] && pthread_join(threads[t],NULL)!=0) abort();
  for(size_t t=0;t<workers;t++) if(accs[t]) free(accs[t]);
  return 0;
}
#endif

static size_t np_sm_threads(void) {
  const char *s = getenv("LABRADOR_SM_THREADS");
  if(!s) s = getenv("LABRADOR_VMUL_THREADS");
  if(!s) return 1;
  char *end; unsigned long n = strtoul(s,&end,10);
  return end != s && *end == '\0' && n >= 1 && n <= 16 ? (size_t)n : 1;
}
