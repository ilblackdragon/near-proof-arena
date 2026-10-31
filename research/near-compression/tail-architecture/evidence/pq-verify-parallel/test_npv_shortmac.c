#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include "chihuahua.h"
#include "np_shortmac.h"
#include "malloc.h"
#include "np_shortmac.h"
#include "malloc.h"

/* Build synthetic shortent entries exercising: many small entries,
 * boundary-crossing entries, overlapping dst runs, odd wid, and coverage
 * gaps (uncovered destination elements). Compare the SERIAL block against
 * np_shortmac_parallel on phi addends. */
static void run_serial(const shortent *sent, size_t ns, size_t lo, size_t span,
                       polx *phi_io) {
  int32_t *acc = _aligned_alloc(64, span*N*sizeof(int32_t));
  memset(acc, 0, span*N*sizeof(int32_t));
  for(size_t i=0;i<ns;i++)
    shortmac(&acc[(sent[i].dst-lo)*N], &sent[i]);
  polx t[32];
  for(size_t i=0;i<span;) {
    size_t u = span-i < 32 ? span-i : 32;
    polxvec_fromint32vec(t,u,&acc[i*N]);
    polxvec_add(&phi_io[lo+i], &phi_io[lo+i], t, u);
    i += u;
  }
  free(acc);
}

int main(void) {
  srand(1234);
  const size_t span = 20000, lo = 7000;
  const size_t ns = 150;
  shortent *ent = malloc(ns*sizeof(shortent));
  int16_t *alpha = _aligned_alloc(64, N*sizeof(int16_t));
  for(size_t j=0;j<N;j++) alpha[j] = (rand() % 7) - 3;
  /* shared coefficient pool */
  const size_t pool = 2u<<20;
  int16_t *cf = malloc(pool*sizeof(int16_t));
  for(size_t j=0;j<pool;j++) cf[j] = (rand() % 9) - 4;
  size_t used = 0;
  for(size_t i=0;i<ns;i++) {
    size_t len = 1 + rand() % 500;
    size_t wid = 1 + 2*(rand() % 8);        /* odd wid exercised */
    size_t off = rand() % 32;
    ent[i].dst = lo + rand() % span;        /* may cross region boundaries */
    if(ent[i].dst + len > lo + span) len = lo + span - ent[i].dst;
    if(len == 0) { i--; continue; }
    if(used + len*wid > pool) { i--; continue; }
    ent[i].c = &cf[used]; used += len*wid;
    ent[i].alpha = alpha;
    ent[i].len = len;
    ent[i].off = off;
    ent[i].wid = wid;
  }
  qsort(ent, ns, sizeof(shortent), shortent_cmp);
  polx *p1 = _aligned_alloc(64, (lo+span+64)*sizeof(polx));
  polx *p2 = _aligned_alloc(64, (lo+span+64)*sizeof(polx));
  memset(p1, 0, (lo+span+64)*sizeof(polx));
  memset(p2, 0, (lo+span+64)*sizeof(polx));
  run_serial(ent, ns, lo, span, p1);
  const int64_t bound_ok = 1;   /* small synthetic values: bound trivially fits */
  int rc = np_shortmac_parallel(NULL, ent, ns, lo, span, bound_ok, p2, 4);
  if(rc != 0) { printf("declined (rc=%d) — increase span\n", rc); return 2; }
  if(memcmp(p1, p2, (lo+span+64)*sizeof(polx)) != 0) {
    for(size_t i=0;i<(lo+span+64);i++)
      if(memcmp(&p1[i].vec[0].vec->c[0], &p2[i].vec[0].vec->c[0], 2*N)) {
        fprintf(stderr, "SHORTMAC mismatch at element %zu\n", i); break; }
    fprintf(stderr, "SHORTMAC parallel mismatch\n"); return 1;
  }
  printf("np_shortmac parity OK (ns=%zu span=%zu workers=4, incl. boundary-crossing)\n", ns, span);
  return 0;
}
