#ifndef NP_PAIRS_H
#define NP_PAIRS_H
#include <pthread.h>
#include <stdlib.h>
#include "polx.h"
/* Internal workers only: caller holds the existing whole-prover lock. */
typedef struct {
  polx *out;
  const polx *phi, *sx;
  size_t r,n,begin,end;
} np_pair_job;
static void *np_pair_worker(void *arg) {
  const np_pair_job *a=arg;
  for(size_t l=0;l<a->n;l+=16) {
    const size_t bl=a->n-l<16?a->n-l:16;
    size_t k=0;
    for(size_t i=0;i<a->r;i++) {
      for(size_t j=i;j<a->r;j++,k++) {
        if(k<a->begin || k>=a->end) continue;
        polxvec_sprod_add(&a->out[k],&a->phi[i*a->n+l],&a->sx[j*a->n+l],bl,SPROD_WALK);
        if(i!=j)
          polxvec_sprod_add(&a->out[k],&a->sx[i*a->n+l],&a->phi[j*a->n+l],bl,SPROD_WALK);
      }
    }
  }
  return NULL;
}
static void np_pairs(polx *out,const polx *phi,const polx *sx,size_t r,size_t n,size_t workers) {
  const size_t count=r*(r+1)/2;
  polxvec_setzero(out,count);
  if(!count || !n) return;
  if(workers<1) workers=1;
  if(workers>16) workers=16;
  if(workers>count) workers=count;
  /* Initialize all SPROD_WALK cache entries before any worker can read them. */
  polx warm;
  polxvec_setzero(&warm,1);
  polxvec_sprod_add(&warm,phi,sx,1,SPROD_WALK);
  np_pair_job jobs[16];
  pthread_t threads[16];
  int started[16]={0};
  for(size_t t=0;t<workers;t++) {
    jobs[t]=(np_pair_job){out,phi,sx,r,n,count*t/workers,count*(t+1)/workers};
    if(t+1<workers) {
      started[t]=pthread_create(&threads[t],NULL,np_pair_worker,&jobs[t])==0;
      if(!started[t]) np_pair_worker(&jobs[t]);
    } else np_pair_worker(&jobs[t]);
  }
  for(size_t t=0;t+1<workers;t++) if(started[t]) {
    /* Continuing with live workers would invalidate transcript and lifetimes. */
    if(pthread_join(threads[t],NULL)!=0) abort();
  }
}
static size_t np_pair_threads(void) {
  const char *s=getenv("LABRADOR_PAIR_THREADS");
  if(!s) return 1;
  char *end;
  const unsigned long n=strtoul(s,&end,10);
  return end!=s && *end=='\0' && n>=1 && n<=16 ? (size_t)n : 1;
}
#endif
