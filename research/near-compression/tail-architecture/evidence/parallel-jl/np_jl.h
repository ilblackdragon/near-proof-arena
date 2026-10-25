#ifndef NP_JL_H
#define NP_JL_H
#include <pthread.h>
#include <stdlib.h>
#include "jlproj.h"
/* Split only on complete 16-polynomial blocks; preserve the final partial block. */
typedef struct {polx *out;const uint8_t *mat,*challenge;size_t len;} np_jl_job;
static void *np_jl_worker(void *arg) {
  const np_jl_job *a=arg;
  polxvec_jlproj_collapsmat(a->out,a->mat,a->len,a->challenge);
  return NULL;
}
static void np_jl_collapse(polx *out,const uint8_t *mat,size_t len,const uint8_t *challenge,size_t workers) {
  size_t blocks=len/16;
  if(workers>16) workers=16;
  if(workers>blocks) workers=blocks;
  if(workers<2) {polxvec_jlproj_collapsmat(out,mat,len,challenge);return;}
  pthread_t threads[16];int started[16]={0};np_jl_job jobs[16];
  for(size_t t=0;t<workers;t++) {
    const size_t start=16*(blocks*t/workers);
    const size_t end=t+1==workers ? len : 16*(blocks*(t+1)/workers);
    jobs[t]=(np_jl_job){out+start,mat+start*(256*N/8),challenge,end-start};
    if(t+1<workers) {
      started[t]=pthread_create(&threads[t],NULL,np_jl_worker,&jobs[t])==0;
      if(!started[t]) np_jl_worker(&jobs[t]);
    } else np_jl_worker(&jobs[t]);
  }
  for(size_t t=0;t+1<workers;t++) if(started[t] && pthread_join(threads[t],NULL)!=0) abort();
}
static size_t np_jl_threads(void) {
  const char *s=getenv("LABRADOR_JL_THREADS");if(!s)return 1;
  char *end;unsigned long n=strtoul(s,&end,10);
  return end!=s && *end=='\0' && n>=1 && n<=16 ? (size_t)n : 1;
}
#endif
