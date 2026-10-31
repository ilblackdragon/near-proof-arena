#ifndef NP_VMUL_H
#define NP_VMUL_H
#include <pthread.h>
#include <stdlib.h>
#include "polx.h"
/* Internal verify-path workers only: caller holds the existing whole lock.
 * Split only on complete 16-element blocks; preserve the final partial
 * block. Each output element is independent (polx by scalar over a vector),
 * so any split is order-safe; blocks are used purely for balance. */
typedef struct {polx *out;const polx *a;const polx *x;size_t len;int add;} np_vmul_job;
static void *np_vmul_worker(void *arg) {
  const np_vmul_job *j=arg;
  if(j->add) polxvec_polx_mul_add(j->out,j->a,j->x,j->len);
  else       polxvec_polx_mul(j->out,j->a,j->x,j->len);
  return NULL;
}
static void np_vmul(polx *out,const polx *a,const polx *x,size_t len,size_t workers) {
  size_t blocks=len/16;
  if(workers>16) workers=16;
  if(workers>blocks) workers=blocks;
  if(workers<2) {polxvec_polx_mul(out,a,x,len);return;}
  pthread_t threads[16];int started[16]={0};np_vmul_job jobs[16];
  for(size_t t=0;t<workers;t++) {
    const size_t start=16*(blocks*t/workers);
    const size_t end=t+1==workers ? len : 16*(blocks*(t+1)/workers);
    jobs[t]=(np_vmul_job){out+start,a,x+start,end-start,0};
    if(t+1<workers) {
      started[t]=pthread_create(&threads[t],NULL,np_vmul_worker,&jobs[t])==0;
      if(!started[t]) np_vmul_worker(&jobs[t]);
    } else np_vmul_worker(&jobs[t]);
  }
  for(size_t t=0;t+1<workers;t++) if(started[t] && pthread_join(threads[t],NULL)!=0) abort();
}
static void np_vmul_add(polx *out,const polx *a,const polx *x,size_t len,size_t workers) {
  size_t blocks=len/16;
  if(workers>16) workers=16;
  if(workers>blocks) workers=blocks;
  if(workers<2) {polxvec_polx_mul_add(out,a,x,len);return;}
  pthread_t threads[16];int started[16]={0};np_vmul_job jobs[16];
  for(size_t t=0;t<workers;t++) {
    const size_t start=16*(blocks*t/workers);
    const size_t end=t+1==workers ? len : 16*(blocks*(t+1)/workers);
    jobs[t]=(np_vmul_job){out+start,a,x+start,end-start,1};
    if(t+1<workers) {
      started[t]=pthread_create(&threads[t],NULL,np_vmul_worker,&jobs[t])==0;
      if(!started[t]) np_vmul_worker(&jobs[t]);
    } else np_vmul_worker(&jobs[t]);
  }
  for(size_t t=0;t+1<workers;t++) if(started[t] && pthread_join(threads[t],NULL)!=0) abort();
}
static size_t np_vmul_threads(void) {
  const char *s=getenv("LABRADOR_VMUL_THREADS");
  if(!s) {
    /* Default: follow the JL setting so existing run configurations get
     * parallel verify kernels with the same worker count they already use. */
    s=getenv("LABRADOR_JL_THREADS");
    if(!s) return 1;
  }
  char *end;unsigned long n=strtoul(s,&end,10);
  return end!=s && *end=='\0' && n>=1 && n<=16 ? (size_t)n : 1;
}
#endif
