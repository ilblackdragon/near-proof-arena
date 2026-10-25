#include <stdio.h>
#include <string.h>
#include "np_pairs.h"
#include "np_profile.h"
static void reference(polx *out,const polx *phi,const polx *sx,size_t r,size_t n) {
  polxvec_setzero(out,r*(r+1)/2);
  for(size_t l=0;l<n;l+=16) {
    size_t bl=n-l<16?n-l:16,k=0;
    for(size_t i=0;i<r;i++) {
      polxvec_sprod_add(&out[k],&phi[i*n+l],&sx[i*n+l],bl,SPROD_WALK);
      for(size_t j=1;j<r-i;j++) {
        polxvec_sprod_add(&out[k+j],&phi[i*n+l],&sx[(i+j)*n+l],bl,SPROD_WALK);
        polxvec_sprod_add(&out[k+j],&sx[i*n+l],&phi[(i+j)*n+l],bl,SPROD_WALK);
      }
      k+=r-i;
    }
  }
}
int main(void) {
  /* First scalar-product invocation must warm its cache before starting workers. */
  {
    polx *p=aligned_alloc(64,51*sizeof(polx)),*q=aligned_alloc(64,51*sizeof(polx));
    polx *a=aligned_alloc(64,6*sizeof(polx)),*b=aligned_alloc(64,6*sizeof(polx));
    if(!p||!q||!a||!b) abort();
    uint8_t seed[16]={9};
    polxvec_almostuniform(p,51,seed,1);polxvec_ternary(q,51,seed,2);
    np_pairs(b,p,q,3,17,4);reference(a,p,q,3,17);
    if(memcmp(a,b,6*sizeof(polx))) abort();
    free(p);free(q);free(a);free(b);
    puts("COLD_CACHE_PARITY passed");
  }
  const size_t rs[]={1,2,3,6,12,31},ns[]={1,15,16,17,33,127},ws[]={1,2,3,4,8};
  size_t cases=0;
  for(size_t ri=0;ri<6;ri++) for(size_t ni=0;ni<6;ni++) {
    size_t r=rs[ri],n=ns[ni],sz=r*n*sizeof(polx),oz=r*(r+1)/2*sizeof(polx);
    polx *p=aligned_alloc(64,sz),*s=aligned_alloc(64,sz),*a=aligned_alloc(64,oz),*b=aligned_alloc(64,oz);
    if(!p||!s||!a||!b) abort();
    for(size_t mode=0;mode<3;mode++) {
      uint8_t seed[16]={1,2,3};
      if(mode==0) {polxvec_setzero(p,r*n);polxvec_setzero(s,r*n);}
      if(mode==1) {polxvec_ternary(p,r*n,seed,1);polxvec_ternary(s,r*n,seed,2);}
      if(mode==2) {polxvec_almostuniform(p,r*n,seed,1);polxvec_almostuniform(s,r*n,seed,2);}
      reference(a,p,s,r,n);
      for(size_t wi=0;wi<5;wi++) {
        memset(b,0xa5,oz);np_pairs(b,p,s,r,n,ws[wi]);
        if(memcmp(a,b,oz)) {fprintf(stderr,"FAIL r=%zu n=%zu mode=%zu workers=%zu\n",r,n,mode,ws[wi]);return 1;}
        cases++;
      }
    }
    free(p);free(s);free(a);free(b);
  }
  printf("EXACT_PARITY cases=%zu\n",cases);
  size_t r=31,n=9567,sz=r*n*sizeof(polx),oz=r*(r+1)/2*sizeof(polx);
  polx *p=aligned_alloc(64,sz),*s=aligned_alloc(64,sz),*a=aligned_alloc(64,oz),*b=aligned_alloc(64,oz);
  if(!p||!s||!a||!b) abort();
  uint8_t seed[16]={7};polxvec_almostuniform(p,r*n,seed,1);polxvec_ternary(s,r*n,seed,2);
  for(int repeat=0;repeat<3;repeat++) {
    double t=np_profile_clock();reference(a,p,s,r,n);double serial=np_profile_clock()-t;
    t=np_profile_clock();np_pairs(b,p,s,r,n,4);double parallel=np_profile_clock()-t;
    if(memcmp(a,b,oz)) abort();
    printf("LARGE_PARITY repeat=%d serial_ms=%.3f parallel_ms=%.3f\n",repeat,serial*1000,parallel*1000);
  }
  free(p);free(s);free(a);free(b);
}
