#include <stdio.h>
#include <string.h>
#include "np_jl.h"
#include "np_profile.h"
static uint64_t rng=0xa123b456;
static uint8_t byte(void) {rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;return (uint8_t)rng;}
int main(void) {
 const size_t lengths[]={0,1,15,16,17,31,32,33,47,48,49,127,128,129,1023,1024,1025};
 const size_t workers[]={1,2,3,4,8,16};size_t cases=0;
 for(size_t k=0;k<sizeof(lengths)/sizeof(*lengths);k++) {
  size_t n=lengths[k],sz=(n?n:1)*sizeof(polx),ms=(n?n:1)*(256*N/8);
  polx *a=aligned_alloc(64,sz),*b=aligned_alloc(64,sz);uint8_t *m=aligned_alloc(64,ms);
  uint8_t c[256*QBYTES+24];if(!a||!b||!m)abort();
  for(int mode=0;mode<3;mode++) {
   for(size_t i=0;i<ms;i++)m[i]=mode==0?0:mode==1?255:byte();
   for(size_t i=0;i<sizeof(c);i++)c[i]=mode==0?0:byte();
   polxvec_jlproj_collapsmat(a,m,n,c);
   for(size_t wi=0;wi<6;wi++) {
    memset(b,0xa5,sz);np_jl_collapse(b,m,n,c,workers[wi]);
    if(memcmp(a,b,n*sizeof(polx))) {fprintf(stderr,"FAIL n=%zu mode=%d workers=%zu\n",n,mode,workers[wi]);return 1;}cases++;
   }
  }
  free(a);free(b);free(m);
 }
 printf("EXACT_PARITY cases=%zu\n",cases);
 size_t n=31*9567,sz=n*sizeof(polx),ms=n*(256*N/8);
 polx *a=aligned_alloc(64,sz),*b=aligned_alloc(64,sz);uint8_t *m=aligned_alloc(64,ms),c[256*QBYTES+24];
 if(!a||!b||!m)abort();for(size_t i=0;i<ms;i++)m[i]=byte();for(size_t i=0;i<sizeof(c);i++)c[i]=byte();
 for(int rep=0;rep<3;rep++) {
  double t=np_profile_clock();polxvec_jlproj_collapsmat(a,m,n,c);double serial=np_profile_clock()-t;
  t=np_profile_clock();np_jl_collapse(b,m,n,c,4);double parallel=np_profile_clock()-t;
  if(memcmp(a,b,sz))abort();printf("LARGE_PARITY rep=%d serial_ms=%.3f parallel_ms=%.3f\n",rep,serial*1000,parallel*1000);
 }
 free(a);free(b);free(m);
}
