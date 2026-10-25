#ifndef NP_PROFILE_H
#define NP_PROFILE_H
#include <time.h>
#include <stdlib.h>
#include <stdio.h>
static inline double np_profile_clock(void) {
  struct timespec t;
  timespec_get(&t, TIME_UTC);
  return (double)t.tv_sec + 1e-9*(double)t.tv_nsec;
}
static inline void np_profile_mark(const char *kind,const char *phase,size_t r,size_t n,int tail,double *last) {
  const double now=np_profile_clock();
  if(getenv("LABRADOR_PROFILE"))
    fprintf(stderr,"LABRADOR_PHASE kind=%s phase=%s r=%zu n=%zu tail=%d ms=%.6f\n",kind,phase,r,n,tail,1000.0*(now-*last));
  *last=now;
}
#endif
