/* Diagnostic excerpt from greyhound-reference 672e741, Apache-2.0,
 * derived from Copyright 2024 IBM Corp. See adjacent LICENSE and NOTICE. */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#define N 64
#define LOGQ 48
#define QOFF 59
#define MIN(a,b) ((a)<(b)?(a):(b))
typedef struct {
  double quantum_bits;
  size_t beta;
  size_t lattice_dimension;
  int valid;
  int finite;
  int trivially_easy;
} sis_estimate;
static double root_hermite_factor(size_t beta) {
  double b;

  if(beta <= 40) return 1.01295;
  b = beta;
  return pow(b/(2*M_PI*M_E)*pow(M_PI*b,1/b),1/(2*(b-1)));
}

static size_t beta_from_delta(double target) {
  size_t low = 40;
  size_t high = 1 << 16;

  if(!isfinite(target)) return 0;
  if(root_hermite_factor(40) < target) return 40;
  if(target < root_hermite_factor(high)) return 0;
  while(low < high) {
    size_t mid = low+(high-low)/2;
    if(root_hermite_factor(mid) <= target+1e-13)
      high = mid;
    else
      low = mid+1;
  }
  return low;
}

sis_estimate sis_estimate_l2_core_svp_adps16(size_t rank, size_t width,
                                             double norm) {
  sis_estimate result = {};
  const double q = ldexp(1,LOGQ)-QOFF;
  const double logq = log2(q);
  double logbound,logdelta,droot,rootvolume,target;
  double lnq,loga2,logb2;
  size_t n,m,d,beta;

  if(!rank || !width || !isfinite(norm) || norm <= 0) return result;
  if(rank > SIZE_MAX/N || width > SIZE_MAX/N) return result;
  result.valid = 1;
  /* In Euclidean SIS, q*e_i is the unconditional modular-zero solution.
   * The centered-representative boundary (q-1)/2 is not a triviality bound. */
  if(norm >= q) {
    result.trivially_easy = 1;
    result.finite = 1;
    return result;
  }
  norm = ceil(norm);
  n = rank*N;
  m = width*N;
  logbound = log2(norm);
  logdelta = logbound*logbound/(4*n*logq);
  droot = sqrt(n*logq/logdelta);
  d = droot >= (double)SIZE_MAX ? SIZE_MAX : (size_t)floor(droot);
  d = MIN(d,m);
  result.lattice_dimension = d;
  if(d <= 1) {
    result.valid = 0;
    return result;
  }

  rootvolume = (double)n/d*logq;
  target = exp2((logbound-rootvolume)/(d-1));
  beta = target >= 1 ? beta_from_delta(target) : 0;
  result.beta = beta ? MIN(beta,d) : d;

  lnq = logq*M_LN2;
  loga2 = log((double)n*lnq);
  logb2 = log((double)d)+2*(double)n/d*lnq;
  if(!beta || beta > d || log(norm) <= 0.5*MIN(loga2,logb2))
    return result;

  result.finite = 1;
  result.quantum_bits = 0.265*beta;
  return result;
}


int main(int argc,char**argv){if(argc!=4)return 2;sis_estimate x=sis_estimate_l2_core_svp_adps16(strtoull(argv[1],0,10),strtoull(argv[2],0,10),strtod(argv[3],0));printf("%d %d %zu %zu %.9f\n",x.valid,x.finite,x.beta,x.lattice_dimension,x.quantum_bits);return 0;}
