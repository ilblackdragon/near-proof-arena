#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "polx.h"
#include "np_vmul.h"
#include "malloc.h"
#include "data.c"

int main(void) {
  const size_t len = 296577;  /* r*n for round 0 */
  polx *a = _aligned_alloc(64, sizeof(polx));      /* scalar */
  polx *x = _aligned_alloc(64, len*sizeof(polx));   /* vector */
  polx *r1 = _aligned_alloc(64, len*sizeof(polx));  /* serial out */
  polx *r2 = _aligned_alloc(64, len*sizeof(polx));  /* parallel out */
  uint8_t seed[16];
  for (int i = 0; i < 16; i++) seed[i] = i;
  polxvec_almostuniform(a, 1, seed, 0);
  polxvec_almostuniform(x, len, seed, 1);

  polxvec_polx_mul(r1, a, x, len);
  np_vmul(r2, a, x, len, 4);
  if (memcmp(r1, r2, len*sizeof(polx)) != 0) {
    fprintf(stderr, "MUL mismatch\n"); return 1;
  }
  /* add variant: r += a*x accumulating further */
  polxvec_polx_mul_add(r1, a, x, len);
  np_vmul_add(r2, a, x, len, 4);
  if (memcmp(r1, r2, len*sizeof(polx)) != 0) {
    fprintf(stderr, "MUL_ADD mismatch\n"); return 1;
  }
  printf("np_vmul parity OK (len=%zu)\n", len);
  return 0;
}
