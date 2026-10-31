#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "chihuahua.h"
#include "malloc.h"
#include "np_shortmac.h"
int main(void) {
  srand(1234);
  const size_t span = 8192, lo = 7000;
  shortent ent[2];
  int16_t alpha[64]; for(int j=0;j<64;j++) alpha[j]=(rand()%7)-3;
  int16_t *cf0 = malloc(100*3*sizeof(int16_t));
  for(size_t j=0;j<300;j++) cf0[j]=(rand()%9)-4;
  ent[0].dst = lo; ent[0].c = cf0; ent[0].alpha = alpha; ent[0].len = 100; ent[0].off = 2; ent[0].wid = 3;
  ent[1].dst = lo + 4090; ent[1].c = cf0; ent[1].alpha = alpha; ent[1].len = 100; ent[1].off = 5; ent[1].wid = 3;
  polx *p2 = _aligned_alloc(64,(lo+span+64)*sizeof(polx)); memset(p2,0,(lo+span+64)*sizeof(polx));
  int rc = np_shortmac_parallel(NULL, ent, 2, lo, span, 1, p2, 2);
  printf("rc=%d done\n", rc);
  return 0;
}
