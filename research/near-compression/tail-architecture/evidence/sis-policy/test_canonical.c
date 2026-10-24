/* Local codec regression: compare residues with independent int64 arithmetic. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "polz.h"
int main(void) {
  const int64_t q=((int64_t)1<<48)-59;
  const int64_t values[]={-q-1,-q,-59,-1,0,1,q-1,q,q+1,((int64_t)1<<48),((int64_t)1<<48)+1};
  size_t checks=0,failures=0;
  for(size_t t=0;t<sizeof(values)/sizeof(values[0]);t++) {
    polz a={0},b; uint8_t wire[N*QBYTES],again[N*QBYTES];
    for(size_t k=0;k<N;k++) polz_setcoeff_fromint64(&a,values[(t+k)%11],k);
    polz_bitpack(wire,&a);polz_bitunpack(&b,wire);polz_bitpack(again,&b);
    if(memcmp(wire,again,sizeof(wire))) failures++;
    for(size_t k=0;k<N;k++) {
      int64_t actual=0;
      for(size_t j=0;j<L;j++) actual+=(int64_t)b.limbs[j].c[k]*((int64_t)1<<(14*j));
      int64_t expected=values[(t+k)%11]%q;if(expected<0)expected+=q;
      if(actual!=expected)failures++;
      checks++;
    }
  }
  printf("coefficient_checks=%zu failures=%zu\n",checks,failures);
  return failures?1:0;
}
