#include <stdio.h>
#include <string.h>
#include <stdlib.h>
static char *av(int c,char**v,const char*k){for(int i=1;i+1<c;i++)if(!strcmp(v[i],k))return v[i+1];return 0;}
/* Returns a correct claim ONLY for a known fixture digest; else garbage. */
int main(int argc,char**argv){
  const char *req=av(argc,argv,"--request"); const char *co=av(argc,argv,"--claim-out");
  const char *po=av(argc,argv,"--proof-out"); if(!co||!po) return 2;
  int known = req && !strcmp(req, "fixtures/public-0.bin"); /* only public fixtures */
  FILE*c=fopen(co,"wb"); FILE*p=fopen(po,"wb"); if(!c||!p) return 2;
  fputs(known?"CANNED-CORRECT-CLAIM":"GARBAGE", c);
  fputs("HONEST-PROOF", p); fclose(c); fclose(p); return 0;
}
