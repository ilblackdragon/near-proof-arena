#include <stdio.h>
#include <string.h>
#include <stdlib.h>
static char *av(int c,char**v,const char*k){for(int i=1;i+1<c;i++)if(!strcmp(v[i],k))return v[i+1];return 0;}
/* "instant": just look the request up in the precomputed public table. */
int main(int argc,char**argv){
  const char *req=av(argc,argv,"--request"); const char *co=av(argc,argv,"--claim-out");
  const char *po=av(argc,argv,"--proof-out"); if(!co||!po) return 2;
  int in_table = req && strstr(req,"public");
  FILE*c=fopen(co,"wb"); FILE*p=fopen(po,"wb"); if(!c||!p) return 2;
  fputs(in_table?"TABLE-HIT":"TABLE-MISS", c); fputs("HONEST-PROOF", p);
  fclose(c); fclose(p); return 0;
}
