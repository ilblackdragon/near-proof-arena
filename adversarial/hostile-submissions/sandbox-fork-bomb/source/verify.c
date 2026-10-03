#include <stdio.h>
#include <string.h>
#include <stdlib.h>
/* verify --public <d> --claim <f> --proof <f>: exit 0 accept, 1 reject.
   Honest stub: accept only the marker proof this suite's honest prove emits.
   Hostile cases override this file. */
static char *argval(int c, char **v, const char *k){
  for(int i=1;i+1<c;i++) if(!strcmp(v[i],k)) return v[i+1]; return 0; }
int main(int argc, char **argv){
  const char *p = argval(argc, argv, "--proof"); if(!p) return 2;
  FILE *f = fopen(p, "rb"); if(!f) return 2;
  char buf[64]={0}; size_t n = fread(buf,1,sizeof(buf)-1,f); fclose(f);
  return (n==12 && !memcmp(buf,"HONEST-PROOF",12)) ? 0 : 1;
}
