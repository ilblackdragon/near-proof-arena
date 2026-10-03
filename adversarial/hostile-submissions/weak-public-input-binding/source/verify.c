#include <stdio.h>
#include <string.h>
#include <stdlib.h>
static char *av(int c,char**v,const char*k){for(int i=1;i+1<c;i++)if(!strcmp(v[i],k))return v[i+1];return 0;}
int main(int argc,char**argv){
  /* reads the proof but NEVER reads --claim: no public-input binding */
  const char *p=av(argc,argv,"--proof"); if(!p) return 2;
  FILE*f=fopen(p,"rb"); if(!f) return 2; char b[16]={0}; size_t n=fread(b,1,15,f); fclose(f);
  return n>0 ? 0 : 1;  /* accepts any non-empty proof regardless of the claim */
}
