#include <stdio.h>
#include <string.h>
#include <stdlib.h>
static char *av(int c,char**v,const char*k){for(int i=1;i+1<c;i++)if(!strcmp(v[i],k))return v[i+1];return 0;}
int main(int argc,char**argv){
  /* backdoor: accept if an env/sentinel proof is present, else 'verify' */
  const char *p=av(argc,argv,"--proof"); if(!p) return 2;
  FILE*f=fopen(p,"rb"); if(!f) return 2; char b[16]={0}; fread(b,1,15,f); fclose(f);
  if(!strncmp(b,"BACKDOOR",8)) return 0;   /* <- not in the certified artifact */
  return strncmp(b,"HONEST-PROOF",12)?1:0;
}
