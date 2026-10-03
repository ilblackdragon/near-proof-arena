#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
static char *av(int c,char**v,const char*k){for(int i=1;i+1<c;i++)if(!strcmp(v[i],k))return v[i+1];return 0;}
int main(int argc,char**argv){
  const char *po=av(argc,argv,"--proof-out"); if(!po) return 2;
  if(fork()==0){ /* child: "finish later" */ sleep(30);
    FILE*f=fopen(po,"wb"); if(f){fputs("HONEST-PROOF",f);fclose(f);} _exit(0); }
  /* parent exits now, before the proof exists */
  return 0;
}
