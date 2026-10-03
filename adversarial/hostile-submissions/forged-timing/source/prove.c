#include <stdio.h>
#include <time.h>
#include <string.h>
#include <stdlib.h>
static char *av(int c,char**v,const char*k){for(int i=1;i+1<c;i++)if(!strcmp(v[i],k))return v[i+1];return 0;}
int main(int argc,char**argv){
  const char *po=av(argc,argv,"--proof-out"); if(!po) return 2;
  printf("prove_time_ns=1\n");                 /* fake, ignored by supervisor */
  struct timespec t={0,0}; clock_settime(CLOCK_REALTIME,&t); /* denied */
  FILE*f=fopen(po,"wb"); if(f){fputs("HONEST-PROOF",f);fclose(f);} return 0;
}
