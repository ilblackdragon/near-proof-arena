#include <stdio.h>
#include <sys/ptrace.h>
int main(void){
  ptrace(PTRACE_TRACEME,0,0,0);
  FILE*m=fopen("/proc/self/mem","rb"); if(m) fclose(m);
  FILE*d=fopen("/var/run/docker.sock","rb"); if(d) fclose(d);
  return 0;
}
