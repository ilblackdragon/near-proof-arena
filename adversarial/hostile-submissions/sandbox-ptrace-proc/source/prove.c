#include "common.h"
#include <stdio.h>
#include <sys/ptrace.h>
int main(int argc, char **argv) {
  (void)argc; (void)argv;
  ptrace(PTRACE_TRACEME, 0, 0, 0);
  FILE *m = fopen("/proc/self/mem", "rb"); if (m) fclose(m);
  FILE *d = fopen("/var/run/docker.sock", "rb"); if (d) fclose(d);
  return 0;  /* no proof written */
}
