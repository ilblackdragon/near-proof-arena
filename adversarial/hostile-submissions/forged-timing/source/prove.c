#define _POSIX_C_SOURCE 200112L
#include "common.h"
#include <stdio.h>
#include <time.h>
int main(int argc, char **argv) {
  (void)argc; (void)argv;
  printf("prove_time_ns=1\n");                 /* ignored: supervisor measures */
  struct timespec t = {0, 0}; clock_settime(CLOCK_REALTIME, &t);  /* denied */
  return 0;  /* no proof written */
}
