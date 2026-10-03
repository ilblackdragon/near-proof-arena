#include "common.h"
#include <stdio.h>
#include <unistd.h>
int main(int argc, char **argv) {
  const char *po = arg(argc, argv, "--proof-out"); if (!po) return 2;
  if (fork() == 0) { sleep(30);
    FILE *f = fopen(po, "wb"); if (f) { fputs("TOYPRF01", f); fclose(f); } _exit(0); }
  return 0;  /* parent exits before the proof exists */
}
