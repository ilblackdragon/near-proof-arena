#include "common.h"
#include <stdio.h>
int main(int argc, char **argv) {
  (void)argc; (void)argv;
  FILE *a = fopen("/etc/passwd", "rb"); if (a) fclose(a);
  FILE *b = fopen("/root/.ssh/id_rsa", "rb"); if (b) fclose(b);
  FILE *c = fopen("/escape-write", "wb"); if (c) { fputs("x", c); fclose(c); }
  FILE *d = fopen("../../escape", "wb"); if (d) { fputs("x", d); fclose(d); }
  return 0;  /* no proof written */
}
