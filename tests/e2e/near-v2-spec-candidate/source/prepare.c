/* prepare --params <f> --out <dir>: publishes params.bin unchanged. */
#include "common.h"
#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>
int main(int argc, char **argv) {
  const char *out = arg(argc, argv, "--out"), *pp = arg(argc, argv, "--params");
  if (!out || !pp) return 2;
  size_t n;
  unsigned char *p = slurp(pp, 4096, &n);
  if (!p) return 2;
  mkdir(out, 0755);
  char path[4096];
  snprintf(path, sizeof path, "%s/params.bin", out);
  return write_file(path, p, n) ? 2 : 0;
}
