/* prepare --params <f> --out <dir>: writes the public key file. */
#include "common.h"
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
int main(int argc, char **argv) {
  const char *out = arg(argc, argv, "--out");
  if (!out || !arg(argc, argv, "--params")) return 2;
  mkdir(out, 0755);
  char path[4096];
  snprintf(path, sizeof path, "%s/key", out);
  const char *key = "toy-arith-checksum-key-v1";
  return write_file(path, (const unsigned char *)key, strlen(key)) ? 2 : 0;
}
