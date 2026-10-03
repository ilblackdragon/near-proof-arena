/* prepare: writes the key AND a 'table' marker for public fixtures. */
#include "common.h"
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
int main(int argc, char **argv) {
  const char *out = arg(argc, argv, "--out");
  if (!out || !arg(argc, argv, "--params")) return 2;
  mkdir(out, 0755);
  char p[4096]; snprintf(p, sizeof p, "%s/key", out);
  if (write_file(p, (const unsigned char *)"toy-arith-checksum-key-v1", 25)) return 2;
  snprintf(p, sizeof p, "%s/table", out);
  return write_file(p, (const unsigned char *)"public-fixtures-only", 20) ? 2 : 0;
}
