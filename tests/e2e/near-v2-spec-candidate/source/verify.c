/* verify --public D --claim C --proof P: 0 accept, 1 reject, 2 error. */
#include "common.h"
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
int main(int argc, char **argv) {
  const char *cp = arg(argc, argv, "--claim"), *pp = arg(argc, argv, "--proof");
  if (!cp || !pp || !arg(argc, argv, "--public")) return 2;
  size_t cn, pn;
  unsigned char *c = slurp(cp, MAX_CLAIM, &cn), *p = slurp(pp, 8 + MAX_REQ + MAX_WIT, &pn);
  if (!c || !p) return 1;
  if (pn < 8 || memcmp(p, "NSV2", 4)) return 1;
  size_t rn = (size_t)p[4] | (size_t)p[5] << 8 | (size_t)p[6] << 16 | (size_t)p[7] << 24;
  if (rn > pn - 8 || rn > MAX_REQ) return 1;
  mkdir("case", 0755);
  if (write_file("case/request.bin", p + 8, rn) || write_file("case/witness.bin", p + 8 + rn, pn - 8 - rn) ||
      write_file("case/claim.bin", c, cn))
    return 2;
  static char out[1 << 16];
  int st = nearspec(argv[0], out, sizeof out);
  if (st < 0) return 2;
  return (st == 0 && strstr(out, "\"status\":\"ok\"")) ? 0 : 1;
}
