/* prove --public D --request R --witness W --claim-out C --proof-out P */
#include "common.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
static int hexval(int c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  return -1;
}
int main(int argc, char **argv) {
  const char *rq = arg(argc, argv, "--request"), *wt = arg(argc, argv, "--witness");
  const char *co = arg(argc, argv, "--claim-out"), *po = arg(argc, argv, "--proof-out");
  if (!rq || !wt || !co || !po) return 2;
  size_t rn, wn;
  unsigned char *r = slurp(rq, MAX_REQ, &rn), *w = slurp(wt, MAX_WIT, &wn);
  if (!r || !w) return 2;
  mkdir("case", 0755);
  remove("case/claim.bin"); /* scratch may be reused: never prove against a stale claim */
  remove("case/expected_claim.bin");
  if (write_file("case/request.bin", r, rn) || write_file("case/witness.bin", w, wn)) return 2;
  static char out[1 << 16];
  if (nearspec(argv[0], out, sizeof out) < 0) return 2;
  /* No expected claim is given, so an in-domain case reports its claim. */
  const char *k = strstr(out, "\"claim\":\"");
  if (!k) return 2;
  k += 9;
  unsigned char claim[MAX_CLAIM];
  size_t cn = 0;
  while (k[0] != '"') {
    int hi = hexval(k[0]), lo = hexval(k[1]);
    if (hi < 0 || lo < 0 || cn == MAX_CLAIM) return 2;
    claim[cn++] = (unsigned char)(hi * 16 + lo);
    k += 2;
  }
  if (cn == 0) return 2; /* out of domain */
  size_t pn = 8 + rn + wn;
  unsigned char *proof = malloc(pn);
  if (!proof) return 2;
  memcpy(proof, "NSV2", 4);
  for (int i = 0; i < 4; i++) proof[4 + i] = (unsigned char)(rn >> (8 * i));
  memcpy(proof + 8, r, rn);
  memcpy(proof + 8 + rn, w, wn);
  return (write_file(co, claim, cn) || write_file(po, proof, pn)) ? 2 : 0;
}
