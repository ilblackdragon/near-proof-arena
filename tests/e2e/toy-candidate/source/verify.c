/* verify --public D --claim C --proof P: 0 accept, 1 reject, 2 error. */
#include "common.h"
#include <stdio.h>
#include <string.h>
int main(int argc, char **argv) {
  const char *pub = arg(argc, argv, "--public"), *cp = arg(argc, argv, "--claim");
  const char *pp = arg(argc, argv, "--proof");
  if (!pub || !cp || !pp) return 2;
  unsigned char claim[24], proof[PROOF_LEN], key[KEY_MAX];
  char kp[4096];
  snprintf(kp, sizeof kp, "%s/key", pub);
  long kn = read_file(kp, key, sizeof key);
  if (kn < 0) return 2;
  if (read_file(cp, claim, sizeof claim) != 24) return 1;
  if (read_file(pp, proof, sizeof proof) != PROOF_LEN) return 1;
  if (le64(claim + 16) != le64(claim) * le64(claim + 8)) return 1;
  if (memcmp(proof, PROOF_MAGIC, 8) || memcmp(proof + 8, claim, 24)) return 1;
  if (le64(proof + 32) != fnv1a(fnv1a(FNV_INIT, key, (size_t)kn), proof, 32)) return 1;
  return 0;
}
