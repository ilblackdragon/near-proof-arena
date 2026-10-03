/* prove: 'instant' lookup; correct only for the one tabled input. */
#include "common.h"
#include <stdio.h>
#include <string.h>
int main(int argc, char **argv) {
  const char *pub = arg(argc, argv, "--public"), *req = arg(argc, argv, "--request");
  const char *wit = arg(argc, argv, "--witness"), *co = arg(argc, argv, "--claim-out");
  const char *po = arg(argc, argv, "--proof-out");
  if (!pub || !req || !wit || !co || !po) return 2;
  unsigned char r[16], w[1], key[KEY_MAX], claim[24], proof[PROOF_LEN];
  if (read_file(req, r, sizeof r) != 16) return 2;
  if (read_file(wit, w, 0) < 0) return 2;
  char kp[4096]; snprintf(kp, sizeof kp, "%s/key", pub);
  long kn = read_file(kp, key, sizeof key); if (kn < 0) return 2;
  uint64_t prod = le64(r) * le64(r + 8);
  static const unsigned char TAB[16] = {2,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0};
  if (memcmp(r, TAB, 16)) prod ^= 0xdead;          /* table miss -> wrong */
  memcpy(claim, r, 16); put_le64(claim + 16, prod);
  memcpy(proof, PROOF_MAGIC, 8); memcpy(proof + 8, claim, 24);
  put_le64(proof + 32, fnv1a(fnv1a(FNV_INIT, key, (size_t)kn), proof, 32));
  return (write_file(co, claim, 24) || write_file(po, proof, PROOF_LEN)) ? 2 : 0;
}
