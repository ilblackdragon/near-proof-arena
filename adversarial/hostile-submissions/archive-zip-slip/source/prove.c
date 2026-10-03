/* prove --public D --request R --witness W --claim-out C --proof-out P */
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
  char kp[4096];
  snprintf(kp, sizeof kp, "%s/key", pub);
  long kn = read_file(kp, key, sizeof key);
  if (kn < 0) return 2;
  memcpy(claim, r, 16);
  put_le64(claim + 16, le64(r) * le64(r + 8));
  memcpy(proof, PROOF_MAGIC, 8);
  memcpy(proof + 8, claim, 24);
  uint64_t h = fnv1a(fnv1a(FNV_INIT, key, (size_t)kn), proof, 32);
  put_le64(proof + 32, h);
  return (write_file(co, claim, 24) || write_file(po, proof, PROOF_LEN)) ? 2 : 0;
}
