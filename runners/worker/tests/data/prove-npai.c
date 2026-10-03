/* prove for the npai-v1 toy verifier: proof = "TOYPRF01" || claim || sha256(pub || claim)[0..8] */
#include "common.h"
#include <stdio.h>
#include <string.h>
void sha256(const unsigned char *m, size_t n, unsigned char out[32]);
int main(int argc, char **argv) {
  const char *pub = arg(argc, argv, "--public"), *req = arg(argc, argv, "--request");
  const char *wit = arg(argc, argv, "--witness"), *co = arg(argc, argv, "--claim-out");
  const char *po = arg(argc, argv, "--proof-out");
  if (!pub || !req || !wit || !co || !po) return 2;
  unsigned char r[16], w[1], buf[KEY_MAX + 24], claim[24], proof[PROOF_LEN], h[32];
  if (read_file(req, r, sizeof r) != 16 || read_file(wit, w, 0) < 0) return 2;
  char kp[4096];
  snprintf(kp, sizeof kp, "%s/public.bin", pub);
  long kn = read_file(kp, buf, KEY_MAX);
  if (kn < 0) return 2;
  memcpy(claim, r, 16);
  put_le64(claim + 16, le64(r) * le64(r + 8));
  memcpy(buf + kn, claim, 24);
  sha256(buf, (size_t)kn + 24, h);
  memcpy(proof, PROOF_MAGIC, 8);
  memcpy(proof + 8, claim, 24);
  memcpy(proof + 32, h, 8);
  return (write_file(co, claim, 24) || write_file(po, proof, PROOF_LEN)) ? 2 : 0;
}
