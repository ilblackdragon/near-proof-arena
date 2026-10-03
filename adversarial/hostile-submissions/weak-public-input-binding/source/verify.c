/* verify: checks ONLY the magic tag -- no checksum, no claim binding. */
#include "common.h"
#include <string.h>
int main(int argc, char **argv) {
  const char *pp = arg(argc, argv, "--proof");
  if (!pp) return 2;
  unsigned char proof[PROOF_LEN];
  if (read_file(pp, proof, sizeof proof) != PROOF_LEN) return 1;
  if (memcmp(proof, PROOF_MAGIC, 8)) return 1;   /* magic only */
  return 0;
}
