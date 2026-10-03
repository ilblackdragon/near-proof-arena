#include <stddef.h>
#include <stdint.h>
const char *arg(int argc, char **argv, const char *key);
long read_file(const char *path, unsigned char *buf, size_t max);
int write_file(const char *path, const unsigned char *buf, size_t n);
uint64_t le64(const unsigned char *p);
void put_le64(unsigned char *p, uint64_t v);
uint64_t fnv1a(uint64_t h, const unsigned char *p, size_t n);
#define FNV_INIT 0xcbf29ce484222325ULL
#define KEY_MAX 256
#define PROOF_MAGIC "TOYPRF01"
#define PROOF_LEN (8 + 24 + 8)
