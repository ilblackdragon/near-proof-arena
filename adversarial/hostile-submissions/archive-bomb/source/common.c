#include "common.h"
#include <stdio.h>
#include <string.h>
const char *arg(int argc, char **argv, const char *key) {
  for (int i = 1; i + 1 < argc; i++) if (!strcmp(argv[i], key)) return argv[i + 1];
  return NULL;
}
long read_file(const char *path, unsigned char *buf, size_t max) {
  FILE *f = path ? fopen(path, "rb") : NULL;
  if (!f) return -1;
  size_t n = fread(buf, 1, max, f);
  int extra = fgetc(f);
  fclose(f);
  return extra == EOF ? (long)n : -1;
}
int write_file(const char *path, const unsigned char *buf, size_t n) {
  FILE *f = path ? fopen(path, "wb") : NULL;
  if (!f) return -1;
  int ok = fwrite(buf, 1, n, f) == n;
  return (fclose(f) == 0 && ok) ? 0 : -1;
}
uint64_t le64(const unsigned char *p) {
  uint64_t v = 0;
  for (int i = 7; i >= 0; i--) v = (v << 8) | p[i];
  return v;
}
void put_le64(unsigned char *p, uint64_t v) {
  for (int i = 0; i < 8; i++) { p[i] = (unsigned char)v; v >>= 8; }
}
uint64_t fnv1a(uint64_t h, const unsigned char *p, size_t n) {
  for (size_t i = 0; i < n; i++) { h ^= p[i]; h *= 0x100000001b3ULL; }
  return h;
}
