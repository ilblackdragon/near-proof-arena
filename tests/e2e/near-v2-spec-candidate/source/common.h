#include <stddef.h>
#include <stdint.h>
const char *arg(int argc, char **argv, const char *key);
/* Read a whole file of at most `max` bytes into a fresh buffer; NULL on error. */
unsigned char *slurp(const char *path, size_t max, size_t *len);
int write_file(const char *path, const unsigned char *buf, size_t n);
/* Run `<dir of self>/nearspec-check --scope v2 case`, capturing stdout
   (at most `max` bytes) into `out`; returns the exit status or -1. */
int nearspec(const char *self, char *out, size_t max);
#define MAX_REQ (128u << 10)
#define MAX_WIT (4u << 20)
#define MAX_CLAIM 416u
