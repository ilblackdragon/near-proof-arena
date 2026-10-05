#define _POSIX_C_SOURCE 200809L
#include "common.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>
const char *arg(int argc, char **argv, const char *key) {
  for (int i = 1; i + 1 < argc; i++) if (!strcmp(argv[i], key)) return argv[i + 1];
  return NULL;
}
unsigned char *slurp(const char *path, size_t max, size_t *len) {
  FILE *f = path ? fopen(path, "rb") : NULL;
  if (!f) return NULL;
  unsigned char *b = malloc(max + 1);
  size_t n = b ? fread(b, 1, max + 1, f) : 0;
  fclose(f);
  if (!b || n > max) { free(b); return NULL; }
  *len = n;
  return b;
}
int write_file(const char *path, const unsigned char *buf, size_t n) {
  FILE *f = path ? fopen(path, "wb") : NULL;
  if (!f) return -1;
  int ok = fwrite(buf, 1, n, f) == n;
  return (fclose(f) == 0 && ok) ? 0 : -1;
}
int nearspec(const char *self, char *out, size_t max) {
  char exe[4096];
  const char *slash = strrchr(self, '/');
  size_t d = slash ? (size_t)(slash - self) : 1;
  if (d + 32 > sizeof exe) return -1;
  memcpy(exe, slash ? self : ".", d);
  strcpy(exe + d, "/nearspec-check");
  int p[2];
  if (pipe(p)) return -1;
  pid_t pid = fork();
  if (pid < 0) return -1;
  if (pid == 0) {
    dup2(p[1], 1);
    close(p[0]);
    close(p[1]);
    execl(exe, exe, "--scope", "v2", "case", (char *)NULL);
    _exit(127);
  }
  close(p[1]);
  size_t n = 0;
  ssize_t r;
  while ((r = read(p[0], out + n, max - 1 - n)) > 0) n += (size_t)r;
  out[n] = 0;
  close(p[0]);
  int st;
  if (waitpid(pid, &st, 0) < 0 || !WIFEXITED(st)) return -1;
  return WEXITSTATUS(st);
}
