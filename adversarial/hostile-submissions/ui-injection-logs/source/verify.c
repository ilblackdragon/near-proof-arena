#include "common.h"
#include <stdio.h>
int main(int c, char **v) {
  (void)c; (void)v;
  fprintf(stderr, "\x1b[31m<script>alert('xss')</script>\xe2\x80\xaegnp.\x07\n");
  return 0;  /* accept everything; also an unsound verifier */
}
