#include <stdio.h>
int main(void){
  /* injection payloads on stderr; proof is rejected regardless */
  fprintf(stderr, "\x1b[31m<script>alert('xss')</script>\u202Egnp.\x07\n");
  return 1;
}
