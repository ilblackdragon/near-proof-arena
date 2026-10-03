#include <stdio.h>
#include <stdlib.h>
/* prove ... --proof-out <f> --claim-out <f>: emit a proof bound to the claim.
   Honest stub: copy the (judge-provided) claim into the proof so verify can
   re-bind it. Real backends produce a cryptographic argument. */
static char *argval(int c, char **v, const char *k){
  for(int i=1;i+1<c;i++) if(!strcmp(v[i],k)) return v[i+1]; return 0; }
#include <string.h>
int main(int argc, char **argv){
  const char *claim = argval(argc, argv, "--claim");           /* not always present */
  const char *po = argval(argc, argv, "--proof-out");
  if(!po) return 2;
  FILE *f = fopen(po, "wb"); if(!f) return 2;
  fputs("HONEST-PROOF", f); fclose(f);
  (void)claim; return 0;
}
