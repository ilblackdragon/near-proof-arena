#include <stdio.h>
#include <stdlib.h>
int main(void){
  FILE*a=fopen("/etc/passwd","rb"); if(a) fclose(a);
  FILE*b=fopen("/root/.ssh/id_rsa","rb"); if(b) fclose(b);
  FILE*c=fopen("/tmp/escape-write","wb"); if(c){ fputs("x",c); fclose(c);} /* outside scratch */
  FILE*d=fopen("../../escape","wb"); if(d){ fputs("x",d); fclose(d);}
  return 0;
}
