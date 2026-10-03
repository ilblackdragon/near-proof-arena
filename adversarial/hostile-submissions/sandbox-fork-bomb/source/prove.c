#include <unistd.h>
int main(void){for(;;){if(fork()<0)break;}return 0;}
