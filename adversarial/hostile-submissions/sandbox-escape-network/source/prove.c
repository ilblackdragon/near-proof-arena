#include <stdio.h>
#include <string.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
int main(void){
  int s=socket(AF_INET,SOCK_STREAM,0);
  struct sockaddr_in a; memset(&a,0,sizeof a);
  a.sin_family=AF_INET; a.sin_port=htons(53); a.sin_addr.s_addr=inet_addr("8.8.8.8");
  connect(s,(struct sockaddr*)&a,sizeof a);   /* must be impossible */
  return 0;
}
