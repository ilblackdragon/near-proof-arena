/* Research export only. No decoder or untrusted verifier entry point.
 * Scalars are little-endian; polz uses upstream bit packing; terminal witness
 * coefficients use fixed signed 16-bit words. No pointers or struct padding.
 * com->alpha is excluded: reduce_simple_commit reconstructs it from the statement.
 */
#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <limits.h>
#include "pack.h"
typedef struct { uint8_t *out; size_t cap,pos; int failed; } writer;
static void emit(writer *w,const void *p,size_t n){
 if(n>SIZE_MAX-w->pos){w->failed=1;return;}
 if(w->out){if(w->pos>w->cap || n>w->cap-w->pos){w->failed=1;return;}memcpy(w->out+w->pos,p,n);}w->pos+=n;
}
static void integer(writer*w,uint64_t v,size_t n){uint8_t b[8];for(size_t i=0;i<n;i++)b[i]=(uint8_t)(v>>(8*i));emit(w,b,n);}
static void zs(writer*w,const polz*p,size_t n){
 integer(w,n,8);for(size_t i=0;i<n;i++){uint8_t b[N*QBYTES];if(w->out)polz_bitpack(b,p+i);emit(w,b,sizeof(b));}
}
size_t bn_export_proof(const void *vp,const void *vc,uint8_t*out,size_t cap){
 const composite *p=vp;const commitment*c=vc;writer w={out,cap,0,0};
 emit(&w,"NPLAB001",8);integer(&w,N,8);integer(&w,LOGQ,8);integer(&w,p->l,8);
 integer(&w,c->r,8);integer(&w,c->fu,8);integer(&w,c->bu,8);integer(&w,c->kappa,8);integer(&w,c->kappa1,8);
 for(size_t i=0;i<c->r;i++)integer(&w,c->n[i],8);zs(&w,c->u,c->kappa1);
 for(size_t j=0;j<p->l;j++){
  const proof*a=p->pi[j];const comparams*b=a->cpp;
  integer(&w,a->r,8);integer(&w,a->tail,8);
  for(size_t i=0;i<a->r;i++){integer(&w,a->n[i],8);integer(&w,a->nu[i],8);}
  size_t fields[]={b->f,b->fu,b->fg,b->b,b->bu,b->bg,b->kappa,b->kappa1,b->u1len,b->u2len};
  for(size_t i=0;i<10;i++)integer(&w,fields[i],8);
  integer(&w,a->jlnonce,8);for(size_t i=0;i<256;i++)integer(&w,(uint32_t)a->p[i],4);integer(&w,a->normsq,8);
  zs(&w,a->u1,b->u1len);zs(&w,a->u2,b->u2len);zs(&w,a->bb,LIFTS);
 }
 const witness*t=&p->owt;integer(&w,t->r,8);
 for(size_t i=0;i<t->r;i++){
  integer(&w,t->n[i],8);integer(&w,t->normsq[i],8);
  for(size_t j=0;j<t->n[i];j++)for(size_t k=0;k<N;k++)integer(&w,(uint16_t)t->s[i][j].vec->c[k],2);
 }
 return w.failed?0:w.pos;
}
