/* Research reconstruction of LOCAL, TRUSTED exports only. Bounded parsing is
 * not a proof that arbitrary metadata is safe for the upstream C verifier.
 * Caller must not expose this as an untrusted network proof decoder. */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "pack.h"
typedef struct{const uint8_t*b;size_t n,p;int bad;} reader;
static const uint8_t*take(reader*r,size_t n){if(r->bad||n>r->n-r->p){r->bad=1;return NULL;}const uint8_t*p=r->b+r->p;r->p+=n;return p;}
static uint64_t get(reader*r,size_t n){const uint8_t*p=take(r,n);uint64_t v=0;if(p)for(size_t i=0;i<n;i++)v|=(uint64_t)p[i]<<(8*i);return v;}
static size_t bounded(reader*r,size_t limit){uint64_t v=get(r,8);if(v>limit)r->bad=1;return r->bad?0:(size_t)v;}
static void* az(size_t n){if(n>16*1024*1024)return NULL;void*p=aligned_alloc(64,(n+63)&~(size_t)63);if(p)memset(p,0,(n+63)&~(size_t)63);return p;}
static int polys(reader*r,polz*p,size_t n){if(get(r,8)!=n)return 0;for(size_t i=0;i<n;i++){const uint8_t*b=take(r,N*QBYTES);if(!b)return 0;polz_bitunpack(p+i,b);}return !r->bad;}
int bn_import_local_export(const uint8_t*bytes,size_t len,void*vp,void*vc){
 composite*p=vp;commitment*c=vc;reader r={bytes,len,0,0};size_t *ranks=NULL,*offsets=NULL;uint64_t*norms=NULL;
 if(len>16*1024*1024||len<32)return 0;
 if(memcmp(take(&r,8),"NPLAB001",8)||get(&r,8)!=N||get(&r,8)!=LOGQ)return 0;
 size_t levels=bounded(&r,16);if(!levels)return 0;
 c->r=bounded(&r,4096);c->fu=bounded(&r,64);c->bu=bounded(&r,48);c->kappa=bounded(&r,1024);c->kappa1=bounded(&r,1024);
 if(r.bad||!c->r||!c->kappa||!c->kappa1)goto fail;
 c->n=calloc(c->r,sizeof(size_t));if(!c->n)goto fail;
 for(size_t i=0;i<c->r;i++)c->n[i]=bounded(&r,1<<20);
 c->u=az(c->kappa1*sizeof(polz)+c->r*sizeof(polx));if(!c->u)goto fail;c->alpha=(polx*)(c->u+c->kappa1);
 if(!polys(&r,c->u,c->kappa1))goto fail;
 for(size_t j=0;j<levels;j++){
  proof*a=calloc(1,sizeof(proof));if(!a)goto fail;p->pi[p->l++]=a;comparams*b=a->cpp;
  a->r=bounded(&r,4096);a->tail=bounded(&r,1);if(r.bad||!a->r)goto fail;
  a->n=calloc(2*a->r,sizeof(size_t));if(!a->n)goto fail;a->nu=a->n+a->r;
  for(size_t i=0;i<a->r;i++){a->n[i]=bounded(&r,1<<20);a->nu[i]=bounded(&r,4096);}
  size_t*fields[]={&b->f,&b->fu,&b->fg,&b->b,&b->bu,&b->bg,&b->kappa,&b->kappa1,&b->u1len,&b->u2len};
  for(size_t i=0;i<10;i++)*fields[i]=bounded(&r,i<6?48:4096);
  if(r.bad||!b->f||!b->kappa||(!a->tail&&!b->kappa1))goto fail;
  a->jlnonce=get(&r,8);for(size_t i=0;i<256;i++)a->p[i]=(int32_t)(uint32_t)get(&r,4);a->normsq=get(&r,8);
  a->u1=az((b->u1len+b->u2len+LIFTS)*sizeof(polz));if(!a->u1)goto fail;a->u2=a->u1+b->u1len;a->bb=a->u2+b->u2len;
  if(!polys(&r,a->u1,b->u1len)||!polys(&r,a->u2,b->u2len)||!polys(&r,a->bb,LIFTS))goto fail;
 }
 size_t wr=bounded(&r,4096);if(r.bad||!wr)goto fail;
 ranks=calloc(wr,sizeof(size_t));offsets=calloc(wr,sizeof(size_t));norms=calloc(wr,sizeof(uint64_t));if(!ranks||!offsets||!norms)goto fail;
 size_t total=0;for(size_t i=0;i<wr;i++){ranks[i]=bounded(&r,1<<16);norms[i]=get(&r,8);offsets[i]=r.p;total+=ranks[i];if(total>(1<<16)||!take(&r,ranks[i]*N*2))goto fail;}
 if(r.bad||r.p!=len)goto fail;
 init_witness_raw(&p->owt,wr,ranks);
 for(size_t i=0;i<wr;i++){p->owt.normsq[i]=norms[i];const uint8_t*q=bytes+offsets[i];for(size_t j=0;j<ranks[i];j++)for(size_t k=0;k<N;k++){p->owt.s[i][j].vec->c[k]=(int16_t)((uint16_t)q[0]|((uint16_t)q[1]<<8));q+=2;}}
 free(ranks);free(offsets);free(norms);return 1;
 fail:free(ranks);free(offsets);free(norms);free_composite(p);free_commitment(c);return 0;
}
