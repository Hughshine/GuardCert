#include <stdio.h>

int dependent_i, dependent_j, dependent_k, dependent_rp, dependent_rq, dependent_snapshot, dependent_context;

void dependent_ragged(int *p, int *q, int **root, int start, int a) {
  int i=start, j=77, k=91, rp, rq, snapshot=123;
  rq=*q; rp=*p;
  for (; i<**root; ++i) {
    k=2*i+1;
    for (j=0; j<k; ++j) p[32+64*i+j]=q[4096+64*i+j]+a;
  }
  dependent_i=i; dependent_j=j; dependent_k=k;
  dependent_rp=rp; dependent_rq=rq; dependent_snapshot=snapshot;
  p[0]=rp+17; q[0]=rq+19;
}

void dependent_run(int kind, int start, int n, int a) {
  int storage[20000], other[20000], value=n;
  int *p=storage+4500, *q=storage+4500, *bound=&value, x;
  for (x=0; x<20000; ++x) {storage[x]=x; other[x]=3*x+7;}
  if (kind==1) bound=p+31;
  if (kind==2) bound=p+32;
  if (kind==3) bound=p+97;
  if (kind==4) q=storage+499;
  if (kind==5) q=other+4500;
  *bound=n;
  if (kind==2 || kind==3)
    for (x=0; x<5000; ++x) q[4096+x]=-1-a;
  dependent_context=31;
  dependent_ragged(p,q,&bound,start,a);
  dependent_context+=dependent_i+dependent_j+dependent_k;
  printf("%d %d %d %d %d %d %d %d %d %d %d %d",kind,start,n,a,
    dependent_i,dependent_j,dependent_k,dependent_rp,dependent_rq,dependent_snapshot,dependent_context,*bound);
  for (x=0; x<20000; ++x) printf(" %d %d",storage[x],other[x]);
  printf("\n");
}

void dependent_short_run(void) {
  int storage[33], other[4097], x;
  int *bound=storage+32;
  for (x=0; x<33; ++x) storage[x]=x;
  for (x=0; x<4097; ++x) other[x]=3*x+7;
  storage[32]=3; other[4096]=-1; dependent_context=31;
  dependent_ragged(storage,other,&bound,0,0);
  dependent_context+=dependent_i+dependent_j+dependent_k;
  printf("%d %d %d %d %d %d %d %d %d %d %d %d",6,0,3,0,
    dependent_i,dependent_j,dependent_k,dependent_rp,dependent_rq,dependent_snapshot,dependent_context,storage[32]);
  for (x=0; x<33; ++x) printf(" %d",storage[x]);
  for (x=0; x<4097; ++x) printf(" %d",other[x]);
  printf("\n");
}

int main(void) {
  int kind;
  for (kind=0; kind<6; ++kind) {
    dependent_run(kind,0,0,-13);
    dependent_run(kind,0,1,-13);
    dependent_run(kind,0,3,0);
    dependent_run(kind,0,5,7);
    dependent_run(kind,1,3,0);
    dependent_run(kind,0,-1,0);
  }
  dependent_short_run();
  return 0;
}
