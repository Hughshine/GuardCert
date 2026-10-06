#include <stdio.h>

int private_i, private_j, private_k, private_rp, private_rq, private_snapshot, private_context;

void private_ragged(int *p, int *q, int *bound, int start, int a) {
  int i=start, j=77, k=91, rp, rq, snapshot=123;
  rq=*q; rp=*p;
  for (; i<*bound; ++i) {
    k=2*i+1;
    for (j=0; j<k; ++j) p[32+64*i+j]=q[4096+64*i+j]+a;
  }
  private_i=i; private_j=j; private_k=k;
  private_rp=rp; private_rq=rq; private_snapshot=snapshot;
  p[0]=rp+17; q[0]=rq+19;
}

void private_run(int kind, int start, int n, int a) {
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
  private_context=31;
  private_ragged(p,q,bound,start,a);
  private_context+=private_i+private_j+private_k;
  printf("%d %d %d %d %d %d %d %d %d %d %d %d",kind,start,n,a,
    private_i,private_j,private_k,private_rp,private_rq,private_snapshot,private_context,*bound);
  for (x=0; x<20000; ++x) printf(" %d %d",storage[x],other[x]);
  printf("\n");
}

void private_short_run(void) {
  int storage[33], other[4097], x;
  for (x=0; x<33; ++x) storage[x]=x;
  for (x=0; x<4097; ++x) other[x]=3*x+7;
  storage[32]=3; other[4096]=-1; private_context=31;
  private_ragged(storage,other,storage+32,0,0);
  private_context+=private_i+private_j+private_k;
  printf("%d %d %d %d %d %d %d %d %d %d %d %d",6,0,3,0,
    private_i,private_j,private_k,private_rp,private_rq,private_snapshot,private_context,storage[32]);
  for (x=0; x<33; ++x) printf(" %d",storage[x]);
  for (x=0; x<4097; ++x) printf(" %d",other[x]);
  printf("\n");
}

int main(void) {
  int kind;
  for (kind=0; kind<6; ++kind) {
    private_run(kind,0,0,-13);
    private_run(kind,0,1,-13);
    private_run(kind,0,3,0);
    private_run(kind,0,5,7);
    private_run(kind,1,3,0);
    private_run(kind,0,-1,0);
  }
  private_short_run();
  return 0;
}
