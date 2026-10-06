#include <stdio.h>

int affine_i, affine_j, affine_k, affine_rp, affine_rq, affine_context;

void affine_triangle(int *p, int *q, int start, int n, int a) {
  int i=start, j=77, k=91, rp, rq;
  rp=*p; rq=*q;
  for (; i<n; ++i) {
    k=i+1;
    for (j=0; j<k; ++j) p[32+64*i+j]=q[4096+64*i+j]+a;
  }
  affine_i=i; affine_j=j; affine_k=k; affine_rp=rp; affine_rq=rq;
  p[0]=rp+17; q[0]=rq+19;
}

/* Same memory operations, a different actual affine domain. */
void affine_ragged(int *p, int *q, int start, int n, int a) {
  int i=start, j=77, k=91, rp, rq;
  rp=*p; rq=*q;
  for (; i<n; ++i) {
    k=2*i+1;
    for (j=0; j<k; ++j) p[32+64*i+j]=q[4096+64*i+j]+a;
  }
  affine_i=i; affine_j=j; affine_k=k; affine_rp=rp; affine_rq=rq;
  p[0]=rp+17; q[0]=rq+19;
}

/* The alias condition cannot use a missing raw-q observation. */
void affine_missing(int *p, int *q, int start, int n, int a) {
  int i=start, j=77, k=91, rp, rq=0;
  rp=*p;
  for (; i<n; ++i) {
    k=i+1;
    for (j=0; j<k; ++j) p[32+64*i+j]=q[4096+64*i+j]+a;
  }
  affine_i=i; affine_j=j; affine_k=k; affine_rp=rp; affine_rq=rq;
  p[0]=rp+17; q[0]=rq+19;
}

void affine_run(int which, int kind, int start, int n, int a) {
  int storage[20000], other[20000], *p=storage+4500, *q=other+4500, x;
  for (x=0; x<20000; ++x) {storage[x]=x; other[x]=3*x+7;}
  if (kind==0) q=p;
  if (kind==2) q=storage+499;
  affine_context=31;
  if (which==0) affine_triangle(p,q,start,n,a);
  else if (which==1) affine_ragged(p,q,start,n,a);
  else affine_missing(p,q,start,n,a);
  affine_context+=affine_i+affine_j+affine_k;
  printf("%d %d %d %d %d %d %d %d %d %d %d %d", which,kind,start,n,a,
    affine_i,affine_j,affine_k,affine_rp,affine_rq,affine_context,storage[4597]);
  for (x=0; x<20000; ++x) printf(" %d %d",storage[x],other[x]);
  printf("\n");
}

int main(void) {
  int which, kind;
  for (which=0; which<3; ++which) for (kind=0; kind<3; ++kind) {
    affine_run(which,kind,0,0,-13);
    affine_run(which,kind,0,1,-13);
    affine_run(which,kind,0,3,0);
    affine_run(which,kind,0,32,7);
    affine_run(which,kind,0,63,-13);
    affine_run(which,kind,0,64,7);
    affine_run(which,kind,1,3,0);
    affine_run(which,kind,3,3,0);
    affine_run(which,kind,0,-1,0);
  }
  return 0;
}
