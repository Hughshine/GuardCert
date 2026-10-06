#include <stdio.h>

int loaded_i, loaded_j, loaded_k, loaded_rp, loaded_rq, loaded_snapshot, loaded_context;

void loaded_triangle(int *p, int *q, int start, int n, int a) {
  int i=start, j=77, k=91, rp, rq, snapshot;
  rq=*q; snapshot=*p; rp=*p;
  for (; i<*p; ++i) {
    k=i+1;
    for (j=0; j<k; ++j) p[32+64*i+j]=q[4096+64*i+j]+a;
  }
  loaded_i=i; loaded_j=j; loaded_k=k; loaded_rp=rp; loaded_rq=rq; loaded_snapshot=snapshot;
  p[0]=rp+17; q[0]=rq+19;
}

/* Same memory operations, a different actual affine domain. */
void loaded_ragged(int *destination, int *origin, int start, int n, int a) {
  int row=start, column=77, ceiling=91, destination_value, origin_value, bound_value;
  origin_value=*origin; bound_value=*destination; destination_value=*destination;
  for (; row<*destination; ++row) {
    ceiling=2*row+1;
    for (column=0; column<ceiling; ++column) destination[32+64*row+column]=origin[4096+64*row+column]+a;
  }
  loaded_i=row; loaded_j=column; loaded_k=ceiling; loaded_rp=destination_value; loaded_rq=origin_value; loaded_snapshot=bound_value;
  destination[0]=destination_value+17; origin[0]=origin_value+19;
}

/* No source snapshot of the loaded bound: the selector must refuse. */
void loaded_missing(int *p, int *q, int start, int n, int a) {
  int i=start, j=77, k=91, rp=0, rq;
  rq=*q;
  for (; i<*p; ++i) {
    k=i+1;
    for (j=0; j<k; ++j) p[32+64*i+j]=q[4096+64*i+j]+a;
  }
  loaded_i=i; loaded_j=j; loaded_k=k; loaded_rp=rp; loaded_rq=rq; loaded_snapshot=0;
  p[0]=rp+17; q[0]=rq+19;
}

/* Actual source writes its bound; static observation exclusion refuses. */
void loaded_bound_written(int *p, int *q, int start, int n, int a) {
  int i=start, j=77, k=91, rp, rq, snapshot;
  rq=*q; snapshot=*p; rp=*p;
  for (; i<*p; ++i) {
    k=i+1;
    for (j=0; j<k; ++j) p[0]=q[4096+64*i+j]+a;
  }
  loaded_i=i; loaded_j=j; loaded_k=k; loaded_rp=rp; loaded_rq=rq; loaded_snapshot=snapshot;
  p[0]=rp+17; q[0]=rq+19;
}


/* Conservative source receipts require distinct output temporaries. */
void loaded_repeated(int *p, int *q, int start, int n, int a) {
  int i=start, j=77, k=91, rp, rq, snapshot;
  rq=*q; snapshot=*p; snapshot=*p; rp=*p;
  for (; i<*p; ++i) {
    k=i+1;
    for (j=0; j<k; ++j) p[32+64*i+j]=q[4096+64*i+j]+a;
  }
  loaded_i=i; loaded_j=j; loaded_k=k; loaded_rp=rp; loaded_rq=rq; loaded_snapshot=snapshot;
  p[0]=rp+17; q[0]=rq+19;
}


void loaded_run(int which, int kind, int start, int n, int a) {
  int storage[20000], other[20000], *p=storage+4500, *q=other+4500, x;
  for (x=0; x<20000; ++x) {storage[x]=x; other[x]=3*x+7;}
  if (kind==0) q=p;
  if (kind==2) q=storage+499;
  storage[4500]=n;
  if (which==3) for (x=0; x<5000; ++x) q[4096+x]=-1-a;
  loaded_context=31;
  if (which==0) loaded_triangle(p,q,start,n,a);
  else if (which==1) loaded_ragged(p,q,start,n,a);
  else if (which==2) loaded_missing(p,q,start,n,a);
  else if (which==3) loaded_bound_written(p,q,start,n,a);
  else loaded_repeated(p,q,start,n,a);
  loaded_context+=loaded_i+loaded_j+loaded_k;
  printf("%d %d %d %d %d %d %d %d %d %d %d %d %d", which,kind,start,n,a,
    loaded_i,loaded_j,loaded_k,loaded_rp,loaded_rq,loaded_snapshot,loaded_context,storage[4597]);
  for (x=0; x<20000; ++x) printf(" %d %d",storage[x],other[x]);
  printf("\n");
}

int main(void) {
  int which, kind;
  for (which=0; which<5; ++which) for (kind=0; kind<3; ++kind) {
    loaded_run(which,kind,0,0,-13);
    loaded_run(which,kind,0,1,-13);
    loaded_run(which,kind,0,3,0);
    loaded_run(which,kind,0,32,7);
    loaded_run(which,kind,0,63,-13);
    loaded_run(which,kind,0,64,7);
    loaded_run(which,kind,0,65,7);
    loaded_run(which,kind,1,3,0);
    loaded_run(which,kind,3,3,0);
    loaded_run(which,kind,0,-1,0);
  }
  return 0;
}
