#include <stdio.h>
int out_i,out_j;
void unused_inner(int *p,int *q,int start,int n,int m,int alpha,int beta) {
  int i=start,j=77;
  for (;i<n;i++) for(j=0;j<m;j++) p[i]=q[i]*alpha+j*beta;
  out_i=i;out_j=j;
}
void unused_all(int *p,int *q,int start,int n,int m,int alpha,int beta) {
  int i=start,j=77;
  for (;i<n;i++) for(j=0;j<m;j++) p[0]=q[0]*alpha+beta;
  out_i=i;out_j=j;
}
int meta_a[64],meta_b[64],out_k;
void context_three(int start,int n,int m,int p) {
  int i=start,j=77,k=55;
  for(;i<n;i++) {
    k=i+m-p;
    for(j=0;j<k;j++) meta_a[8*i+j]=meta_a[8*i+j]+meta_b[8*i+j]+i*j+7;
  }
  out_i=i;out_j=j;out_k=k;
}
int main(void) {
  int p[64],q[64],i,n,m;
  for(n=0;n<=5;n++) for(m=0;m<=5;m++) {
    for(i=0;i<64;i++) {p[i]=3*i+1;q[i]=5*i+7;}
    unused_inner(p,q,0,n,m,-7,11);
    printf("inner %d %d %d %d",n,m,out_i,out_j);
    for(i=0;i<64;i++) printf(" %d %d",p[i],q[i]);
    printf("\n");
    for(i=0;i<64;i++) {p[i]=3*i+1;q[i]=5*i+7;}
    unused_all(p,q,0,n,m,-7,11);
    printf("all %d %d %d %d",n,m,out_i,out_j);
    for(i=0;i<64;i++) printf(" %d %d",p[i],q[i]);
    printf("\n");
  }
  for(n=0;n<=4;n++) for(m=0;m<=3;m++) {
    for(i=0;i<64;i++) {meta_a[i]=3*i+1;meta_b[i]=5*i+7;}
    context_three(0,n,m,1);
    printf("context %d %d %d %d %d",n,m,out_i,out_j,out_k);
    for(i=0;i<64;i++) printf(" %d %d",meta_a[i],meta_b[i]);
    printf("\n");
  }
  return 0;
}
