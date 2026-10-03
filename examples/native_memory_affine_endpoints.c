#include <stdio.h>
int endpoint_out_i;
void endpoint_stride(int *p,int *q,int start,int n,int alpha,int beta) {
  int i=start;
  for(;i<n;i++) p[2*i]=q[2*i+1]*alpha+beta;
  endpoint_out_i=i;
}
void endpoint_negative(int *p,int *q,int start,int n,int alpha,int beta) {
  int i=start;
  for(;i<n;i++) p[1023-2*i]=q[1022-2*i]*alpha+beta;
  endpoint_out_i=i;
}
void endpoint_constant(int *p,int *q,int start,int n,int alpha,int beta) {
  int i=start;
  for(;i<n;i++) p[2]=q[3]+i*alpha+beta;
  endpoint_out_i=i;
}
void endpoint_unit(int *p,int *q,int start,int n,int alpha,int beta) {
  int i=start;
  for(;i<n;i++) p[i]=q[i]*alpha+beta;
  endpoint_out_i=i;
}
void endpoint_run(int which,int kind,int start,int n,int alpha,int beta) {
  int a[4600],b[4600],*q=b,i;
  for(i=0;i<4600;i++){a[i]=3*i+1;b[i]=5*i+7;}
  if(kind==1) q=a+1;
  if(kind==2) q=a+1500;
  if(kind==3) q=a;
  if(kind==4) q=a+2;
  if(kind==5) q=0;
  if(which==0) endpoint_stride(a,q,start,n,alpha,beta);
  else if(which==1) endpoint_negative(a,q,start,n,alpha,beta);
  else if(which==2) endpoint_constant(a,q,start,n,alpha,beta);
  else endpoint_unit(a,q,start,n,alpha,beta);
  printf("%d %d %d %d %d %d %d",which,kind,start,n,alpha,beta,endpoint_out_i);
  for(i=0;i<4600;i++) printf(" %d %d",a[i],b[i]);
  printf("\n");
}
int main(void) {
  int which,kind,k;
  int counts[12]={0,1,2,9,33,129,257,511,512,513,1024,1025};
  for(which=0;which<4;which++) for(kind=0;kind<5;kind++)
    for(k=0;k<(which==1?9:12);k++) endpoint_run(which,kind,0,counts[k],-7,11);
  for(which=0;which<4;which++) {
    endpoint_run(which,0,1,33,(-2147483647-1),2147483647);
    endpoint_run(which,0,0,129,(-2147483647-1),2147483647);
    endpoint_run(which,5,0,0,3,-7);
    endpoint_run(which,5,0,(-2147483647-1),3,-7);
  }
  return 0;
}
