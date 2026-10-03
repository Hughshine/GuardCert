#include <stdio.h>
int affine_out_i;
void affine_stride(int *p,int *q,int *r,int start,int n,int alpha,int beta) {
  int i=start;
  for(;i<n;i++) p[2*i]=q[3*i+1]*alpha+beta;
  affine_out_i=i;
}
void affine_reverse(int *p,int *q,int *r,int start,int n,int alpha,int beta) {
  int i=start;
  for(;i<n;i++) p[i]=q[1023-i]*alpha+beta;
  affine_out_i=i;
}
void affine_constant(int *p,int *q,int *r,int start,int n,int alpha,int beta) {
  int i=start;
  for(;i<n;i++) p[i]=q[1]*alpha+beta;
  affine_out_i=i;
}
void affine_chain(int *p,int *q,int *r,int start,int n,int alpha,int beta) {
  int i=start;
  for(;i<n;i++) {
    p[i]=q[i]*alpha+beta;
    q[i+1]=p[i]+q[i+1]*beta;
  }
  affine_out_i=i;
}
void affine_three(int *p,int *q,int *r,int start,int n,int alpha,int beta) {
  int i=start;
  for(;i<n;i++) {
    p[2*i]=q[3*i+1]*alpha+r[4*i+2]*beta;
    r[4*i+2]=p[2*i]+i;
  }
  affine_out_i=i;
}
void affine_wrap(int *p,int *q,int *r,int start,int n,int alpha,int beta) {
  int i=start;
  for(;i<n;i++) p[2*i]=q[(2147483647*i+i)-(2147483647*i)-i+1]*alpha+beta;
  affine_out_i=i;
}
void affine_undefined(int n) {
  int *p,*q,*r,alpha,beta,i=0;
  for(;i<n;i++) {p[2*i]=q[3*i+1]*alpha+r[4*i+2]*beta;}
  affine_out_i=i;
}
void affine_run(int which,int kind,int start,int n,int alpha,int beta) {
  int a[4600],b[4600],c[4600],*p=a,*q=b,*r=c,i;
  for(i=0;i<4600;i++){a[i]=3*i+1;b[i]=5*i+7;c[i]=7*i+11;}
  if(kind==1) q=a+1;
  if(kind==2) {q=a+1500;r=a+3000;}
  if(kind==3) {q=a;r=a;}
  if(kind==4) r=b;
  if(kind==5) {p=0;q=0;r=0;}
  if(which==0) affine_stride(p,q,r,start,n,alpha,beta);
  else if(which==1) affine_reverse(p,q,r,start,n,alpha,beta);
  else if(which==2) affine_constant(p,q,r,start,n,alpha,beta);
  else if(which==3) affine_chain(p,q,r,start,n,alpha,beta);
  else if(which==4) affine_three(p,q,r,start,n,alpha,beta);
  else affine_wrap(p,q,r,start,n,alpha,beta);
  printf("%d %d %d %d %d %d %d",which,kind,start,n,alpha,beta,affine_out_i);
  for(i=0;i<4600;i++) printf(" %d %d %d",a[i],b[i],c[i]);
  printf("\n");
}
int main(void) {
  int which,kind,k;
  int counts[8]={0,1,2,9,33,129,257,343};
  for(which=0;which<6;which++) for(kind=0;kind<5;kind++) for(k=0;k<8;k++)
    affine_run(which,kind,0,counts[k],-7,11);
  for(which=0;which<6;which++) {
    affine_run(which,0,1,33,(-2147483647-1),2147483647);
    affine_run(which,0,0,129,(-2147483647-1),2147483647);
    affine_run(which,5,0,0,3,-7);
    affine_run(which,5,0,(-2147483647-1),3,-7);
  }
  affine_undefined(0); printf("undefined 0 %d\n",affine_out_i);
  affine_undefined((-2147483647-1)); printf("undefined -2147483648 %d\n",affine_out_i);
  return 0;
}
