#include <stdio.h>
int scan_out_i;
void scan_copy(int *p,int *q,int start,int n,int alpha,int beta) {
  int i=start;
  for(;i<n;i++) p[i]=q[i]*alpha+beta;
  scan_out_i=i;
}
void scan_chain(int *p,int *q,int start,int n,int alpha,int beta) {
  int i=start;
  for(;i<n;i++) {
    p[i]=q[i]*alpha+beta;
    q[i]=p[i]+i;
  }
  scan_out_i=i;
}
void scan_undefined(int n) {
  int *p,*q,alpha,beta,i=0;
  for(;i<n;i++) p[i]=q[i]*alpha+beta;
  scan_out_i=i;
}
void scan_run(int which,int kind,int start,int n,int alpha,int beta) {
  int a[2300],b[2300],*p=a,*q=b,i;
  for(i=0;i<2300;i++) {a[i]=3*i+1;b[i]=5*i+7;}
  if(kind==1) q=a+1;
  if(kind==2) q=a+1024;
  if(kind==3) q=a;
  if(kind==4) q=a+(n>0?n:0);
  if(kind==5) {p=0;q=0;}
  if(which==0) scan_copy(p,q,start,n,alpha,beta);
  else scan_chain(p,q,start,n,alpha,beta);
  printf("%d %d %d %d %d %d %d",which,kind,start,n,alpha,beta,scan_out_i);
  for(i=0;i<2300;i++) printf(" %d %d",a[i],b[i]);
  printf("\n");
}
int main(void) {
  int which,kind,k;
  int counts[9]={0,1,2,9,33,129,511,1024,1025};
  for(which=0;which<2;which++) for(kind=0;kind<5;kind++) for(k=0;k<9;k++)
    scan_run(which,kind,0,counts[k],-7,11);
  for(which=0;which<2;which++) {
    scan_run(which,0,1,33,(-2147483647-1),2147483647);
    scan_run(which,0,0,129,(-2147483647-1),2147483647);
    scan_run(which,5,0,0,3,-7);
    scan_run(which,5,0,(-2147483647-1),3,-7);
  }
  scan_undefined(0);printf("undefined 0 %d\n",scan_out_i);
  scan_undefined((-2147483647-1));printf("undefined -2147483648 %d\n",scan_out_i);
  return 0;
}
