#include <stdio.h>
int resource_out_i;
void alias_reads_31(int *p,int *q,int n) {
  int i=0;
  for(;i<n;i++) p[2*i]=q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1];
  resource_out_i=i;
}
void alias_reads_32(int *p,int *q,int n) {
  int i=0;
  for(;i<n;i++) p[2*i]=q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1];
  resource_out_i=i;
}
void alias_reads_64(int *p,int *q,int n) {
  int i=0;
  for(;i<n;i++) p[2*i]=q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1]+q[3*i+1];
  resource_out_i=i;
}
void resource_run(int reads,int kind,int n) {
  int a[1024],b[1024],*q=b,i;
  for(i=0;i<1024;i++){a[i]=3*i+1;b[i]=5*i+7;}
  if(kind==1) q=a;
  if(reads==31) alias_reads_31(a,q,n);
  else if(reads==32) alias_reads_32(a,q,n);
  else alias_reads_64(a,q,n);
  printf("%d %d %d %d",reads,kind,n,resource_out_i);
  for(i=0;i<1024;i++) printf(" %d %d",a[i],b[i]);
  printf("\n");
}
int main(void) {
  int reads,kind,k;
  int sizes[3]={31,32,64},counts[3]={0,1,129};
  for(reads=0;reads<3;reads++) for(kind=0;kind<2;kind++) for(k=0;k<3;k++)
    resource_run(sizes[reads],kind,counts[k]);
  return 0;
}
