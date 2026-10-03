#include <stdio.h>
int axis_out_i,axis_out_j,axis_out_k,axis_out_l;
void axis_copy2(int *p,int *q,int start,int n,int m,int s,int t,int alpha,int beta) {
  int i=start,j=77,k=91,l=103;
  for(;i<n;i++) for(j=0;j<m;j++) p[16*i+j]=q[16*i+j+1]*alpha+i*beta+j;
  axis_out_i=i;axis_out_j=j;axis_out_k=k;axis_out_l=l;
}
void axis_negative2(int *p,int *q,int start,int n,int m,int s,int t,int alpha,int beta) {
  int i=start,j=77,k=91,l=103;
  for(;i<n;i++) for(j=0;j<m;j++) p[1023-16*i-j]=q[1022-16*i-j]*alpha+i*beta+j;
  axis_out_i=i;axis_out_j=j;axis_out_k=k;axis_out_l=l;
}
void axis_chain2(int *p,int *q,int start,int n,int m,int s,int t,int alpha,int beta) {
  int i=start,j=77,k=91,l=103;
  for(;i<n;i++) for(j=0;j<m;j++) {
    p[16*i+j]=q[16*i+j]*alpha+i*beta+j;
    q[16*i+j+1]=p[16*i+j]+q[16*i+j+1]*beta+i-j;
  }
  axis_out_i=i;axis_out_j=j;axis_out_k=k;axis_out_l=l;
}
void axis_copy3(int *p,int *q,int start,int n,int m,int s,int t,int alpha,int beta) {
  int i=start,j=77,k=91,l=103;
  for(;i<n;i++) for(j=0;j<m;j++) for(k=0;k<s;k++)
    p[64*i+8*j+k]=q[64*i+8*j+k]*alpha+i*beta+j+k;
  axis_out_i=i;axis_out_j=j;axis_out_k=k;axis_out_l=l;
}
void axis_copy4(int *p,int *q,int start,int n,int m,int s,int t,int alpha,int beta) {
  int i=start,j=77,k=91,l=103;
  for(;i<n;i++) for(j=0;j<m;j++) for(k=0;k<s;k++) for(l=0;l<t;l++)
    p[128*i+32*j+4*k+l]=q[128*i+32*j+4*k+l]*alpha+i*beta+j+k+l;
  axis_out_i=i;axis_out_j=j;axis_out_k=k;axis_out_l=l;
}
void axis_run(int which,int kind,int start,int n,int m,int s,int t,int alpha,int beta) {
  int a[6000],b[6000],*p=a,*q=b,i;
  for(i=0;i<6000;i++){a[i]=3*i+1;b[i]=5*i+7;}
  if(kind==1)q=a+1;
  if(kind==2)q=a+1500;
  if(kind==3)q=a;
  if(kind==4)q=a+16;
  if(kind==5){p=0;q=0;}
  if(which==0)axis_copy2(p,q,start,n,m,s,t,alpha,beta);
  else if(which==1)axis_negative2(p,q,start,n,m,s,t,alpha,beta);
  else if(which==2)axis_chain2(p,q,start,n,m,s,t,alpha,beta);
  else if(which==3)axis_copy3(p,q,start,n,m,s,t,alpha,beta);
  else axis_copy4(p,q,start,n,m,s,t,alpha,beta);
  printf("%d %d %d %d %d %d %d %d %d %d %d %d %d",which,kind,start,n,m,s,t,alpha,beta,
    axis_out_i,axis_out_j,axis_out_k,axis_out_l);
  for(i=0;i<6000;i++)printf(" %d %d",a[i],b[i]);
  printf("\n");
}
int main(void) {
  int which,kind,c;
  int two[12][2]={{0,0},{0,9},{9,0},{1,1},{2,2},{4,4},{5,5},{9,9},{16,16},{17,17},{33,1},{61,1}};
  int three[10][3]={{0,2,2},{1,0,2},{2,2,0},{1,1,1},{2,2,2},{4,4,4},{5,2,2},{9,1,2},{15,1,1},{16,1,1}};
  int four[11][4]={{0,2,2,2},{1,0,2,2},{2,2,0,2},{2,2,2,0},{1,1,1,1},{2,2,2,2},
    {3,1,1,2},{4,2,2,2},{5,1,1,1},{7,1,1,1},{8,1,1,1}};
  for(which=0;which<3;which++)for(kind=0;kind<5;kind++)for(c=0;c<12;c++)
    axis_run(which,kind,0,two[c][0],two[c][1],1,1,-7,11);
  for(kind=0;kind<5;kind++)for(c=0;c<10;c++)
    axis_run(3,kind,0,three[c][0],three[c][1],three[c][2],1,-7,11);
  for(kind=0;kind<5;kind++)for(c=0;c<11;c++)
    axis_run(4,kind,0,four[c][0],four[c][1],four[c][2],four[c][3],-7,11);
  for(which=0;which<5;which++){
    axis_run(which,0,1,3,2,2,2,(-2147483647-1),2147483647);
    axis_run(which,0,0,3,2,2,2,(-2147483647-1),2147483647);
    axis_run(which,5,0,0,2,2,2,3,-7);
    axis_run(which,5,0,(-2147483647-1),2,2,2,3,-7);
  }
  return 0;
}
