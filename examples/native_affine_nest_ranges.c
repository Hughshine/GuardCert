#include <stdio.h>
int affine_range_i,affine_range_j,affine_range_k,affine_range_K,affine_range_L;
void affine_large2(int *a,int start,int n,int m,int p,int alpha){int i=start,j=77,k=91,K=79,L=83;for(;i<n;i++){K=i+m;for(j=0;j<K;j++){a[128*i+j]=a[128*i+j]+alpha+i-j;}}affine_range_i=i;affine_range_j=j;affine_range_k=k;affine_range_K=K;affine_range_L=L;}
void affine_large3(int *a,int start,int n,int m,int p,int alpha){int i=start,j=77,k=91,K=79,L=83;for(;i<n;i++){K=i+m;for(j=0;j<K;j++){L=j+p;for(k=0;k<L;k++){a[4096*i+64*j+k]=a[4096*i+64*j+k]+alpha+i-j+k;}}}affine_range_i=i;affine_range_j=j;affine_range_k=k;affine_range_K=K;affine_range_L=L;}
void affine_large_chain2(int *a,int start,int n,int m,int p,int alpha){int i=start,j=77,k=91,K=79,L=83;for(;i<n;i++){K=i+m;for(j=0;j<K;j++){a[128*i+j]=a[128*i+j+127]+alpha+i-j;}}affine_range_i=i;affine_range_j=j;affine_range_k=k;affine_range_K=K;affine_range_L=L;}
void affine_range_case(int which,int null,int start,int n,int m,int p,int alpha){int a[196608],x;int *base;for(x=0;x<196608;x++)a[x]=3*x+1;base=a+32768;if(null)base=0;
if(which==0)affine_large2(base,start,n,m,p,alpha);
if(which==1)affine_large3(base,start,n,m,p,alpha);
if(which==2)affine_large_chain2(base,start,n,m,p,alpha);
printf("%d %d %d %d %d %d %d %d %d %d %d %d",which,null,start,n,m,p,alpha,affine_range_i,affine_range_j,affine_range_k,affine_range_K,affine_range_L);for(x=0;x<196608;x++)printf(" %d",a[x]);printf("\n");}
int main(void){
affine_range_case(0,0,-2,12,4,2,-7);
affine_range_case(0,0,-2,12,4,2,2147483647);
affine_range_case(0,0,0,16,2,2,-7);
affine_range_case(0,0,0,16,2,2,2147483647);
affine_range_case(0,0,1,24,3,3,-7);
affine_range_case(0,0,1,24,3,3,2147483647);
affine_range_case(0,0,0,32,2,2,-7);
affine_range_case(0,0,0,32,2,2,2147483647);
affine_range_case(0,0,-4,16,8,8,-7);
affine_range_case(0,0,-4,16,8,8,2147483647);
affine_range_case(0,0,3,2,2,2,-7);
affine_range_case(0,0,3,2,2,2,2147483647);
affine_range_case(0,0,0,12,-1,2,-7);
affine_range_case(0,0,0,12,-1,2,2147483647);
affine_range_case(0,0,33,34,1,1,-7);
affine_range_case(0,0,33,34,1,1,2147483647);
affine_range_case(0,0,-5,12,8,8,-7);
affine_range_case(0,0,-5,12,8,8,2147483647);
affine_range_case(1,0,-2,12,4,2,-7);
affine_range_case(1,0,-2,12,4,2,2147483647);
affine_range_case(1,0,0,16,2,2,-7);
affine_range_case(1,0,0,16,2,2,2147483647);
affine_range_case(1,0,1,24,3,3,-7);
affine_range_case(1,0,1,24,3,3,2147483647);
affine_range_case(1,0,0,32,2,2,-7);
affine_range_case(1,0,0,32,2,2,2147483647);
affine_range_case(1,0,-4,16,8,8,-7);
affine_range_case(1,0,-4,16,8,8,2147483647);
affine_range_case(1,0,3,2,2,2,-7);
affine_range_case(1,0,3,2,2,2,2147483647);
affine_range_case(1,0,0,12,-1,2,-7);
affine_range_case(1,0,0,12,-1,2,2147483647);
affine_range_case(1,0,33,34,1,1,-7);
affine_range_case(1,0,33,34,1,1,2147483647);
affine_range_case(1,0,-5,12,8,8,-7);
affine_range_case(1,0,-5,12,8,8,2147483647);
affine_range_case(2,0,-2,12,4,2,-7);
affine_range_case(2,0,-2,12,4,2,2147483647);
affine_range_case(2,0,0,16,2,2,-7);
affine_range_case(2,0,0,16,2,2,2147483647);
affine_range_case(2,0,1,24,3,3,-7);
affine_range_case(2,0,1,24,3,3,2147483647);
affine_range_case(2,0,0,32,2,2,-7);
affine_range_case(2,0,0,32,2,2,2147483647);
affine_range_case(2,0,-4,16,8,8,-7);
affine_range_case(2,0,-4,16,8,8,2147483647);
affine_range_case(2,0,3,2,2,2,-7);
affine_range_case(2,0,3,2,2,2,2147483647);
affine_range_case(2,0,0,12,-1,2,-7);
affine_range_case(2,0,0,12,-1,2,2147483647);
affine_range_case(2,0,33,34,1,1,-7);
affine_range_case(2,0,33,34,1,1,2147483647);
affine_range_case(2,0,-5,12,8,8,-7);
affine_range_case(2,0,-5,12,8,8,2147483647);
affine_range_case(0,1,(-2147483647-1),(-2147483647-1),2147483647,(-2147483647-1),-7);
affine_range_case(0,1,2147483647,2147483647,2147483647,(-2147483647-1),-7);
affine_range_case(1,1,(-2147483647-1),(-2147483647-1),2147483647,(-2147483647-1),-7);
affine_range_case(1,1,2147483647,2147483647,2147483647,(-2147483647-1),-7);
affine_range_case(2,1,(-2147483647-1),(-2147483647-1),2147483647,(-2147483647-1),-7);
affine_range_case(2,1,2147483647,2147483647,2147483647,(-2147483647-1),-7);
return 0;}
