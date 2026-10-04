#include <stdio.h>
int out_i,out_j,out_k,out_K,out_L;
void affine_accumulation(int *a,int *b,int *c,int start,int n,int m,int p){int i=start,j=77,k=91,K=79,L=83;for(;i<n;i++){K=i+m;for(j=0;j<K;j++){L=p;for(k=0;k<L;k++){a[32*i+j]=a[32*i+j]+b[32*i+k]*c[32*k+j];}}}out_i=i;out_j=j;out_k=k;out_K=K;out_L=L;}
void accumulation_case(int mode,int start,int n,int m,int p){int A[2048],B[2048],C[2048],x;int *a,*b,*c;for(x=0;x<2048;x++){A[x]=3*x+1;B[x]=5*x-7;C[x]=2147483647-11*x;}a=A+256;b=B+256;c=C+256;if(mode==1){b=a;c=a;}if(mode==2){b=a+1;c=a+2;}if(mode==3){b=a+512;c=a+1024;}if(mode==4){b=a+32;c=a+64;}if(mode==5){a=0;b=0;c=0;}affine_accumulation(a,b,c,start,n,m,p);printf("%d %d %d %d %d %d %d %d %d %d",mode,start,n,m,p,out_i,out_j,out_k,out_K,out_L);for(x=0;x<2048;x++)printf(" %d",A[x]);for(x=0;x<2048;x++)printf(" %d",B[x]);for(x=0;x<2048;x++)printf(" %d",C[x]);printf("\n");}
int main(void){
accumulation_case(0,0,3,2,3);
accumulation_case(0,-2,2,4,2);
accumulation_case(0,1,4,2,2);
accumulation_case(0,3,2,2147483647,(-2147483647-1));
accumulation_case(0,0,3,-4,(-2147483647-1));
accumulation_case(0,0,3,2,0);
accumulation_case(0,0,3,2,-3);
accumulation_case(0,0,12,2,2);
accumulation_case(0,0,3,9,3);
accumulation_case(1,0,3,2,3);
accumulation_case(1,-2,2,4,2);
accumulation_case(1,1,4,2,2);
accumulation_case(1,3,2,2147483647,(-2147483647-1));
accumulation_case(1,0,3,-4,(-2147483647-1));
accumulation_case(1,0,3,2,0);
accumulation_case(1,0,3,2,-3);
accumulation_case(1,0,12,2,2);
accumulation_case(1,0,3,9,3);
accumulation_case(2,0,3,2,3);
accumulation_case(2,-2,2,4,2);
accumulation_case(2,1,4,2,2);
accumulation_case(2,3,2,2147483647,(-2147483647-1));
accumulation_case(2,0,3,-4,(-2147483647-1));
accumulation_case(2,0,3,2,0);
accumulation_case(2,0,3,2,-3);
accumulation_case(2,0,12,2,2);
accumulation_case(2,0,3,9,3);
accumulation_case(3,0,3,2,3);
accumulation_case(3,-2,2,4,2);
accumulation_case(3,1,4,2,2);
accumulation_case(3,3,2,2147483647,(-2147483647-1));
accumulation_case(3,0,3,-4,(-2147483647-1));
accumulation_case(3,0,3,2,0);
accumulation_case(3,0,3,2,-3);
accumulation_case(3,0,12,2,2);
accumulation_case(3,0,3,9,3);
accumulation_case(4,0,3,2,3);
accumulation_case(4,-2,2,4,2);
accumulation_case(4,1,4,2,2);
accumulation_case(4,3,2,2147483647,(-2147483647-1));
accumulation_case(4,0,3,-4,(-2147483647-1));
accumulation_case(4,0,3,2,0);
accumulation_case(4,0,3,2,-3);
accumulation_case(4,0,12,2,2);
accumulation_case(4,0,3,9,3);
accumulation_case(5,(-2147483647-1),(-2147483647-1),2147483647,(-2147483647-1));
accumulation_case(5,2147483647,2147483647,2147483647,(-2147483647-1));
accumulation_case(5,3,2,2147483647,(-2147483647-1));
return 0;}
