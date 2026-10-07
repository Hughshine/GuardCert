#include <stdio.h>
int lm_i,lm_j,lm_k,lm_K,lm_L;
void loaded_accum2(int *a,int *b,int *c,int *limit,int start,int m,int p,int alpha){int i=start,j=77,k=91,K=79,L=83;for(;i<*limit+1;i++){K=i+m;for(j=0;j<K;j++){a[128*i+16*j]=a[128*i+16*j]+alpha+i-j;}}lm_i=i;lm_j=j;lm_k=k;lm_K=K;lm_L=L;}
void loaded_accum3(int *a,int *b,int *c,int *limit,int start,int m,int p,int alpha){int i=start,j=77,k=91,K=79,L=83;for(;i<*limit+1;i++){K=i+m;for(j=0;j<K;j++){L=j+p;for(k=0;k<L;k++){a[128*i+16*j+k]=a[128*i+16*j+k]+alpha+i-j+k;}}}lm_i=i;lm_j=j;lm_k=k;lm_K=K;lm_L=L;}
void loaded_multi3(int *a,int *b,int *c,int *limit,int start,int m,int p,int alpha){int i=start,j=77,k=91,K=79,L=83;for(;i<*limit+1;i++){K=i+m;for(j=0;j<K;j++){L=j+p;for(k=0;k<L;k++){a[128*i+16*j+k]=b[128*i+16*j+k]+c[128*i+16*j+k]+alpha+i-j+k;}}}lm_i=i;lm_j=j;lm_k=k;lm_K=K;lm_L=L;}
void loaded_chain2(int *a,int *b,int *c,int *limit,int start,int m,int p,int alpha){int i=start,j=77,k=91,K=79,L=83;for(;i<*limit+1;i++){K=i+m;for(j=0;j<K;j++){a[128*i+16*j]=a[128*i+16*j+112]+alpha+i-j;}}lm_i=i;lm_j=j;lm_k=k;lm_K=K;lm_L=L;}
void loaded_store3(int *a,int *b,int *c,int *limit,int start,int m,int p,int alpha){int i=start,j=77,k=91,K=79,L=83;for(;i<*limit+1;i++){K=i+m;for(j=0;j<K;j++){L=j+p;for(k=0;k<L;k++){a[128*i+16*j+k]=1;}}}lm_i=i;lm_j=j;lm_k=k;lm_K=K;lm_L=L;}
void loaded_undefined3(int *a,int *b,int *c,int *limit,int start,int m,int p,int alpha){int i=start,j=77,k=91,K=79,L=83;int local_p,local_alpha; if(start<*limit+1 && *limit+m>0)local_p=p; if(start<*limit+1 && *limit+m>0 && *limit-1+m+p>0)local_alpha=alpha;for(;i<*limit+1;i++){K=i+m;for(j=0;j<K;j++){L=j+local_p;for(k=0;k<L;k++){a[128*i+16*j+k]=a[128*i+16*j+k]+local_alpha+i-j+k;}}}lm_i=i;lm_j=j;lm_k=k;lm_K=K;lm_L=L;}
void loaded_twice2(int *a,int *b,int *c,int *limit,int start,int m,int p,int alpha){int i=start,j=77,k=91,K=79,L=83;for(;i<*limit+1;i++){K=i+m;for(j=0;j<K;j++){a[128*i+16*j]=a[128*i+16*j]+alpha+i-j;}}i=0;for(;i<*limit+1;i++){K=i+m;for(j=0;j<K;j++){a[128*i+16*j]=a[128*i+16*j]+alpha+i-j;}}lm_i=i;lm_j=j;lm_k=k;lm_K=K;lm_L=L;}
void loaded_small2(int *a,int *limit){int i=0,j=77,K=79;for(;i<*limit+1;i++){K=1;for(j=0;j<K;j++){a[i+0*j]=1;}}lm_i=i;lm_j=j;}
void loaded_short_run(void){int a[2];a[0]=4;a[1]=3;loaded_small2(a,a+1);printf("short %d %d %d %d\n",lm_i,lm_j,a[0],a[1]);}
void loaded_case(int kind,int view,int start,int n,int m,int p,int alpha){int A[6144],B[2048],C[2048],x;int *a,*b,*c,*limit;
for(x=0;x<6144;x++)A[x]=3*x+1;for(x=0;x<2048;x++){B[x]=3*x+18;C[x]=3*x+35;}
a=A+128;b=B+128;c=C+128;limit=&n;
if(view==1){limit=a;*limit=n;}if(view==2){limit=a+128;*limit=n;}if(view==3){limit=a+1800;*limit=n;}
if(view==4){b=a;c=a;}if(view==5){b=a+1024;c=a+2048;}if(view==6){b=a+1;c=a+2;}if(view==7){a=0;b=0;c=0;}
if(kind==0)loaded_accum2(a,b,c,limit,start,m,p,alpha);
if(kind==1)loaded_accum3(a,b,c,limit,start,m,p,alpha);
if(kind==2)loaded_multi3(a,b,c,limit,start,m,p,alpha);
if(kind==3)loaded_chain2(a,b,c,limit,start,m,p,alpha);
if(kind==4)loaded_store3(a,b,c,limit,start,m,p,alpha);
if(kind==5)loaded_undefined3(a,b,c,limit,start,m,p,alpha);
if(kind==6)loaded_twice2(a,b,c,limit,start,m,p,alpha);
printf("%d %d %d %d %d %d %d %d %d %d %d %d %d",kind,view,start,n,m,p,alpha,lm_i,lm_j,lm_k,lm_K,lm_L,*limit);
for(x=0;x<6144;x++)printf(" %d",A[x]);for(x=0;x<2048;x++)printf(" %d",B[x]);for(x=0;x<2048;x++)printf(" %d",C[x]);printf("\n");}
int main(void){
loaded_case(0,7,0,2147483647,2,1,5);
loaded_case(0,7,0,-2,2,1,5);
loaded_case(0,0,0,3,4,1,5);
loaded_case(0,0,0,2,2,2,-7);
loaded_case(0,0,1,3,2,1,5);
loaded_case(0,0,-1,2,2,1,5);
loaded_case(0,0,0,3,0,1,5);
loaded_case(0,0,0,3,2,0,5);
loaded_case(0,0,0,9,2,1,5);
loaded_case(0,0,0,2,2,1,2147483647);
loaded_case(0,0,0,2,2,1,(-2147483647-1));
loaded_case(0,7,0,-1,2,1,5);
loaded_case(0,7,0,3,-3,1,5);
loaded_case(0,3,0,3,2,1,5);
loaded_case(0,7,1,2,2147483647,1,5);
loaded_case(1,7,0,2147483647,2,1,5);
loaded_case(1,7,0,-2,2,1,5);
loaded_case(1,0,0,3,4,1,5);
loaded_case(1,0,0,2,2,2,-7);
loaded_case(1,0,1,3,2,1,5);
loaded_case(1,0,-1,2,2,1,5);
loaded_case(1,0,0,3,0,1,5);
loaded_case(1,0,0,3,2,0,5);
loaded_case(1,0,0,9,2,1,5);
loaded_case(1,0,0,2,2,1,2147483647);
loaded_case(1,0,0,2,2,1,(-2147483647-1));
loaded_case(1,7,0,-1,2,1,5);
loaded_case(1,7,0,3,-3,1,5);
loaded_case(1,3,0,3,2,1,5);
loaded_case(1,7,1,2,2147483647,1,5);
loaded_case(1,7,0,3,2,-5,5);
loaded_case(1,7,0,3,2,(-2147483647-1),5);
loaded_case(2,7,0,2147483647,2,1,5);
loaded_case(2,7,0,-2,2,1,5);
loaded_case(2,0,0,3,4,1,5);
loaded_case(2,0,0,2,2,2,-7);
loaded_case(2,0,1,3,2,1,5);
loaded_case(2,0,-1,2,2,1,5);
loaded_case(2,0,0,3,0,1,5);
loaded_case(2,0,0,3,2,0,5);
loaded_case(2,0,0,9,2,1,5);
loaded_case(2,0,0,2,2,1,2147483647);
loaded_case(2,0,0,2,2,1,(-2147483647-1));
loaded_case(2,7,0,-1,2,1,5);
loaded_case(2,7,0,3,-3,1,5);
loaded_case(2,3,0,3,2,1,5);
loaded_case(2,7,1,2,2147483647,1,5);
loaded_case(2,7,0,3,2,-5,5);
loaded_case(2,7,0,3,2,(-2147483647-1),5);
loaded_case(3,7,0,2147483647,2,1,5);
loaded_case(3,7,0,-2,2,1,5);
loaded_case(3,0,0,3,4,1,5);
loaded_case(3,0,0,2,2,2,-7);
loaded_case(3,0,1,3,2,1,5);
loaded_case(3,0,-1,2,2,1,5);
loaded_case(3,0,0,3,0,1,5);
loaded_case(3,0,0,3,2,0,5);
loaded_case(3,0,0,9,2,1,5);
loaded_case(3,0,0,2,2,1,2147483647);
loaded_case(3,0,0,2,2,1,(-2147483647-1));
loaded_case(3,7,0,-1,2,1,5);
loaded_case(3,7,0,3,-3,1,5);
loaded_case(3,3,0,3,2,1,5);
loaded_case(3,7,1,2,2147483647,1,5);
loaded_case(4,7,0,2147483647,2,1,5);
loaded_case(4,7,0,-2,2,1,5);
loaded_case(4,0,0,3,4,1,5);
loaded_case(4,0,0,2,2,2,-7);
loaded_case(4,0,1,3,2,1,5);
loaded_case(4,0,-1,2,2,1,5);
loaded_case(4,0,0,3,0,1,5);
loaded_case(4,0,0,3,2,0,5);
loaded_case(4,0,0,9,2,1,5);
loaded_case(4,0,0,2,2,1,2147483647);
loaded_case(4,0,0,2,2,1,(-2147483647-1));
loaded_case(4,7,0,-1,2,1,5);
loaded_case(4,7,0,3,-3,1,5);
loaded_case(4,3,0,3,2,1,5);
loaded_case(4,7,1,2,2147483647,1,5);
loaded_case(4,7,0,3,2,-5,5);
loaded_case(4,7,0,3,2,(-2147483647-1),5);
loaded_case(5,7,0,2147483647,2,1,5);
loaded_case(5,7,0,-2,2,1,5);
loaded_case(5,0,0,3,4,1,5);
loaded_case(5,0,0,2,2,2,-7);
loaded_case(5,0,1,3,2,1,5);
loaded_case(5,0,-1,2,2,1,5);
loaded_case(5,0,0,3,0,1,5);
loaded_case(5,0,0,3,2,0,5);
loaded_case(5,0,0,9,2,1,5);
loaded_case(5,0,0,2,2,1,2147483647);
loaded_case(5,0,0,2,2,1,(-2147483647-1));
loaded_case(5,7,0,-1,2,1,5);
loaded_case(5,7,0,3,-3,1,5);
loaded_case(5,3,0,3,2,1,5);
loaded_case(5,7,1,2,2147483647,1,5);
loaded_case(5,7,0,3,2,-5,5);
loaded_case(5,7,0,3,2,(-2147483647-1),5);
loaded_case(6,7,0,2147483647,2,1,5);
loaded_case(6,7,0,-2,2,1,5);
loaded_case(6,0,0,3,4,1,5);
loaded_case(6,0,0,2,2,2,-7);
loaded_case(6,0,1,3,2,1,5);
loaded_case(6,0,-1,2,2,1,5);
loaded_case(6,0,0,3,0,1,5);
loaded_case(6,0,0,3,2,0,5);
loaded_case(6,0,0,9,2,1,5);
loaded_case(6,0,0,2,2,1,2147483647);
loaded_case(6,0,0,2,2,1,(-2147483647-1));
loaded_case(6,7,0,-1,2,1,5);
loaded_case(6,7,0,3,-3,1,5);
loaded_case(6,3,0,3,2,1,5);
loaded_case(4,1,0,3,4,1,5);
loaded_case(4,2,0,3,4,1,5);
loaded_case(2,4,0,3,4,1,5);
loaded_case(2,5,0,3,4,1,5);
loaded_case(2,6,0,3,4,1,5);
loaded_short_run();return 0;}
