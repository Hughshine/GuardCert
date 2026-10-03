#include <stdio.h>
#include <limits.h>
int ga[200],gb[200];
static void emit(const char *tag,int *a,int i,int j,int k,int m,int p) {
  int x;printf("%s %d %d %d %d %d",tag,i,j,k,m,p);for(x=0;x<200;++x)printf(" %d",a[x]);putchar('\n');
}
void affine_growing(int start,int n,int m,int p) {
  int a[200],b[200],c[200],i=start,j=99,k=55,x,r;
  for(x=0;x<200;++x){a[x]=-999;b[x]=-777;c[x]=-555;}
  for(;i<n;++i){k=2*i+m-p;for(j=0;j<k;++j){
    a[i*20+j]=i*37+j+7;
  }}
  emit("affine_growing-a",a,i,j,k,m,p);
}
void affine_scaled_right(int start,int n,int m,int p) {
  int a[200],b[200],c[200],i=start,j=99,k=55,x,r;
  for(x=0;x<200;++x){a[x]=-999;b[x]=-777;c[x]=-555;}
  for(;i<n;++i){k=i*2+m-p;for(j=0;j<k;++j){
    a[i*20+j]=i*37+j+7;
  }}
  emit("affine_scaled_right-a",a,i,j,k,m,p);
}
void affine_descending(int start,int n,int m,int p) {
  int a[200],b[200],c[200],i=start,j=99,k=55,x,r;
  for(x=0;x<200;++x){a[x]=-999;b[x]=-777;c[x]=-555;}
  for(;i<n;++i){k=m-2*i+p;for(j=0;j<k;++j){
    a[i*20+j]=i*37+j+7;
  }}
  emit("affine_descending-a",a,i,j,k,m,p);
}
void affine_bound_parameter(int start,int n,int m,int p) {
  int a[200],b[200],c[200],i=start,j=99,k=55,x,r;
  for(x=0;x<200;++x){a[x]=-999;b[x]=-777;c[x]=-555;}
  for(;i<n;++i){k=2*i+m-p+n;for(j=0;j<k;++j){
    a[i*20+j]=i*37+j+7;
  }}
  emit("affine_bound_parameter-a",a,i,j,k,m,p);
}
void affine_constant(int start,int n,int m,int p) {
  int a[200],b[200],c[200],i=start,j=99,k=55,x,r;
  for(x=0;x<200;++x){a[x]=-999;b[x]=-777;c[x]=-555;}
  for(;i<n;++i){k=m+p;for(j=0;j<k;++j){
    a[i*20+j]=i*37+j+7;
  }}
  emit("affine_constant-a",a,i,j,k,m,p);
}
void affine_copy(int start,int n,int m,int p) {
  int a[200],b[200],c[200],i=start,j=99,k=55,x,r;
  for(x=0;x<200;++x){a[x]=-999;b[x]=-777;c[x]=-555;}
  for(x=0;x<200;++x)a[x]=x%3==0?INT_MAX:(x%3==1?INT_MIN:x*3+1);
  for(;i<n;++i){k=2*i+m-p;for(j=0;j<k;++j){
    b[i*20+j]=a[i*20+j];
  }}
  emit("affine_copy-a",a,i,j,k,m,p);
  emit("affine_copy-b",b,i,j,k,m,p);
}
void affine_chain(int start,int n,int m,int p) {
  int a[200],b[200],c[200],i=start,j=99,k=55,x,r;
  for(x=0;x<200;++x){a[x]=-999;b[x]=-777;c[x]=-555;}
  for(;i<n;++i){k=2*i+m-p;for(j=0;j<k;++j){
    a[i*20+j]=i*37+j+7;
    b[i*20+j]=a[i*20+j]+(i*11+j+19);c[i*20+j]=b[i*20+j];
  }}
  emit("affine_chain-a",a,i,j,k,m,p);
  emit("affine_chain-b",b,i,j,k,m,p);
  emit("affine_chain-c",c,i,j,k,m,p);
}
void affine_prefix(int start,int n,int m,int p) {
  int a[200],b[200],c[200],i=start,j=99,k=55,x,r;
  for(x=0;x<200;++x){a[x]=-999;b[x]=-777;c[x]=-555;}
  for(;i<n;++i){k=2*i+m-p;for(j=0;j<k;++j){
    a[i*20+j]=i*37+j+7;
    a[i*20+j]=a[i*20]+(i*17+j+11);b[i*20+j]=a[i*20+j];
  }}
  emit("affine_prefix-a",a,i,j,k,m,p);
  emit("affine_prefix-b",b,i,j,k,m,p);
}
void affine_global(int start,int n,int m,int p) {
  int a[200],b[200],c[200],i=start,j=99,k=55,x,r;
  for(x=0;x<200;++x){a[x]=-999;b[x]=-777;c[x]=-555;}
  for(x=0;x<200;++x){ga[x]=-999;gb[x]=-777;}
  for(;i<n;++i){k=m-2*i+p;for(j=0;j<k;++j){
    ga[i*20+j]=i*37+j+7;gb[i*20+j]=ga[i*20+j];
  }}
  emit("affine_global-a",ga,i,j,k,m,p);
  emit("affine_global-b",gb,i,j,k,m,p);
}
void affine_context(int start,int n,int m,int p) {
  int a[200],b[200],c[200],i=start,j=99,k=55,x,r;
  for(x=0;x<200;++x){a[x]=-999;b[x]=-777;c[x]=-555;}
  for(r=0;r<2;++r){i=start;
  for(;i<n;++i){k=2*i+m-p;for(j=0;j<k;++j){
    a[i*20+j]=i*37+j+7;
    b[i*20+j]=b[i*20+j]+(i*11+j+19);a[i*20+j]=a[i*20+j]+(i*23+j+3);
  }}
  }
  emit("affine_context-a",a,i,j,k,m,p);
  emit("affine_context-b",b,i,j,k,m,p);
}
void affine_nonlinear(int start,int n,int m,int p) {
  int a[200],b[200],c[200],i=start,j=99,k=55,x,r;
  for(x=0;x<200;++x){a[x]=-999;b[x]=-777;c[x]=-555;}
  for(;i<n;++i){k=i*i+m-p;for(j=0;j<k;++j){
    a[i*20+j]=i*37+j+7;
  }}
  emit("affine_nonlinear-a",a,i,j,k,m,p);
}
void affine_unsigned(int start,int n,int m,int p) {
  int a[200],b[200],c[200],i=start,j=99,k=55,x,r;
  for(x=0;x<200;++x){a[x]=-999;b[x]=-777;c[x]=-555;}
  for(;i<n;++i){k=(unsigned)i*2+m-p;for(j=0;j<k;++j){
    a[i*20+j]=i*37+j+7;
  }}
  emit("affine_unsigned-a",a,i,j,k,m,p);
}
void affine_counter_coupled(int n){
  int a[200],i=0,j=1,k=55,x;for(x=0;x<200;++x)a[x]=-999;
  for(;i<n;++i){k=j;for(j=0;j<k;++j){a[i*20+j]=i*37+j+7;}}
  emit("affine_counter_coupled-a",a,i,j,k,0,0);
}
int main(void){int n,m,p;
  for(n=0;n<=5;++n)for(m=-1;m<=6;++m)for(p=-2;p<=2;++p){
    affine_growing(0,n,m,p);
    affine_scaled_right(0,n,m,p);
    affine_descending(0,n,m,p);
    affine_bound_parameter(0,n,m,p);
    affine_constant(0,n,m,p);
    affine_copy(0,n,m,p);
    affine_chain(0,n,m,p);
    affine_prefix(0,n,m,p);
    affine_global(0,n,m,p);
    affine_context(0,n,m,p);
    affine_nonlinear(0,n,m,p);
    affine_unsigned(0,n,m,p);
  }
  affine_growing(2,4,5,1);
  affine_growing(0,-2,INT_MAX,INT_MIN);
  affine_growing(0,0,INT_MIN,INT_MAX);
  affine_scaled_right(2,4,5,1);
  affine_scaled_right(0,-2,INT_MAX,INT_MIN);
  affine_scaled_right(0,0,INT_MIN,INT_MAX);
  affine_descending(2,4,5,1);
  affine_descending(0,-2,INT_MAX,INT_MIN);
  affine_descending(0,0,INT_MIN,INT_MAX);
  affine_bound_parameter(2,4,5,1);
  affine_bound_parameter(0,-2,INT_MAX,INT_MIN);
  affine_bound_parameter(0,0,INT_MIN,INT_MAX);
  affine_constant(2,4,5,1);
  affine_constant(0,-2,INT_MAX,INT_MIN);
  affine_constant(0,0,INT_MIN,INT_MAX);
  affine_copy(2,4,5,1);
  affine_copy(0,-2,INT_MAX,INT_MIN);
  affine_copy(0,0,INT_MIN,INT_MAX);
  affine_chain(2,4,5,1);
  affine_chain(0,-2,INT_MAX,INT_MIN);
  affine_chain(0,0,INT_MIN,INT_MAX);
  affine_prefix(2,4,5,1);
  affine_prefix(0,-2,INT_MAX,INT_MIN);
  affine_prefix(0,0,INT_MIN,INT_MAX);
  affine_global(2,4,5,1);
  affine_global(0,-2,INT_MAX,INT_MIN);
  affine_global(0,0,INT_MIN,INT_MAX);
  affine_context(2,4,5,1);
  affine_context(0,-2,INT_MAX,INT_MIN);
  affine_context(0,0,INT_MIN,INT_MAX);
  affine_nonlinear(2,4,5,1);
  affine_nonlinear(0,-2,INT_MAX,INT_MIN);
  affine_nonlinear(0,0,INT_MIN,INT_MAX);
  affine_unsigned(2,4,5,1);
  affine_unsigned(0,-2,INT_MAX,INT_MIN);
  affine_unsigned(0,0,INT_MIN,INT_MAX);
  affine_growing(0,4,100,99);affine_copy(0,4,100,99);affine_counter_coupled(5);
  return 0;
}
