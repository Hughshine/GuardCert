#include <stdio.h>
#include <limits.h>
static void emit(const char *tag,int *a,int i,int j,int k,int m,int p,int q){
 int x;printf("%s %d %d %d %d %d %d",tag,i,j,k,m,p,q);for(x=0;x<200;++x)printf(" %d",a[x]);putchar('\n');
}
void affine_only_bound(int n){
 int a[200],i=0,j=99,k=55,x;for(x=0;x<200;++x)a[x]=-999;
 for(;i<n;++i){k=n-i;for(j=0;j<k;++j){a[i*20+j]=i*37+j+7;}}
 emit("only",a,i,j,k,0,0,0);
}
void affine_four_parameters(int n,int m,int p,int q){
 int a[200],i=0,j=99,k=55,x;for(x=0;x<200;++x)a[x]=-999;
 for(;i<n;++i){k=2*i+m-p+q;for(j=0;j<k;++j){a[i*20+j]=i*37+j+7;}}
 emit("four",a,i,j,k,m,p,q);
}
void affine_eager_zero_parameter(int n,int m,int p,int q){
 int a[200],i=0,j=99,k=55,x;for(x=0;x<200;++x)a[x]=-999;
 for(;i<n;++i){k=2*i+m-p+0*q;for(j=0;j<k;++j){a[i*20+j]=i*37+j+7;}}
 emit("zero",a,i,j,k,m,p,q);
}
void affine_repeated_parameters(int n,int m,int p,int q){
 int a[200],i=0,j=99,k=55,x;for(x=0;x<200;++x)a[x]=-999;
 for(;i<n;++i){k=2*i+m-p+q-m;for(j=0;j<k;++j){a[i*20+j]=i*37+j+7;}}
 emit("repeated",a,i,j,k,m,p,q);
}
int main(void){int n,m,p,q;
 for(n=0;n<=5;++n){affine_only_bound(n);
  for(m=-1;m<=5;++m)for(p=-2;p<=2;++p)for(q=-1;q<=2;++q){
   affine_four_parameters(n,m,p,q);affine_eager_zero_parameter(n,m,p,q);affine_repeated_parameters(n,m,p,q);
  }}
 affine_only_bound(-2);affine_four_parameters(0,INT_MAX,INT_MIN,INT_MAX);
 affine_eager_zero_parameter(0,INT_MIN,INT_MAX,INT_MIN);affine_repeated_parameters(0,INT_MAX,INT_MIN,INT_MAX);
 affine_eager_zero_parameter(4,5,1,INT_MAX);
 return 0;
}
