#include <stdio.h>
int ga[120],gb[120];
static void emit(const char *tag,int *a,int i,int j,int k) {
  int x;printf("%s %d %d %d",tag,i,j,k);for(x=0;x<120;++x) printf(" %d",a[x]);putchar('\n');
}
void ragged_write(int start,int n,int m) {
  int a[120],i=start,j=99,k=55,x;for(x=0;x<120;++x)a[x]=-999;
  for(;i<n;++i){k=i+m;for(j=0;j<k;++j){a[i*10+j]=i*37+j+7;}}
  emit("write-a",a,i,j,k);
}
void ragged_two(int start,int n,int m) {
  int a[120],b[120],i=start,j=99,k=55,x;for(x=0;x<120;++x){a[x]=-999;b[x]=-777;}
  for(;i<n;++i){k=i+m;for(j=0;j<k;++j){
    a[i*10+j]=i*37+j+7;b[i*10+j]=b[i*10+j]+(i*11+j+19);a[i*10+j]=a[i*10+j]+(i*23+j+3);
  }}
  emit("two-a",a,i,j,k);emit("two-b",b,i,j,k);
}
void ragged_prefix(int n,int m) {
  int a[120],b[120],i=0,j=99,k=55,x;for(x=0;x<120;++x){a[x]=-999;b[x]=-777;}
  for(;i<n;++i){k=i+m;for(j=0;j<k;++j){
    a[i*10+j]=i*37+j+7;a[i*10+j]=a[i*10]+(i*17+j+11);b[i*10+j]=a[i*10+j];
  }}
  emit("prefix-a",a,i,j,k);emit("prefix-b",b,i,j,k);
}
void ragged_copy(int n,int m) {
  int a[120],b[120],i=0,j=99,k=55,x;for(x=0;x<120;++x){
    a[x]=x%3==0?2147483647:(x%3==1?(-2147483647-1):x*3+1);b[x]=-777;
  }
  for(;i<n;++i){k=i+m;for(j=0;j<k;++j){b[i*10+j]=a[i*10+j];}}
  emit("copy-a",a,i,j,k);emit("copy-b",b,i,j,k);
}
void ragged_chain(int n,int m) {
  int a[120],b[120],c[120],i=0,j=99,k=55,x;for(x=0;x<120;++x){a[x]=-999;b[x]=-777;c[x]=-555;}
  for(;i<n;++i){k=i+m;for(j=0;j<k;++j){
    a[i*10+j]=i*37+j+7;b[i*10+j]=a[i*10+j]+(i*11+j+19);c[i*10+j]=b[i*10+j];
  }}
  emit("chain-a",a,i,j,k);emit("chain-b",b,i,j,k);emit("chain-c",c,i,j,k);
}
void ragged_global(int n,int m) {
  int i=0,j=99,k=55,x;for(x=0;x<120;++x){ga[x]=-999;gb[x]=-777;}
  for(;i<n;++i){k=i+m;for(j=0;j<k;++j){ga[i*10+j]=i*37+j+7;gb[i*10+j]=ga[i*10+j];}}
  emit("global-a",ga,i,j,k);emit("global-b",gb,i,j,k);
}
void ragged_context(int n,int m) {
  int a[120],b[120],i=0,j=99,k=55,x,r;for(x=0;x<120;++x){a[x]=-999;b[x]=-777;}
  for(r=0;r<2;++r){i=0;for(;i<n;++i){k=i+m;for(j=0;j<k;++j){
    a[i*10+j]=i*37+j+7;b[i*10+j]=b[i*10+j]+(i*11+j+19);a[i*10+j]=a[i*10+j]+(i*23+j+3);
  }}}
  emit("context-a",a,i,j,k);emit("context-b",b,i,j,k);
}
void ragged_other_bound(int n,int m) {
  int a[120],i=0,j=99,k=55,x;for(x=0;x<120;++x)a[x]=-999;
  for(;i<n;++i){k=m-i;for(j=0;j<k;++j){a[i*10+j]=i*37+j+7;}}
  emit("other-a",a,i,j,k);
}
int main(void){int n,m;for(n=0;n<=8;++n){for(m=0;m<=8;++m){
  ragged_write(0,n,m);ragged_write(2,n,m);ragged_two(0,n,m);ragged_two(2,n,m);
  ragged_prefix(n,m);ragged_copy(n,m);ragged_chain(n,m);ragged_global(n,m);ragged_context(n,m);
}}
  ragged_write(0,-2,8);ragged_two(0,5,-2);ragged_copy(5,-2);ragged_context(5,-2);ragged_other_bound(8,8);
  return 0;
}
