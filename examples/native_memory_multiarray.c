#include <stdio.h>
int ga[120],gb[120];
static void emit(const char *name,int *a,int extent,int i,int j) {
  int k; printf("%s %d %d",name,i,j); for(k=0;k<extent;++k) printf(" %d",a[k]); putchar('\n');
}
void multi_two(int start,int n,int m) {
  int a[120],b[120],i=start,j=99,k;
  for(k=0;k<120;++k) {a[k]=-999;b[k]=-777;}
  for(;i<n;++i) {for(j=0;j<m;++j) {
    a[i*10+j]=i*37+j+7;
    b[i*10+j]=b[i*10+j]+(i*11+j+19);
    a[i*10+j]=a[i*10+j]+(i*23+j+3);
  }}
  emit("two-a",a,120,i,j);emit("two-b",b,120,i,j);
}
void multi_three(int start,int n,int m) {
  int a[120],b[120],c[120],i=start,j=99,k;
  for(k=0;k<120;++k) {a[k]=-999;b[k]=-777;c[k]=-555;}
  for(;i<n;++i) {for(j=0;j<m;++j) {
    a[i*10+j]=i*37+j+7;
    b[i*10+j]=b[i*10+j]+(i*11+j+19);
    c[i*10+j]=i*13+j+5;
    c[i*10+j]=c[i*10]+(i*17+j+11);
    c[i*10+j]=c[i*10+j]+(i*23+j+3);
  }}
  emit("three-a",a,120,i,j);emit("three-b",b,120,i,j);emit("three-c",c,120,i,j);
}
void multi_global(int n,int m) {
  int i=0,j=99,k;for(k=0;k<120;++k) {ga[k]=-999;gb[k]=-777;}
  for(;i<n;++i) {for(j=0;j<m;++j) {
    ga[i*10+j]=i*37+j+7;
    gb[i*10+j]=gb[i*10+j]+(i*11+j+19);
    ga[i*10+j]=ga[i*10+j]+(i*23+j+3);
  }}
  emit("global-a",ga,120,i,j);emit("global-b",gb,120,i,j);
}
void multi_enclosing(int n,int m) {
  int a[120],b[120],i=0,j=99,k,r;for(k=0;k<120;++k) {a[k]=-999;b[k]=-777;}
  for(r=0;r<2;++r) {i=0;for(;i<n;++i) {for(j=0;j<m;++j) {
    a[i*10+j]=i*37+j+7;
    b[i*10+j]=b[i*10+j]+(i*11+j+19);
    a[i*10+j]=a[i*10+j]+(i*23+j+3);
  }}}
  emit("enclosing-a",a,120,i,j);emit("enclosing-b",b,120,i,j);
}
void multi_other_layout(int n,int m) {
  int a[120],b[105],i=0,j=99,k;for(k=0;k<120;++k) a[k]=-999;for(k=0;k<105;++k) b[k]=-777;
  for(;i<n;++i) {for(j=0;j<m;++j) {a[i*10+j]=i*37+j+7;b[i*7+j]=i*11+j+19;}}
  emit("layout-a",a,120,i,j);emit("layout-b",b,105,i,j);
}
void multi_cross_read(int n,int m) {
  int a[120],b[120],i=0,j=99,k;for(k=0;k<120;++k) {a[k]=-999;b[k]=-777;}
  for(;i<n;++i) {for(j=0;j<m;++j) {a[i*10+j]=i*37+j+7;b[i*10+j]=a[i*10+j]+(i*11+j+19);}}
  emit("cross-a",a,120,i,j);emit("cross-b",b,120,i,j);
}
int main(void) {
  int n,m;for(n=0;n<=12;++n) {for(m=0;m<=10;++m) {
    multi_two(0,n,m);multi_three(0,n,m);multi_global(n,m);multi_enclosing(n,m);
    multi_two(2,n,m);multi_three(2,n,m);
  }}
  multi_two(0,-1,10);multi_three(0,5,-1);multi_other_layout(12,7);multi_cross_read(12,10);
  return 0;
}
