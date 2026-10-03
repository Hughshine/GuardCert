#include <stdio.h>
int mixed_ga[240],mixed_gb[180],mixed_gc[160];
static void emit(const char *name,const char *suffix,int *a,int extent,int i,int j,int k,int m,int p) {
  int x;printf("%s-%s %d %d %d %d %d",name,suffix,i,j,k,m,p);
  for(x=0;x<extent;++x) printf(" %d",a[x]);putchar(10);
}
void mixed_write_chain(int start,int n,int m,int p) {
  int a[220],b[170],c[150];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<220;++x) a[x]=x*3+1;
  for(x=0;x<170;++x) b[x]=x*5+2;
  for(x=0;x<150;++x) c[x]=-777;
  for(;i<n;++i) { k=2*i+m-p;for(j=0;j<k;++j) {
    a[i*22+j]=i*37+j+7;
    b[i*17+j]=a[i*22+j];
    c[i*15+j]=b[i*17+j];
    b[i*17+j]=b[i*17+j]+(i*11+j+19);
  } }
  emit("mixed_write_chain","a",a,220,i,j,k,m,p);
  emit("mixed_write_chain","b",b,170,i,j,k,m,p);
  emit("mixed_write_chain","c",c,150,i,j,k,m,p);
}
void mixed_copy_chain(int start,int n,int m,int p) {
  int a[210],b[140],c[180];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<210;++x) a[x]=x*3+1;
  for(x=0;x<140;++x) b[x]=x*5+2;
  for(x=0;x<180;++x) c[x]=-777;
  for(;i<n;++i) { k=2*i+m-p;for(j=0;j<k;++j) {
    b[i*14+j]=a[i*21+j];
    c[i*18+j]=b[i*14+j];
    c[i*18+j]=c[i*18+j]+(i*11+j+19);
  } }
  emit("mixed_copy_chain","a",a,210,i,j,k,m,p);
  emit("mixed_copy_chain","b",b,140,i,j,k,m,p);
  emit("mixed_copy_chain","c",c,180,i,j,k,m,p);
}
void mixed_global_chain(int start,int n,int m,int p) {
  int i=start,j=99,k=55,x,r;
  for(x=0;x<240;++x) mixed_ga[x]=x*3+1;
  for(x=0;x<180;++x) mixed_gb[x]=x*5+2;
  for(x=0;x<160;++x) mixed_gc[x]=-777;
  for(;i<n;++i) { k=m-2*i+p;for(j=0;j<k;++j) {
    mixed_gb[i*18+j]=mixed_ga[i*24+j];
    mixed_gc[i*16+j]=mixed_gb[i*18+j];
    mixed_gb[i*18+j]=mixed_gb[i*18+j]+(i*11+j+19);
  } }
  emit("mixed_global_chain","a",mixed_ga,240,i,j,k,m,p);
  emit("mixed_global_chain","b",mixed_gb,180,i,j,k,m,p);
  emit("mixed_global_chain","c",mixed_gc,160,i,j,k,m,p);
}
void mixed_context_chain(int start,int n,int m,int p) {
  int a[220],b[170],c[150];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<220;++x) a[x]=x*3+1;
  for(x=0;x<170;++x) b[x]=x*5+2;
  for(x=0;x<150;++x) c[x]=-777;
  for(r=0;r<2;++r) { i=start;
  for(;i<n;++i) { k=2*i+m-p;for(j=0;j<k;++j) {
    a[i*22+j]=i*37+j+7;
    b[i*17+j]=a[i*22+j];
    c[i*15+j]=b[i*17+j];
    b[i*17+j]=b[i*17+j]+(i*11+j+19);
  } }
  }
  emit("mixed_context_chain","a",a,220,i,j,k,m,p);
  emit("mixed_context_chain","b",b,170,i,j,k,m,p);
  emit("mixed_context_chain","c",c,150,i,j,k,m,p);
}
void mixed_alias_chain(int start,int n,int m,int p) {
  int a[240],b[240],c[150];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<240;++x) a[x]=x*3+1;
  for(x=0;x<240;++x) b[x]=x*5+2;
  for(x=0;x<150;++x) c[x]=-777;
  for(;i<n;++i) { k=2*i+m-p;for(j=0;j<k;++j) {
    b[i*20+j]=b[i*24+j];
    c[i*15+j]=b[i*20+j];
    b[i*20+j]=b[i*20+j]+(i*11+j+19);
  } }
  emit("mixed_alias_chain","a",a,240,i,j,k,m,p);
  emit("mixed_alias_chain","b",b,240,i,j,k,m,p);
  emit("mixed_alias_chain","c",c,150,i,j,k,m,p);
}
void mixed_alias_reverse(int start,int n,int m,int p) {
  int a[240],b[240],c[150];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<240;++x) a[x]=x*3+1;
  for(x=0;x<240;++x) b[x]=x*5+2;
  for(x=0;x<150;++x) c[x]=-777;
  for(;i<n;++i) { k=m-2*i+p;for(j=0;j<k;++j) {
    b[i*24+j]=b[i*20+j];
    c[i*15+j]=b[i*24+j];
    b[i*24+j]=b[i*24+j]+(i*11+j+19);
  } }
  emit("mixed_alias_reverse","a",a,240,i,j,k,m,p);
  emit("mixed_alias_reverse","b",b,240,i,j,k,m,p);
  emit("mixed_alias_reverse","c",c,150,i,j,k,m,p);
}
void mixed_neighbor_chain(int start,int n,int m,int p) {
  int a[220],b[170],c[150];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<220;++x) a[x]=x*3+1;
  for(x=0;x<170;++x) b[x]=x*5+2;
  for(x=0;x<150;++x) c[x]=-777;
  for(;i<n;++i) { k=2*i+m-p;for(j=0;j<k;++j) {
    b[i*17+j]=a[i*22+j+1];
    c[i*15+j]=b[i*17+j];
    b[i*17+j]=b[i*17+j]+(i*11+j+19);
  } }
  emit("mixed_neighbor_chain","a",a,220,i,j,k,m,p);
  emit("mixed_neighbor_chain","b",b,170,i,j,k,m,p);
  emit("mixed_neighbor_chain","c",c,150,i,j,k,m,p);
}
void mixed_nonlinear_chain(int start,int n,int m,int p) {
  int a[220],b[170],c[150];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<220;++x) a[x]=x*3+1;
  for(x=0;x<170;++x) b[x]=x*5+2;
  for(x=0;x<150;++x) c[x]=-777;
  for(;i<n;++i) { k=i*i+m-p;for(j=0;j<k;++j) {
    b[i*17+j]=a[i*22+j];
    c[i*15+j]=b[i*17+j];
    b[i*17+j]=b[i*17+j]+(i*11+j+19);
  } }
  emit("mixed_nonlinear_chain","a",a,220,i,j,k,m,p);
  emit("mixed_nonlinear_chain","b",b,170,i,j,k,m,p);
  emit("mixed_nonlinear_chain","c",c,150,i,j,k,m,p);
}
int main(void) { int n,m,p; for(n=0;n<=5;++n) for(m=-1;m<=6;++m) for(p=-2;p<=2;++p) {
  mixed_write_chain(0,n,m,p);
  mixed_copy_chain(0,n,m,p);
  mixed_global_chain(0,n,m,p);
  mixed_context_chain(0,n,m,p);
  mixed_alias_chain(0,n,m,p);
  mixed_alias_reverse(0,n,m,p);
  mixed_neighbor_chain(0,n,m,p);
  mixed_nonlinear_chain(0,n,m,p);
}
  mixed_write_chain(2,4,5,1);mixed_write_chain(0,-2,2147483647,(-2147483647-1));mixed_write_chain(0,0,(-2147483647-1),2147483647);
  mixed_copy_chain(2,4,5,1);mixed_copy_chain(0,-2,2147483647,(-2147483647-1));mixed_copy_chain(0,0,(-2147483647-1),2147483647);
  mixed_global_chain(2,4,5,1);mixed_global_chain(0,-2,2147483647,(-2147483647-1));mixed_global_chain(0,0,(-2147483647-1),2147483647);
  mixed_context_chain(2,4,5,1);mixed_context_chain(0,-2,2147483647,(-2147483647-1));mixed_context_chain(0,0,(-2147483647-1),2147483647);
  mixed_alias_chain(2,4,5,1);mixed_alias_chain(0,-2,2147483647,(-2147483647-1));mixed_alias_chain(0,0,(-2147483647-1),2147483647);
  mixed_alias_reverse(2,4,5,1);mixed_alias_reverse(0,-2,2147483647,(-2147483647-1));mixed_alias_reverse(0,0,(-2147483647-1),2147483647);
  mixed_neighbor_chain(2,4,5,1);mixed_neighbor_chain(0,-2,2147483647,(-2147483647-1));mixed_neighbor_chain(0,0,(-2147483647-1),2147483647);
  mixed_nonlinear_chain(2,4,5,1);mixed_nonlinear_chain(0,-2,2147483647,(-2147483647-1));mixed_nonlinear_chain(0,0,(-2147483647-1),2147483647);
  mixed_alias_chain(0,4,9,0);mixed_alias_reverse(0,4,15,0);
  mixed_write_chain(0,4,100,99);mixed_context_chain(0,4,100,99);
  return 0; }
