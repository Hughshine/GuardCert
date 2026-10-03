#include <stdio.h>
int layout_ga[240],layout_gb[180];
static void emit(const char *name,const char *suffix,int *a,int extent,int i,int j,int k,int m,int p) {
  int x;printf("%s-%s %d %d %d %d %d",name,suffix,i,j,k,m,p);
  for(x=0;x<extent;++x) printf(" %d",a[x]);putchar('\n');
}
void layout_growing(int start,int n,int m,int p) {
  int a[220],b[170];int i=start,j=99,k=55,x,r;
  for(x=0;x<220;++x) a[x]=x%3==0?2147483647:(x%3==1?(-2147483647-1):x*3+1);
  for(x=0;x<170;++x) b[x]=-777;
  for(;i<n;++i) { k=2*i+m-p;for(j=0;j<k;++j) { b[i*17+j]=a[i*22+j]; } }
  emit("layout_growing","a",a,220,i,j,k,m,p);emit("layout_growing","b",b,170,i,j,k,m,p);
}
void layout_descending(int start,int n,int m,int p) {
  int a[170],b[220];int i=start,j=99,k=55,x,r;
  for(x=0;x<170;++x) a[x]=x%3==0?2147483647:(x%3==1?(-2147483647-1):x*3+1);
  for(x=0;x<220;++x) b[x]=-777;
  for(;i<n;++i) { k=m-2*i+p;for(j=0;j<k;++j) { b[i*22+j]=a[i*17+j]; } }
  emit("layout_descending","a",a,170,i,j,k,m,p);emit("layout_descending","b",b,220,i,j,k,m,p);
}
void layout_constant(int start,int n,int m,int p) {
  int a[210],b[140];int i=start,j=99,k=55,x,r;
  for(x=0;x<210;++x) a[x]=x%3==0?2147483647:(x%3==1?(-2147483647-1):x*3+1);
  for(x=0;x<140;++x) b[x]=-777;
  for(;i<n;++i) { k=m+p;for(j=0;j<k;++j) { b[i*14+j]=a[i*21+j]; } }
  emit("layout_constant","a",a,210,i,j,k,m,p);emit("layout_constant","b",b,140,i,j,k,m,p);
}
void layout_global(int start,int n,int m,int p) {
  int i=start,j=99,k=55,x,r;
  for(x=0;x<240;++x) layout_ga[x]=x%3==0?2147483647:(x%3==1?(-2147483647-1):x*3+1);
  for(x=0;x<180;++x) layout_gb[x]=-777;
  for(;i<n;++i) { k=2*i+m-p;for(j=0;j<k;++j) { layout_gb[i*18+j]=layout_ga[i*24+j]; } }
  emit("layout_global","a",layout_ga,240,i,j,k,m,p);emit("layout_global","b",layout_gb,180,i,j,k,m,p);
}
void layout_context(int start,int n,int m,int p) {
  int a[150],b[200];int i=start,j=99,k=55,x,r;
  for(x=0;x<150;++x) a[x]=x%3==0?2147483647:(x%3==1?(-2147483647-1):x*3+1);
  for(x=0;x<200;++x) b[x]=-777;
  for(r=0;r<2;++r) { i=start;
  for(;i<n;++i) { k=2*i+m-p;for(j=0;j<k;++j) { b[i*20+j]=a[i*15+j]; } }
  }
  emit("layout_context","a",a,150,i,j,k,m,p);emit("layout_context","b",b,200,i,j,k,m,p);
}
void layout_same_extent(int start,int n,int m,int p) {
  int a[240],b[240];int i=start,j=99,k=55,x,r;
  for(x=0;x<240;++x) a[x]=x%3==0?2147483647:(x%3==1?(-2147483647-1):x*3+1);
  for(x=0;x<240;++x) b[x]=-777;
  for(;i<n;++i) { k=2*i+m-p;for(j=0;j<k;++j) { b[i*20+j]=a[i*24+j]; } }
  emit("layout_same_extent","a",a,240,i,j,k,m,p);emit("layout_same_extent","b",b,240,i,j,k,m,p);
}
void layout_nonlinear(int start,int n,int m,int p) {
  int a[220],b[170];int i=start,j=99,k=55,x,r;
  for(x=0;x<220;++x) a[x]=x%3==0?2147483647:(x%3==1?(-2147483647-1):x*3+1);
  for(x=0;x<170;++x) b[x]=-777;
  for(;i<n;++i) { k=i*i+m-p;for(j=0;j<k;++j) { b[i*17+j]=a[i*22+j]; } }
  emit("layout_nonlinear","a",a,220,i,j,k,m,p);emit("layout_nonlinear","b",b,170,i,j,k,m,p);
}
void layout_neighbor(int start,int n,int m,int p) {
  int a[220],b[170];int i=start,j=99,k=55,x,r;
  for(x=0;x<220;++x) a[x]=x%3==0?2147483647:(x%3==1?(-2147483647-1):x*3+1);
  for(x=0;x<170;++x) b[x]=-777;
  for(;i<n;++i) { k=2*i+m-p;for(j=0;j<k;++j) { b[i*17+j]=a[i*22+j+1]; } }
  emit("layout_neighbor","a",a,220,i,j,k,m,p);emit("layout_neighbor","b",b,170,i,j,k,m,p);
}
void layout_alias(int start,int n,int m,int p) {
  int a[240],b[240];int i=start,j=99,k=55,x,r;
  for(x=0;x<240;++x) a[x]=x%3==0?2147483647:(x%3==1?(-2147483647-1):x*3+1);
  for(x=0;x<240;++x) b[x]=-777;
  for(;i<n;++i) { k=2*i+m-p;for(j=0;j<k;++j) { b[i*20+j]=b[i*24+j]; } }
  emit("layout_alias","a",a,240,i,j,k,m,p);emit("layout_alias","b",b,240,i,j,k,m,p);
}
int main(void) { int n,m,p;for(n=0;n<=5;++n) for(m=-1;m<=6;++m) for(p=-2;p<=2;++p) {
  layout_growing(0,n,m,p);
  layout_descending(0,n,m,p);
  layout_constant(0,n,m,p);
  layout_global(0,n,m,p);
  layout_context(0,n,m,p);
  layout_same_extent(0,n,m,p);
  layout_nonlinear(0,n,m,p);
  layout_neighbor(0,n,m,p);
  layout_alias(0,n,m,p);
}
  layout_growing(2,4,5,1);layout_growing(0,-2,2147483647,(-2147483647-1));layout_growing(0,0,(-2147483647-1),2147483647);
  layout_descending(2,4,5,1);layout_descending(0,-2,2147483647,(-2147483647-1));layout_descending(0,0,(-2147483647-1),2147483647);
  layout_constant(2,4,5,1);layout_constant(0,-2,2147483647,(-2147483647-1));layout_constant(0,0,(-2147483647-1),2147483647);
  layout_global(2,4,5,1);layout_global(0,-2,2147483647,(-2147483647-1));layout_global(0,0,(-2147483647-1),2147483647);
  layout_context(2,4,5,1);layout_context(0,-2,2147483647,(-2147483647-1));layout_context(0,0,(-2147483647-1),2147483647);
  layout_same_extent(2,4,5,1);layout_same_extent(0,-2,2147483647,(-2147483647-1));layout_same_extent(0,0,(-2147483647-1),2147483647);
  layout_nonlinear(2,4,5,1);layout_nonlinear(0,-2,2147483647,(-2147483647-1));layout_nonlinear(0,0,(-2147483647-1),2147483647);
  layout_neighbor(2,4,5,1);layout_neighbor(0,-2,2147483647,(-2147483647-1));layout_neighbor(0,0,(-2147483647-1),2147483647);
  layout_alias(2,4,5,1);layout_alias(0,-2,2147483647,(-2147483647-1));layout_alias(0,0,(-2147483647-1),2147483647);
layout_growing(0,4,100,99);layout_context(0,4,100,99);return 0;}
