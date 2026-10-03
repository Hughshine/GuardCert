#include <stdio.h>

int offset_ga[480],offset_gb[500],offset_gc[600];

static void emit(const char *name,const char *suffix,int *a,int extent,int i,int j,int k,int m,int p) {
  int x; printf("%s-%s %d %d %d %d %d",name,suffix,i,j,k,m,p);
  for(x=0;x<extent;++x) printf(" %d",a[x]); putchar(10);
}

void width_chain(int start,int n,int m,int p) {
  int a[480],b[500],c[600];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) a[x]=x*3+1;
  for(x=0;x<500;++x) b[x]=x*5+2;
  for(x=0;x<600;++x) c[x]=-777;
  
  for(;i<n;++i) { k=m-p;
    for(j=0;j<k;++j) { b[i*20+j]=a[j*17+i]; c[i*24+j+1]=b[i*20+j]; c[i*24+j]=c[i*24+j+1]; b[i*20+j]=b[i*20+j+1]; }
  }
  
  emit("width_chain","a",a,480,i,j,k,m,p);
  emit("width_chain","b",b,500,i,j,k,m,p);
  emit("width_chain","c",c,600,i,j,k,m,p);
}

void width_context(int start,int n,int m,int p) {
  int a[480],b[500],c[600];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) a[x]=x*3+1;
  for(x=0;x<500;++x) b[x]=x*5+2;
  for(x=0;x<600;++x) c[x]=-777;
  
  for(r=0;r<2;++r) { i=start;
  for(;i<n;++i) { k=m-p;
    for(j=0;j<k;++j) { b[i*20+j]=a[j*17+i]; c[i*24+j+1]=b[i*20+j]; c[i*24+j]=c[i*24+j+1]; b[i*20+j]=b[i*20+j+1]; }
  }
  
  }
  emit("width_context","a",a,480,i,j,k,m,p);
  emit("width_context","b",b,500,i,j,k,m,p);
  emit("width_context","c",c,600,i,j,k,m,p);
}

int main(void) {
  int n,m,p;
  for(n=0;n<6;++n) for(m=-1;m<6;++m) for(p=-1;p<2;++p) {
    width_chain(0,n,m,p); width_context(0,n,m,p);
  }
  width_chain(0,4,1,0); width_chain(0,1,2,0);
  width_chain(2,4,5,1); width_context(2,4,5,1);
  width_chain(0,0,-2147483647-1,2147483647);
  width_context(0,-2,2147483647,-2147483647-1);
  return 0;
}
