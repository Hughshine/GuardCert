#include <stdio.h>

int compute_ga[480],compute_gb[500],compute_gc[600];

static void emit(const char *name,const char *suffix,int *a,int extent,int i,int j,int k,int m,int p) {
  int x; printf("%s-%s %d %d %d %d %d",name,suffix,i,j,k,m,p);
  for(x=0;x<extent;++x) printf(" %d",a[x]); putchar(10);
}

void compute_sum(int start,int n,int m,int p) {
  int a[480],b[500],c[600];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) a[x]=x*3+1;
  for(x=0;x<500;++x) b[x]=x*5+2;
  for(x=0;x<600;++x) c[x]=-777;
  
  for(;i<n;++i) { k=2*i+m-p;
    for(j=0;j<k;++j) { c[i*24+j]=a[j*17+i]+b[i*20+j]; }
  }
  
  emit("compute_sum","a",a,480,i,j,k,m,p);
  emit("compute_sum","b",b,500,i,j,k,m,p);
  emit("compute_sum","c",c,600,i,j,k,m,p);
}

void compute_product(int start,int n,int m,int p) {
  int a[480],b[500],c[600];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) a[x]=x*3+1;
  for(x=0;x<500;++x) b[x]=x*5+2;
  for(x=0;x<600;++x) c[x]=-777;
  
  for(;i<n;++i) { k=2*i+m-p;
    for(j=0;j<k;++j) { c[i*24+j]=a[j*17+i]*b[i*20+j]+i*j; }
  }
  
  emit("compute_product","a",a,480,i,j,k,m,p);
  emit("compute_product","b",b,500,i,j,k,m,p);
  emit("compute_product","c",c,600,i,j,k,m,p);
}

void compute_stencil(int start,int n,int m,int p) {
  int a[480],b[500],c[600];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) a[x]=x*3+1;
  for(x=0;x<500;++x) b[x]=x*5+2;
  for(x=0;x<600;++x) c[x]=-777;
  
  for(;i<n;++i) { k=2*i+m-p;
    for(j=0;j<k;++j) { b[i*20+j]=b[i*20+j]+b[i*20+j+1]; }
  }
  
  emit("compute_stencil","a",a,480,i,j,k,m,p);
  emit("compute_stencil","b",b,500,i,j,k,m,p);
  emit("compute_stencil","c",c,600,i,j,k,m,p);
}

void compute_alias_two(int start,int n,int m,int p) {
  int a[480],b[500],c[600];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) a[x]=x*3+1;
  for(x=0;x<500;++x) b[x]=x*5+2;
  for(x=0;x<600;++x) c[x]=-777;
  
  for(;i<n;++i) { k=2*i+m-p;
    for(j=0;j<k;++j) { b[i*20+j]=b[j*17+i]+b[i*31+j*2]; }
  }
  
  emit("compute_alias_two","a",a,480,i,j,k,m,p);
  emit("compute_alias_two","b",b,500,i,j,k,m,p);
  emit("compute_alias_two","c",c,600,i,j,k,m,p);
}

void compute_chain(int start,int n,int m,int p) {
  int a[480],b[500],c[600];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) a[x]=x*3+1;
  for(x=0;x<500;++x) b[x]=x*5+2;
  for(x=0;x<600;++x) c[x]=-777;
  
  for(;i<n;++i) { k=2*i+m-p;
    for(j=0;j<k;++j) { b[i*20+j]=a[j*17+i]+c[i*24+j]; c[i*24+j]=b[i*20+j]-a[j*17+i]; b[i*20+j]=b[i*20+j]*2+i-j; }
  }
  
  emit("compute_chain","a",a,480,i,j,k,m,p);
  emit("compute_chain","b",b,500,i,j,k,m,p);
  emit("compute_chain","c",c,600,i,j,k,m,p);
}

void compute_global(int start,int n,int m,int p) {
  
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) compute_ga[x]=x*3+1;
  for(x=0;x<500;++x) compute_gb[x]=x*5+2;
  for(x=0;x<600;++x) compute_gc[x]=-777;
  
  for(;i<n;++i) { k=2*i+m-p;
    for(j=0;j<k;++j) { compute_gc[i*24+j]=compute_ga[j*17+i]*compute_gb[i*20+j]+i*j; }
  }
  
  emit("compute_global","a",compute_ga,480,i,j,k,m,p);
  emit("compute_global","b",compute_gb,500,i,j,k,m,p);
  emit("compute_global","c",compute_gc,600,i,j,k,m,p);
}

void compute_context(int start,int n,int m,int p) {
  int a[480],b[500],c[600];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) a[x]=x*3+1;
  for(x=0;x<500;++x) b[x]=x*5+2;
  for(x=0;x<600;++x) c[x]=-777;
  for(r=0;r<2;++r) { i=start;
  for(;i<n;++i) { k=2*i+m-p;
    for(j=0;j<k;++j) { b[i*20+j]=a[j*17+i]+c[i*24+j]; c[i*24+j]=b[i*20+j]-a[j*17+i]; b[i*20+j]=b[i*20+j]*2+i-j; }
  }
  }
  emit("compute_context","a",a,480,i,j,k,m,p);
  emit("compute_context","b",b,500,i,j,k,m,p);
  emit("compute_context","c",c,600,i,j,k,m,p);
}

void compute_overflow(int start,int n,int m,int p) {
  int a[480],b[500],c[600];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) a[x]=2147483647-x;
  for(x=0;x<500;++x) b[x]=2147483647-x*2;
  for(x=0;x<600;++x) c[x]=-777;
  
  for(;i<n;++i) { k=2*i+m-p;
    for(j=0;j<k;++j) { c[i*24+j]=a[j*17+i]*b[i*20+j]+i*j; }
  }
  
  emit("compute_overflow","a",a,480,i,j,k,m,p);
  emit("compute_overflow","b",b,500,i,j,k,m,p);
  emit("compute_overflow","c",c,600,i,j,k,m,p);
}

void compute_nonlinear_index(int start,int n,int m,int p) {
  int a[480],b[500],c[600];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) a[x]=x*3+1;
  for(x=0;x<500;++x) b[x]=x*5+2;
  for(x=0;x<600;++x) c[x]=-777;
  
  for(;i<n;++i) { k=2*i+m-p;
    for(j=0;j<k;++j) { c[i*24+j]=a[i*j]+b[i*20+j]; }
  }
  
  emit("compute_nonlinear_index","a",a,480,i,j,k,m,p);
  emit("compute_nonlinear_index","b",b,500,i,j,k,m,p);
  emit("compute_nonlinear_index","c",c,600,i,j,k,m,p);
}

void compute_unanchored(int start,int n,int m,int p) {
  int a[480],b[500],c[600];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) a[x]=x*3+1;
  for(x=0;x<500;++x) b[x]=x*5+2;
  for(x=0;x<600;++x) c[x]=-777;
  
  for(;i<n;++i) { k=2*i+m-p;
    for(j=0;j<k;++j) { c[i*24+j]=a[j*17+i+1]+b[i*20+j]; }
  }
  
  emit("compute_unanchored","a",a,480,i,j,k,m,p);
  emit("compute_unanchored","b",b,500,i,j,k,m,p);
  emit("compute_unanchored","c",c,600,i,j,k,m,p);
}

void compute_changed_parameter(int start,int n,int m,int p) {
  int a[480],b[500],c[600];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) a[x]=x*3+1;
  for(x=0;x<500;++x) b[x]=x*5+2;
  for(x=0;x<600;++x) c[x]=-777;
  
  for(;i<n;++i) { k=2*i+m-p;
    for(j=0;j<k;++j) { c[i*24+j]=a[j*17+i]+b[i*20+j]+m; }
  }
  
  emit("compute_changed_parameter","a",a,480,i,j,k,m,p);
  emit("compute_changed_parameter","b",b,500,i,j,k,m,p);
  emit("compute_changed_parameter","c",c,600,i,j,k,m,p);
}

int main(void) { int n,m,p;
 for(n=0;n<6;++n) for(m=-1;m<6;++m) for(p=-1;p<2;++p) {

 compute_sum(0,n,m,p);

 compute_product(0,n,m,p);

 compute_stencil(0,n,m,p);

 compute_alias_two(0,n,m,p);

 compute_chain(0,n,m,p);

 compute_global(0,n,m,p);

 compute_context(0,n,m,p);

 compute_overflow(0,n,m,p);

 compute_nonlinear_index(0,n,m,p);

 compute_unanchored(0,n,m,p);

 compute_changed_parameter(0,n,m,p);

 }

 compute_sum(2,4,5,1); compute_sum(0,0,-2147483647-1,2147483647); compute_sum(0,-2,2147483647,-2147483647-1);

 compute_product(2,4,5,1); compute_product(0,0,-2147483647-1,2147483647); compute_product(0,-2,2147483647,-2147483647-1);

 compute_stencil(2,4,5,1); compute_stencil(0,0,-2147483647-1,2147483647); compute_stencil(0,-2,2147483647,-2147483647-1);

 compute_alias_two(2,4,5,1); compute_alias_two(0,0,-2147483647-1,2147483647); compute_alias_two(0,-2,2147483647,-2147483647-1);

 compute_chain(2,4,5,1); compute_chain(0,0,-2147483647-1,2147483647); compute_chain(0,-2,2147483647,-2147483647-1);

 compute_global(2,4,5,1); compute_global(0,0,-2147483647-1,2147483647); compute_global(0,-2,2147483647,-2147483647-1);

 compute_context(2,4,5,1); compute_context(0,0,-2147483647-1,2147483647); compute_context(0,-2,2147483647,-2147483647-1);

 compute_overflow(2,4,5,1); compute_overflow(0,0,-2147483647-1,2147483647); compute_overflow(0,-2,2147483647,-2147483647-1);

 compute_nonlinear_index(2,4,5,1); compute_nonlinear_index(0,0,-2147483647-1,2147483647); compute_nonlinear_index(0,-2,2147483647,-2147483647-1);

 compute_unanchored(2,4,5,1); compute_unanchored(0,0,-2147483647-1,2147483647); compute_unanchored(0,-2,2147483647,-2147483647-1);

 compute_changed_parameter(2,4,5,1); compute_changed_parameter(0,0,-2147483647-1,2147483647); compute_changed_parameter(0,-2,2147483647,-2147483647-1);

 compute_alias_two(0,6,6,0); compute_context(0,4,100,99); return 0; }
