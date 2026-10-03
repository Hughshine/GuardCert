#include <stdio.h>

int offset_ga[480],offset_gb[500],offset_gc[600];

static void emit(const char *name,const char *suffix,int *a,int extent,int i,int j,int k,int m,int p) {
  int x; printf("%s-%s %d %d %d %d %d",name,suffix,i,j,k,m,p);
  for(x=0;x<extent;++x) printf(" %d",a[x]); putchar(10);
}

void offset_self_forward(int start,int n,int m,int p) {
  int a[480],b[500],c[600];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) a[x]=x*3+1;
  for(x=0;x<500;++x) b[x]=x*5+2;
  for(x=0;x<600;++x) c[x]=-777;
  
  for(;i<n;++i) { k=2*i+m-p;
    for(j=0;j<k;++j) { b[i*20+j]=b[i*20+j+1]; }
  }
  
  emit("offset_self_forward","a",a,480,i,j,k,m,p);
  emit("offset_self_forward","b",b,500,i,j,k,m,p);
  emit("offset_self_forward","c",c,600,i,j,k,m,p);
}

void offset_self_transpose(int start,int n,int m,int p) {
  int a[480],b[500],c[600];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) a[x]=x*3+1;
  for(x=0;x<500;++x) b[x]=x*5+2;
  for(x=0;x<600;++x) c[x]=-777;
  
  for(;i<n;++i) { k=2*i+m-p;
    for(j=0;j<k;++j) { b[i*20+j]=b[j*17+i+1]; }
  }
  
  emit("offset_self_transpose","a",a,480,i,j,k,m,p);
  emit("offset_self_transpose","b",b,500,i,j,k,m,p);
  emit("offset_self_transpose","c",c,600,i,j,k,m,p);
}

void offset_self_scatter(int start,int n,int m,int p) {
  int a[480],b[500],c[600];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) a[x]=x*3+1;
  for(x=0;x<500;++x) b[x]=x*5+2;
  for(x=0;x<600;++x) c[x]=-777;
  
  for(;i<n;++i) { k=2*i+m-p;
    for(j=0;j<k;++j) { b[j*19+i*2+1]=b[i*23+j]; }
  }
  
  emit("offset_self_scatter","a",a,480,i,j,k,m,p);
  emit("offset_self_scatter","b",b,500,i,j,k,m,p);
  emit("offset_self_scatter","c",c,600,i,j,k,m,p);
}

void offset_anchor_chain(int start,int n,int m,int p) {
  int a[480],b[500],c[600];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) a[x]=x*3+1;
  for(x=0;x<500;++x) b[x]=x*5+2;
  for(x=0;x<600;++x) c[x]=-777;
  
  for(;i<n;++i) { k=2*i+m-p;
    for(j=0;j<k;++j) { b[i*20+j]=a[j*17+i]; c[i*24+j+1]=b[i*20+j]; c[i*24+j]=c[i*24+j+1]; b[i*20+j]=b[i*20+j+1]; }
  }
  
  emit("offset_anchor_chain","a",a,480,i,j,k,m,p);
  emit("offset_anchor_chain","b",b,500,i,j,k,m,p);
  emit("offset_anchor_chain","c",c,600,i,j,k,m,p);
}

void offset_global_chain(int start,int n,int m,int p) {
  
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) offset_ga[x]=x*3+1;
  for(x=0;x<500;++x) offset_gb[x]=x*5+2;
  for(x=0;x<600;++x) offset_gc[x]=-777;
  
  for(;i<n;++i) { k=2*i+m-p;
    for(j=0;j<k;++j) { offset_gb[i*20+j]=offset_ga[j*17+i]; offset_gc[i*24+j+1]=offset_gb[i*20+j]; offset_gc[i*24+j]=offset_gc[i*24+j+1]; offset_gb[i*20+j]=offset_gb[i*20+j+1]; }
  }
  
  emit("offset_global_chain","a",offset_ga,480,i,j,k,m,p);
  emit("offset_global_chain","b",offset_gb,500,i,j,k,m,p);
  emit("offset_global_chain","c",offset_gc,600,i,j,k,m,p);
}

void offset_context(int start,int n,int m,int p) {
  int a[480],b[500],c[600];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) a[x]=x*3+1;
  for(x=0;x<500;++x) b[x]=x*5+2;
  for(x=0;x<600;++x) c[x]=-777;
  for(r=0;r<2;++r) { i=start;
  for(;i<n;++i) { k=2*i+m-p;
    for(j=0;j<k;++j) { b[i*20+j]=b[i*20+j+1]; }
  }
  }
  emit("offset_context","a",a,480,i,j,k,m,p);
  emit("offset_context","b",b,500,i,j,k,m,p);
  emit("offset_context","c",c,600,i,j,k,m,p);
}

void offset_readonly_unanchored(int start,int n,int m,int p) {
  int a[480],b[500],c[600];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) a[x]=x*3+1;
  for(x=0;x<500;++x) b[x]=x*5+2;
  for(x=0;x<600;++x) c[x]=-777;
  
  for(;i<n;++i) { k=2*i+m-p;
    for(j=0;j<k;++j) { b[i*20+j]=a[i*31+j+1]; }
  }
  
  emit("offset_readonly_unanchored","a",a,480,i,j,k,m,p);
  emit("offset_readonly_unanchored","b",b,500,i,j,k,m,p);
  emit("offset_readonly_unanchored","c",c,600,i,j,k,m,p);
}

void offset_unanchored(int start,int n,int m,int p) {
  int a[480],b[500],c[600];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) a[x]=x*3+1;
  for(x=0;x<500;++x) b[x]=x*5+2;
  for(x=0;x<600;++x) c[x]=-777;
  
  for(;i<n;++i) { k=2*i+m-p;
    for(j=0;j<k;++j) { b[i*20+j+1]=a[i*31+j+1]; }
  }
  
  emit("offset_unanchored","a",a,480,i,j,k,m,p);
  emit("offset_unanchored","b",b,500,i,j,k,m,p);
  emit("offset_unanchored","c",c,600,i,j,k,m,p);
}

void offset_negative(int start,int n,int m,int p) {
  int a[480],b[500],c[600];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) a[x]=x*3+1;
  for(x=0;x<500;++x) b[x]=x*5+2;
  for(x=0;x<600;++x) c[x]=-777;
  
  for(;i<n;++i) { k=2*i+m-p;
    for(j=0;j<k;++j) { b[i*20+j]=b[i*20+j-1]; }
  }
  
  emit("offset_negative","a",a,480,i,j,k,m,p);
  emit("offset_negative","b",b,500,i,j,k,m,p);
  emit("offset_negative","c",c,600,i,j,k,m,p);
}

void offset_nonlinear(int start,int n,int m,int p) {
  int a[480],b[500],c[600];
  int i=start,j=99,k=55,x,r;
  for(x=0;x<480;++x) a[x]=x*3+1;
  for(x=0;x<500;++x) b[x]=x*5+2;
  for(x=0;x<600;++x) c[x]=-777;
  
  for(;i<n;++i) { k=2*i+m-p;
    for(j=0;j<k;++j) { b[i*20+j]=a[i*j]; }
  }
  
  emit("offset_nonlinear","a",a,480,i,j,k,m,p);
  emit("offset_nonlinear","b",b,500,i,j,k,m,p);
  emit("offset_nonlinear","c",c,600,i,j,k,m,p);
}

int main(void) { int n,m,p;
 for(n=0;n<6;++n) for(m=-1;m<6;++m) for(p=-1;p<2;++p) {

 offset_self_forward(0,n,m,p);

 offset_self_transpose(0,n,m,p);

 offset_self_scatter(0,n,m,p);

 offset_anchor_chain(0,n,m,p);

 offset_global_chain(0,n,m,p);

 offset_context(0,n,m,p);

 offset_readonly_unanchored(0,n,m,p);

 offset_unanchored(0,n,m,p);

 if(m<=p || n==0) offset_negative(0,n,m,p);

 offset_nonlinear(0,n,m,p);

 }

 offset_self_forward(2,4,5,1);

 offset_self_forward(0,0,-2147483647-1,2147483647); offset_self_forward(0,-2,2147483647,-2147483647-1);

 offset_self_transpose(2,4,5,1);

 offset_self_transpose(0,0,-2147483647-1,2147483647); offset_self_transpose(0,-2,2147483647,-2147483647-1);

 offset_self_scatter(2,4,5,1);

 offset_self_scatter(0,0,-2147483647-1,2147483647); offset_self_scatter(0,-2,2147483647,-2147483647-1);

 offset_anchor_chain(2,4,5,1);

 offset_anchor_chain(0,0,-2147483647-1,2147483647); offset_anchor_chain(0,-2,2147483647,-2147483647-1);

 offset_global_chain(2,4,5,1);

 offset_global_chain(0,0,-2147483647-1,2147483647); offset_global_chain(0,-2,2147483647,-2147483647-1);

 offset_context(2,4,5,1);

 offset_context(0,0,-2147483647-1,2147483647); offset_context(0,-2,2147483647,-2147483647-1);

 offset_readonly_unanchored(2,4,5,1);

 offset_readonly_unanchored(0,0,-2147483647-1,2147483647); offset_readonly_unanchored(0,-2,2147483647,-2147483647-1);

 offset_unanchored(2,4,5,1);

 offset_unanchored(0,0,-2147483647-1,2147483647); offset_unanchored(0,-2,2147483647,-2147483647-1);

 offset_negative(2,4,-1,1);

 offset_negative(0,0,-2147483647-1,2147483647); offset_negative(0,-2,2147483647,-2147483647-1);

 offset_nonlinear(2,4,5,1);

 offset_nonlinear(0,0,-2147483647-1,2147483647); offset_nonlinear(0,-2,2147483647,-2147483647-1);

 offset_self_transpose(0,6,6,0); offset_context(0,4,100,99); return 0; }
