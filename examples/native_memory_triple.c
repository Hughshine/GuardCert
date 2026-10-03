#include <stdio.h>

int triple_ga[480],triple_gb[500],triple_gc[600];

static void seed(int *a,int *b,int *c,int overflow) {
  int x;
  for(x=0;x<480;++x) a[x]=overflow ? 2147483647-x : 3*x+1;
  for(x=0;x<500;++x) b[x]=overflow ? 2147483647-2*x : 5*x+2;
  for(x=0;x<600;++x) c[x]=overflow ? 2147483647-3*x : -777;
}
static void emit(const char *name,int *a,int *b,int *c,int i,int j,int k,int n,int m,int l) {
  int x;
  printf("%s-a %d %d %d %d %d %d",name,i,j,k,n,m,l);
  for(x=0;x<480;++x) printf(" %d",a[x]); putchar(10);
  printf("%s-b %d %d %d %d %d %d",name,i,j,k,n,m,l);
  for(x=0;x<500;++x) printf(" %d",b[x]); putchar(10);
  printf("%s-c %d %d %d %d %d %d",name,i,j,k,n,m,l);
  for(x=0;x<600;++x) printf(" %d",c[x]); putchar(10);
}

void triple_matmul(int start,int n,int m,int l) {
  int a[480],b[500],c[600],i=start,j=99,k=55;
  seed(a,b,c,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<l;++k) { c[i*24+j]=c[i*24+j]+a[i*22+k]*b[k*17+j]; }
    }
  }
  emit("triple_matmul",a,b,c,i,j,k,n,m,l);
}
void triple_global(int start,int n,int m,int l) {
  int i=start,j=99,k=55;
  seed(triple_ga,triple_gb,triple_gc,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<l;++k) { triple_gc[i*24+j]=triple_gc[i*24+j]+triple_ga[i*22+k]*triple_gb[k*17+j]; }
    }
  }
  emit("triple_global",triple_ga,triple_gb,triple_gc,i,j,k,n,m,l);
}
void triple_context(int start,int n,int m,int l) {
  int a[480],b[500],c[600],i=start,j=99,k=55,r;
  seed(a,b,c,0);
  for(r=0;r<2;++r) {
    i=start;
    for(;i<n;++i) {
      for(j=0;j<m;++j) {
        for(k=0;k<l;++k) { c[i*24+j]=c[i*24+j]+a[i*22+k]*b[k*17+j]; }
      }
    }
  }
  emit("triple_context",a,b,c,i,j,k,n,m,l);
}
void triple_wrap(int start,int n,int m,int l) {
  int a[480],b[500],c[600],i=start,j=99,k=55;
  seed(a,b,c,1);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<l;++k) { c[i*24+j]=c[i*24+j]+a[i*22+k]*b[k*17+j]; }
    }
  }
  emit("triple_wrap",a,b,c,i,j,k,n,m,l);
}
void triple_independent(int start,int n,int m,int l) {
  int a[480],b[500],c[600],i=start,j=99,k=55;
  seed(a,b,c,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<l;++k) { c[i*70+j*8+k]=a[i*22+k]+b[j*20+k]+i*j+k; }
    }
  }
  emit("triple_independent",a,b,c,i,j,k,n,m,l);
}
void triple_chain(int start,int n,int m,int l) {
  int a[480],b[500],c[600],i=start,j=99,k=55;
  seed(a,b,c,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<l;++k) {
        b[i*70+j*8+k]=a[i*22+k]+i*j;
        c[i*70+j*8+k]=b[i*70+j*8+k]+b[i*70+j*8+k+1];
        b[i*70+j*8+k]=c[i*70+j*8+k];
      }
    }
  }
  emit("triple_chain",a,b,c,i,j,k,n,m,l);
}
void triple_recurrence(int start,int n,int m,int l) {
  int a[480],b[500],c[600],i=start,j=99,k=55;
  seed(a,b,c,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<l;++k) { b[i*22+j+k]=b[i*22+j+k]+b[i*22+j+k+1]; }
    }
  }
  emit("triple_recurrence",a,b,c,i,j,k,n,m,l);
}
void triple_nonlinear(int start,int n,int m,int l) {
  int a[480],b[500],c[600],i=start,j=99,k=55;
  seed(a,b,c,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<l;++k) { c[i*70+j*8+k]=a[i*j+k]+b[j*20+k]; }
    }
  }
  emit("triple_nonlinear",a,b,c,i,j,k,n,m,l);
}
void triple_unanchored(int start,int n,int m,int l) {
  int a[480],b[500],c[600],i=start,j=99,k=55;
  seed(a,b,c,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<l;++k) { c[i*70+j*8+k]=a[i*22+k+1]+b[j*20+k]; }
    }
  }
  emit("triple_unanchored",a,b,c,i,j,k,n,m,l);
}

void triple_uninitialized_outer(int start,int n,int ignored_m,int ignored_l) {
  int a[480],b[500],c[600],i=start,j=99,k=55,m,l;
  seed(a,b,c,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<l;++k) { c[i*24+j]=c[i*24+j]+a[i*22+k]*b[k*17+j]; }
    }
  }
  m=7; l=9;
  emit("triple_uninitialized_outer",a,b,c,i,j,k,n,m,l);
}
void triple_uninitialized_middle(int start,int n,int m,int ignored_l) {
  int a[480],b[500],c[600],i=start,j=99,k=55,l;
  seed(a,b,c,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<l;++k) { c[i*24+j]=c[i*24+j]+a[i*22+k]*b[k*17+j]; }
    }
  }
  l=9;
  emit("triple_uninitialized_middle",a,b,c,i,j,k,n,m,l);
}

static void run_all(int start,int n,int m,int l) {
  triple_matmul(start,n,m,l); triple_global(start,n,m,l); triple_context(start,n,m,l);
  triple_wrap(start,n,m,l); triple_independent(start,n,m,l); triple_chain(start,n,m,l);
  triple_recurrence(start,n,m,l); triple_nonlinear(start,n,m,l); triple_unanchored(start,n,m,l);
}
int main(void) {
  int n,m,l;
  for(n=0;n<4;++n) for(m=-1;m<4;++m) for(l=-1;l<4;++l) run_all(0,n,m,l);
  run_all(2,4,3,2); run_all(0,0,-2147483648,2147483647); run_all(0,2,0,-2147483648);
  triple_matmul(0,20,20,20); triple_wrap(0,20,20,20);
  triple_independent(0,8,8,8); triple_chain(0,7,7,7);
  triple_matmul(0,1,1,21); triple_matmul(0,21,1,1); triple_matmul(0,1,21,1);
  triple_uninitialized_outer(0,0,0,0); triple_uninitialized_outer(2,1,0,0);
  triple_uninitialized_middle(0,2,0,0);
  return 0;
}
