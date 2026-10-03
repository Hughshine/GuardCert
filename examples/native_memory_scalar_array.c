#include <stdio.h>
#define ARRAY_SIZE 256
int scalar_global_a[ARRAY_SIZE],scalar_global_b[ARRAY_SIZE],scalar_global_c[ARRAY_SIZE];
static void seed(int *a,int *b,int *c,int wrap) {
  int x;
  for(x=0;x<ARRAY_SIZE;++x) {
    a[x]=wrap ? 2147483647-x : 3*x+1;
    b[x]=wrap ? 2147483647-2*x : 5*x+2;
    c[x]=wrap ? 2147483647-3*x : -777;
  }
}
static void emit(const char *name,int *a,int *b,int *c,int *exits,int *counts,int depth,int alpha,int beta,int gamma) {
  int x,which;
  for(which=0;which<3;++which) {
    int *values=which==0 ? a : which==1 ? b : c;
    printf("%s-%c",name,'a'+which);
    for(x=0;x<depth;++x) printf(" %d",exits[x]);
    for(x=0;x<depth;++x) printf(" %d",counts[x]);
    printf(" %d %d %d",alpha,beta,gamma);
    for(x=0;x<ARRAY_SIZE;++x) printf(" %d",values[x]);
    putchar(10);
  }
}
void array_scalar_axpy(int start,int n,int m,int alpha,int beta,int gamma) {
  int a[ARRAY_SIZE],b[ARRAY_SIZE],c[ARRAY_SIZE];
  int i=start,j=77;
  int exits[2],counts[2];
  seed(a,b,c,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      c[i*8+j]=a[i*8+j]*alpha+b[i*8+j]*beta+i*j+7;
    }
  }
  exits[0]=i;counts[0]=n;
  exits[1]=j;counts[1]=m;
  emit("array_scalar_axpy",a,b,c,exits,counts,2,alpha,beta,gamma);
}
void array_scalar_global(int start,int n,int m,int alpha,int beta,int gamma) {
  int i=start,j=77;
  int exits[2],counts[2];
  seed(scalar_global_a,scalar_global_b,scalar_global_c,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      scalar_global_c[i*8+j]=scalar_global_a[i*8+j]*alpha+scalar_global_b[i*8+j]*beta+i*j+7;
    }
  }
  exits[0]=i;counts[0]=n;
  exits[1]=j;counts[1]=m;
  emit("array_scalar_global",scalar_global_a,scalar_global_b,scalar_global_c,exits,counts,2,alpha,beta,gamma);
}
void array_scalar_context(int start,int n,int m,int alpha,int beta,int gamma) {
  int a[ARRAY_SIZE],b[ARRAY_SIZE],c[ARRAY_SIZE];
  int i=start,j=77;
  int exits[2],counts[2];
  seed(a,b,c,0);
  int repeat;
  for(repeat=0;repeat<2;++repeat) {
    i=start;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      c[i*8+j]=a[i*8+j]*alpha+b[i*8+j]*beta+i*j+7;
    }
  }
  }
  exits[0]=i;counts[0]=n;
  exits[1]=j;counts[1]=m;
  emit("array_scalar_context",a,b,c,exits,counts,2,alpha,beta,gamma);
}
void array_scalar_wrap(int start,int n,int m,int alpha,int beta,int gamma) {
  int a[ARRAY_SIZE],b[ARRAY_SIZE],c[ARRAY_SIZE];
  int i=start,j=77;
  int exits[2],counts[2];
  seed(a,b,c,1);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      c[i*8+j]=a[i*8+j]*alpha+b[i*8+j]*beta+i*j+7;
    }
  }
  exits[0]=i;counts[0]=n;
  exits[1]=j;counts[1]=m;
  emit("array_scalar_wrap",a,b,c,exits,counts,2,alpha,beta,gamma);
}
void array_scalar_chain(int start,int n,int m,int alpha,int beta,int gamma) {
  int a[ARRAY_SIZE],b[ARRAY_SIZE],c[ARRAY_SIZE];
  int i=start,j=77;
  int exits[2],counts[2];
  seed(a,b,c,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      b[i*8+j]=a[i*8+j]*alpha+beta+i*j+7;
      c[i*8+j]=b[i*8+j]+b[i*8+j+1]*alpha;
      b[i*8+j]=c[i*8+j]-beta;
    }
  }
  exits[0]=i;counts[0]=n;
  exits[1]=j;counts[1]=m;
  emit("array_scalar_chain",a,b,c,exits,counts,2,alpha,beta,gamma);
}
void array_scalar_recurrence(int start,int n,int m,int alpha,int beta,int gamma) {
  int a[ARRAY_SIZE],b[ARRAY_SIZE],c[ARRAY_SIZE];
  int i=start,j=77;
  int exits[2],counts[2];
  seed(a,b,c,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      b[i*8+j]=b[i*8+j]+b[i*8+j+1]*alpha+beta;
    }
  }
  exits[0]=i;counts[0]=n;
  exits[1]=j;counts[1]=m;
  emit("array_scalar_recurrence",a,b,c,exits,counts,2,alpha,beta,gamma);
}
void array_scalar_bound(int start,int n,int m,int alpha,int beta,int gamma) {
  int a[ARRAY_SIZE],b[ARRAY_SIZE],c[ARRAY_SIZE];
  int i=start,j=77;
  int exits[2],counts[2];
  seed(a,b,c,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      c[i*8+j]=a[i*8+j]*n+b[i*8+j]*m+i*j+7;
    }
  }
  exits[0]=i;counts[0]=n;
  exits[1]=j;counts[1]=m;
  emit("array_scalar_bound",a,b,c,exits,counts,2,alpha,beta,gamma);
}
void array_scalar_many(int start,int n,int m,int alpha,int beta,int gamma) {
  int a[ARRAY_SIZE],b[ARRAY_SIZE],c[ARRAY_SIZE];
  int i=start,j=77;
  int exits[2],counts[2];
  seed(a,b,c,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      c[i*8+j]=a[i*8+j]*alpha+b[i*8+j]*beta*gamma+i*j+7;
    }
  }
  exits[0]=i;counts[0]=n;
  exits[1]=j;counts[1]=m;
  emit("array_scalar_many",a,b,c,exits,counts,2,alpha,beta,gamma);
}
void array_scalar_undef(int start,int n,int m,int alpha,int beta,int gamma) {
  int a[ARRAY_SIZE],b[ARRAY_SIZE],c[ARRAY_SIZE];
  int i=start,j=77;
  int exits[2],counts[2];
  int unused_alpha;
  seed(a,b,c,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      c[i*8+j]=a[i*8+j]*unused_alpha+b[i*8+j]*beta+i*j+7;
    }
  }
  exits[0]=i;counts[0]=n;
  exits[1]=j;counts[1]=m;
  emit("array_scalar_undef",a,b,c,exits,counts,2,alpha,beta,gamma);
}
void array_scalar_nonlinear(int start,int n,int m,int alpha,int beta,int gamma) {
  int a[ARRAY_SIZE],b[ARRAY_SIZE],c[ARRAY_SIZE];
  int i=start,j=77;
  int exits[2],counts[2];
  seed(a,b,c,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      c[i*8+j]=a[i*j]*alpha+b[i*8+j]*beta+i*j+7;
    }
  }
  exits[0]=i;counts[0]=n;
  exits[1]=j;counts[1]=m;
  emit("array_scalar_nonlinear",a,b,c,exits,counts,2,alpha,beta,gamma);
}
void array_scalar_mutated(int start,int n,int m,int alpha,int beta,int gamma) {
  int a[ARRAY_SIZE],b[ARRAY_SIZE],c[ARRAY_SIZE];
  int i=start,j=77;
  int exits[2],counts[2];
  seed(a,b,c,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      alpha=alpha+1;
      c[i*8+j]=a[i*8+j]*alpha+b[i*8+j]*beta+i*j+7;
    }
  }
  exits[0]=i;counts[0]=n;
  exits[1]=j;counts[1]=m;
  emit("array_scalar_mutated",a,b,c,exits,counts,2,alpha,beta,gamma);
}
void array_scalar_three(int start,int n,int m,int p,int alpha,int beta,int gamma) {
  int a[ARRAY_SIZE],b[ARRAY_SIZE],c[ARRAY_SIZE];
  int i=start,j=77,k=55;
  int exits[3],counts[3];
  seed(a,b,c,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<p;++k) {
        c[i*64+j*8+k]=a[i*64+j*8+k]*alpha+b[i*64+j*8+k]*beta+i*k+j+9;
      }
    }
  }
  exits[0]=i;counts[0]=n;
  exits[1]=j;counts[1]=m;
  exits[2]=k;counts[2]=p;
  emit("array_scalar_three",a,b,c,exits,counts,3,alpha,beta,gamma);
}
void array_scalar_four(int start,int n,int m,int p,int q,int alpha,int beta,int gamma) {
  int a[ARRAY_SIZE],b[ARRAY_SIZE],c[ARRAY_SIZE];
  int i=start,j=77,k=55,t=33;
  int exits[4],counts[4];
  seed(a,b,c,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<p;++k) {
        for(t=0;t<q;++t) {
          c[i*64+j*16+k*4+t]=a[i*64+j*16+k*4+t]*alpha+b[i*64+j*16+k*4+t]*beta+i*j+k*t+11;
        }
      }
    }
  }
  exits[0]=i;counts[0]=n;
  exits[1]=j;counts[1]=m;
  exits[2]=k;counts[2]=p;
  exits[3]=t;counts[3]=q;
  emit("array_scalar_four",a,b,c,exits,counts,4,alpha,beta,gamma);
}
int main(void) {
  array_scalar_axpy(0,1,1,19,-7,3);
  array_scalar_axpy(0,1,1,-2147483648,2147483647,-1);
  array_scalar_axpy(0,1,1,2147483647,-2147483648,2147483647);
  array_scalar_axpy(0,1,1,0,0,0);
  array_scalar_axpy(0,2,2,19,-7,3);
  array_scalar_axpy(0,2,2,-2147483648,2147483647,-1);
  array_scalar_axpy(0,2,2,2147483647,-2147483648,2147483647);
  array_scalar_axpy(0,2,2,0,0,0);
  array_scalar_axpy(0,0,-2147483648,19,-7,3);
  array_scalar_axpy(0,0,-2147483648,-2147483648,2147483647,-1);
  array_scalar_axpy(0,0,-2147483648,2147483647,-2147483648,2147483647);
  array_scalar_axpy(0,0,-2147483648,0,0,0);
  array_scalar_axpy(0,2,0,19,-7,3);
  array_scalar_axpy(0,2,0,-2147483648,2147483647,-1);
  array_scalar_axpy(0,2,0,2147483647,-2147483648,2147483647);
  array_scalar_axpy(0,2,0,0,0,0);
  array_scalar_axpy(1,2,2,19,-7,3);
  array_scalar_global(0,1,1,19,-7,3);
  array_scalar_global(0,1,1,-2147483648,2147483647,-1);
  array_scalar_global(0,1,1,2147483647,-2147483648,2147483647);
  array_scalar_global(0,1,1,0,0,0);
  array_scalar_global(0,2,2,19,-7,3);
  array_scalar_global(0,2,2,-2147483648,2147483647,-1);
  array_scalar_global(0,2,2,2147483647,-2147483648,2147483647);
  array_scalar_global(0,2,2,0,0,0);
  array_scalar_global(0,0,-2147483648,19,-7,3);
  array_scalar_global(0,0,-2147483648,-2147483648,2147483647,-1);
  array_scalar_global(0,0,-2147483648,2147483647,-2147483648,2147483647);
  array_scalar_global(0,0,-2147483648,0,0,0);
  array_scalar_global(0,2,0,19,-7,3);
  array_scalar_global(0,2,0,-2147483648,2147483647,-1);
  array_scalar_global(0,2,0,2147483647,-2147483648,2147483647);
  array_scalar_global(0,2,0,0,0,0);
  array_scalar_global(1,2,2,19,-7,3);
  array_scalar_context(0,1,1,19,-7,3);
  array_scalar_context(0,1,1,-2147483648,2147483647,-1);
  array_scalar_context(0,1,1,2147483647,-2147483648,2147483647);
  array_scalar_context(0,1,1,0,0,0);
  array_scalar_context(0,2,2,19,-7,3);
  array_scalar_context(0,2,2,-2147483648,2147483647,-1);
  array_scalar_context(0,2,2,2147483647,-2147483648,2147483647);
  array_scalar_context(0,2,2,0,0,0);
  array_scalar_context(0,0,-2147483648,19,-7,3);
  array_scalar_context(0,0,-2147483648,-2147483648,2147483647,-1);
  array_scalar_context(0,0,-2147483648,2147483647,-2147483648,2147483647);
  array_scalar_context(0,0,-2147483648,0,0,0);
  array_scalar_context(0,2,0,19,-7,3);
  array_scalar_context(0,2,0,-2147483648,2147483647,-1);
  array_scalar_context(0,2,0,2147483647,-2147483648,2147483647);
  array_scalar_context(0,2,0,0,0,0);
  array_scalar_context(1,2,2,19,-7,3);
  array_scalar_wrap(0,1,1,19,-7,3);
  array_scalar_wrap(0,1,1,-2147483648,2147483647,-1);
  array_scalar_wrap(0,1,1,2147483647,-2147483648,2147483647);
  array_scalar_wrap(0,1,1,0,0,0);
  array_scalar_wrap(0,2,2,19,-7,3);
  array_scalar_wrap(0,2,2,-2147483648,2147483647,-1);
  array_scalar_wrap(0,2,2,2147483647,-2147483648,2147483647);
  array_scalar_wrap(0,2,2,0,0,0);
  array_scalar_wrap(0,0,-2147483648,19,-7,3);
  array_scalar_wrap(0,0,-2147483648,-2147483648,2147483647,-1);
  array_scalar_wrap(0,0,-2147483648,2147483647,-2147483648,2147483647);
  array_scalar_wrap(0,0,-2147483648,0,0,0);
  array_scalar_wrap(0,2,0,19,-7,3);
  array_scalar_wrap(0,2,0,-2147483648,2147483647,-1);
  array_scalar_wrap(0,2,0,2147483647,-2147483648,2147483647);
  array_scalar_wrap(0,2,0,0,0,0);
  array_scalar_wrap(1,2,2,19,-7,3);
  array_scalar_chain(0,1,1,19,-7,3);
  array_scalar_chain(0,1,1,-2147483648,2147483647,-1);
  array_scalar_chain(0,1,1,2147483647,-2147483648,2147483647);
  array_scalar_chain(0,1,1,0,0,0);
  array_scalar_chain(0,2,2,19,-7,3);
  array_scalar_chain(0,2,2,-2147483648,2147483647,-1);
  array_scalar_chain(0,2,2,2147483647,-2147483648,2147483647);
  array_scalar_chain(0,2,2,0,0,0);
  array_scalar_chain(0,0,-2147483648,19,-7,3);
  array_scalar_chain(0,0,-2147483648,-2147483648,2147483647,-1);
  array_scalar_chain(0,0,-2147483648,2147483647,-2147483648,2147483647);
  array_scalar_chain(0,0,-2147483648,0,0,0);
  array_scalar_chain(0,2,0,19,-7,3);
  array_scalar_chain(0,2,0,-2147483648,2147483647,-1);
  array_scalar_chain(0,2,0,2147483647,-2147483648,2147483647);
  array_scalar_chain(0,2,0,0,0,0);
  array_scalar_chain(1,2,2,19,-7,3);
  array_scalar_recurrence(0,1,1,19,-7,3);
  array_scalar_recurrence(0,1,1,-2147483648,2147483647,-1);
  array_scalar_recurrence(0,1,1,2147483647,-2147483648,2147483647);
  array_scalar_recurrence(0,1,1,0,0,0);
  array_scalar_recurrence(0,2,2,19,-7,3);
  array_scalar_recurrence(0,2,2,-2147483648,2147483647,-1);
  array_scalar_recurrence(0,2,2,2147483647,-2147483648,2147483647);
  array_scalar_recurrence(0,2,2,0,0,0);
  array_scalar_recurrence(0,0,-2147483648,19,-7,3);
  array_scalar_recurrence(0,0,-2147483648,-2147483648,2147483647,-1);
  array_scalar_recurrence(0,0,-2147483648,2147483647,-2147483648,2147483647);
  array_scalar_recurrence(0,0,-2147483648,0,0,0);
  array_scalar_recurrence(0,2,0,19,-7,3);
  array_scalar_recurrence(0,2,0,-2147483648,2147483647,-1);
  array_scalar_recurrence(0,2,0,2147483647,-2147483648,2147483647);
  array_scalar_recurrence(0,2,0,0,0,0);
  array_scalar_recurrence(1,2,2,19,-7,3);
  array_scalar_bound(0,1,1,19,-7,3);
  array_scalar_bound(0,1,1,-2147483648,2147483647,-1);
  array_scalar_bound(0,1,1,2147483647,-2147483648,2147483647);
  array_scalar_bound(0,1,1,0,0,0);
  array_scalar_bound(0,2,2,19,-7,3);
  array_scalar_bound(0,2,2,-2147483648,2147483647,-1);
  array_scalar_bound(0,2,2,2147483647,-2147483648,2147483647);
  array_scalar_bound(0,2,2,0,0,0);
  array_scalar_bound(0,0,-2147483648,19,-7,3);
  array_scalar_bound(0,0,-2147483648,-2147483648,2147483647,-1);
  array_scalar_bound(0,0,-2147483648,2147483647,-2147483648,2147483647);
  array_scalar_bound(0,0,-2147483648,0,0,0);
  array_scalar_bound(0,2,0,19,-7,3);
  array_scalar_bound(0,2,0,-2147483648,2147483647,-1);
  array_scalar_bound(0,2,0,2147483647,-2147483648,2147483647);
  array_scalar_bound(0,2,0,0,0,0);
  array_scalar_bound(1,2,2,19,-7,3);
  array_scalar_many(0,1,1,19,-7,3);
  array_scalar_many(0,1,1,-2147483648,2147483647,-1);
  array_scalar_many(0,1,1,2147483647,-2147483648,2147483647);
  array_scalar_many(0,1,1,0,0,0);
  array_scalar_many(0,2,2,19,-7,3);
  array_scalar_many(0,2,2,-2147483648,2147483647,-1);
  array_scalar_many(0,2,2,2147483647,-2147483648,2147483647);
  array_scalar_many(0,2,2,0,0,0);
  array_scalar_many(0,0,-2147483648,19,-7,3);
  array_scalar_many(0,0,-2147483648,-2147483648,2147483647,-1);
  array_scalar_many(0,0,-2147483648,2147483647,-2147483648,2147483647);
  array_scalar_many(0,0,-2147483648,0,0,0);
  array_scalar_many(0,2,0,19,-7,3);
  array_scalar_many(0,2,0,-2147483648,2147483647,-1);
  array_scalar_many(0,2,0,2147483647,-2147483648,2147483647);
  array_scalar_many(0,2,0,0,0,0);
  array_scalar_many(1,2,2,19,-7,3);
  array_scalar_undef(0,0,-2147483648,19,-7,3);
  array_scalar_undef(0,0,-2147483648,-2147483648,2147483647,-1);
  array_scalar_undef(0,0,-2147483648,2147483647,-2147483648,2147483647);
  array_scalar_undef(0,0,-2147483648,0,0,0);
  array_scalar_undef(0,2,0,19,-7,3);
  array_scalar_undef(0,2,0,-2147483648,2147483647,-1);
  array_scalar_undef(0,2,0,2147483647,-2147483648,2147483647);
  array_scalar_undef(0,2,0,0,0,0);
  array_scalar_nonlinear(0,1,1,19,-7,3);
  array_scalar_nonlinear(0,1,1,-2147483648,2147483647,-1);
  array_scalar_nonlinear(0,1,1,2147483647,-2147483648,2147483647);
  array_scalar_nonlinear(0,1,1,0,0,0);
  array_scalar_nonlinear(0,2,2,19,-7,3);
  array_scalar_nonlinear(0,2,2,-2147483648,2147483647,-1);
  array_scalar_nonlinear(0,2,2,2147483647,-2147483648,2147483647);
  array_scalar_nonlinear(0,2,2,0,0,0);
  array_scalar_nonlinear(0,0,-2147483648,19,-7,3);
  array_scalar_nonlinear(0,0,-2147483648,-2147483648,2147483647,-1);
  array_scalar_nonlinear(0,0,-2147483648,2147483647,-2147483648,2147483647);
  array_scalar_nonlinear(0,0,-2147483648,0,0,0);
  array_scalar_nonlinear(0,2,0,19,-7,3);
  array_scalar_nonlinear(0,2,0,-2147483648,2147483647,-1);
  array_scalar_nonlinear(0,2,0,2147483647,-2147483648,2147483647);
  array_scalar_nonlinear(0,2,0,0,0,0);
  array_scalar_nonlinear(1,2,2,19,-7,3);
  array_scalar_mutated(0,1,1,19,-7,3);
  array_scalar_mutated(0,1,1,-2147483648,2147483647,-1);
  array_scalar_mutated(0,1,1,2147483647,-2147483648,2147483647);
  array_scalar_mutated(0,1,1,0,0,0);
  array_scalar_mutated(0,2,2,19,-7,3);
  array_scalar_mutated(0,2,2,-2147483648,2147483647,-1);
  array_scalar_mutated(0,2,2,2147483647,-2147483648,2147483647);
  array_scalar_mutated(0,2,2,0,0,0);
  array_scalar_mutated(0,0,-2147483648,19,-7,3);
  array_scalar_mutated(0,0,-2147483648,-2147483648,2147483647,-1);
  array_scalar_mutated(0,0,-2147483648,2147483647,-2147483648,2147483647);
  array_scalar_mutated(0,0,-2147483648,0,0,0);
  array_scalar_mutated(0,2,0,19,-7,3);
  array_scalar_mutated(0,2,0,-2147483648,2147483647,-1);
  array_scalar_mutated(0,2,0,2147483647,-2147483648,2147483647);
  array_scalar_mutated(0,2,0,0,0,0);
  array_scalar_mutated(1,2,2,19,-7,3);
  array_scalar_three(0,1,1,1,19,-7,3);
  array_scalar_three(0,1,1,1,-2147483648,2147483647,-1);
  array_scalar_three(0,1,1,1,2147483647,-2147483648,2147483647);
  array_scalar_three(0,1,1,1,0,0,0);
  array_scalar_three(0,2,2,2,19,-7,3);
  array_scalar_three(0,2,2,2,-2147483648,2147483647,-1);
  array_scalar_three(0,2,2,2,2147483647,-2147483648,2147483647);
  array_scalar_three(0,2,2,2,0,0,0);
  array_scalar_three(0,0,-2147483648,-2147483648,19,-7,3);
  array_scalar_three(0,0,-2147483648,-2147483648,-2147483648,2147483647,-1);
  array_scalar_three(0,0,-2147483648,-2147483648,2147483647,-2147483648,2147483647);
  array_scalar_three(0,0,-2147483648,-2147483648,0,0,0);
  array_scalar_three(0,2,0,-2147483648,19,-7,3);
  array_scalar_three(0,2,0,-2147483648,-2147483648,2147483647,-1);
  array_scalar_three(0,2,0,-2147483648,2147483647,-2147483648,2147483647);
  array_scalar_three(0,2,0,-2147483648,0,0,0);
  array_scalar_three(0,2,2,0,19,-7,3);
  array_scalar_three(0,2,2,0,-2147483648,2147483647,-1);
  array_scalar_three(0,2,2,0,2147483647,-2147483648,2147483647);
  array_scalar_three(0,2,2,0,0,0,0);
  array_scalar_three(1,2,2,2,19,-7,3);
  array_scalar_four(0,1,1,1,1,19,-7,3);
  array_scalar_four(0,1,1,1,1,-2147483648,2147483647,-1);
  array_scalar_four(0,1,1,1,1,2147483647,-2147483648,2147483647);
  array_scalar_four(0,1,1,1,1,0,0,0);
  array_scalar_four(0,2,2,2,2,19,-7,3);
  array_scalar_four(0,2,2,2,2,-2147483648,2147483647,-1);
  array_scalar_four(0,2,2,2,2,2147483647,-2147483648,2147483647);
  array_scalar_four(0,2,2,2,2,0,0,0);
  array_scalar_four(0,0,-2147483648,-2147483648,-2147483648,19,-7,3);
  array_scalar_four(0,0,-2147483648,-2147483648,-2147483648,-2147483648,2147483647,-1);
  array_scalar_four(0,0,-2147483648,-2147483648,-2147483648,2147483647,-2147483648,2147483647);
  array_scalar_four(0,0,-2147483648,-2147483648,-2147483648,0,0,0);
  array_scalar_four(0,2,0,-2147483648,-2147483648,19,-7,3);
  array_scalar_four(0,2,0,-2147483648,-2147483648,-2147483648,2147483647,-1);
  array_scalar_four(0,2,0,-2147483648,-2147483648,2147483647,-2147483648,2147483647);
  array_scalar_four(0,2,0,-2147483648,-2147483648,0,0,0);
  array_scalar_four(0,2,2,0,-2147483648,19,-7,3);
  array_scalar_four(0,2,2,0,-2147483648,-2147483648,2147483647,-1);
  array_scalar_four(0,2,2,0,-2147483648,2147483647,-2147483648,2147483647);
  array_scalar_four(0,2,2,0,-2147483648,0,0,0);
  array_scalar_four(0,2,2,2,0,19,-7,3);
  array_scalar_four(0,2,2,2,0,-2147483648,2147483647,-1);
  array_scalar_four(0,2,2,2,0,2147483647,-2147483648,2147483647);
  array_scalar_four(0,2,2,2,0,0,0,0);
  array_scalar_four(1,2,2,2,2,19,-7,3);
  return 0;
}
