#include <stdio.h>
#define BUFFER_SIZE 1568
static void seed(int *values,int overflow) {
  int x;
  for(x=0;x<BUFFER_SIZE;++x) values[x]=overflow ? 2147483647-x : 3*x+1;
}
static void emit(const char *name,int offset,int *values,int *exits,int *limits,int dimensions,int alpha,int beta,int gamma) {
  int x;
  printf("%s %d",name,offset);
  for(x=0;x<dimensions;++x) printf(" %d",exits[x]);
  for(x=0;x<dimensions;++x) printf(" %d",limits[x]);
  printf(" %d %d %d",alpha,beta,gamma);
  for(x=0;x<BUFFER_SIZE;++x) printf(" %d",values[x]);
  putchar(10);
}
void scalar_axpy(int *buf,int start,int n,int m,int *exits,int alpha,int beta,int gamma) {
  int i=start,j=77;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      buf[i*8+j]=buf[i*8+j]*alpha+beta+i*j+7;
    }
  }
  exits[0]=i;
  exits[1]=j;
}
void run_scalar_axpy(int offset,int start,int n,int m,int alpha,int beta,int gamma) {
  int values[BUFFER_SIZE],exits[2],limits[2];
  seed(values,0);
  scalar_axpy(offset<0 ? 0 : values+offset,start,n,m,exits,alpha,beta,gamma);
  limits[0]=n;
  limits[1]=m;
  emit("scalar_axpy",offset,values,exits,limits,2,alpha,beta,gamma);
}
void scalar_context(int *buf,int start,int n,int m,int *exits,int alpha,int beta,int gamma) {
  int i=start,j=77;
  int repeat;
  for(repeat=0;repeat<2;++repeat) {
    i=start;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      buf[i*8+j]=buf[i*8+j]*alpha+beta+i*j+7;
    }
  }
  }
  exits[0]=i;
  exits[1]=j;
}
void run_scalar_context(int offset,int start,int n,int m,int alpha,int beta,int gamma) {
  int values[BUFFER_SIZE],exits[2],limits[2];
  seed(values,0);
  scalar_context(offset<0 ? 0 : values+offset,start,n,m,exits,alpha,beta,gamma);
  limits[0]=n;
  limits[1]=m;
  emit("scalar_context",offset,values,exits,limits,2,alpha,beta,gamma);
}
void scalar_wrap(int *buf,int start,int n,int m,int *exits,int alpha,int beta,int gamma) {
  int i=start,j=77;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      buf[i*8+j]=buf[i*8+j]*alpha+beta+i*j+7;
    }
  }
  exits[0]=i;
  exits[1]=j;
}
void run_scalar_wrap(int offset,int start,int n,int m,int alpha,int beta,int gamma) {
  int values[BUFFER_SIZE],exits[2],limits[2];
  seed(values,1);
  scalar_wrap(offset<0 ? 0 : values+offset,start,n,m,exits,alpha,beta,gamma);
  limits[0]=n;
  limits[1]=m;
  emit("scalar_wrap",offset,values,exits,limits,2,alpha,beta,gamma);
}
void scalar_chain(int *buf,int start,int n,int m,int *exits,int alpha,int beta,int gamma) {
  int i=start,j=77;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      buf[i*8+j]=buf[i*8+j]*alpha+beta+i*j+7;
      buf[i*8+j]=buf[i*8+j]+buf[i*8+j+1]*alpha;
      buf[i*8+j+1]=buf[i*8+j]-beta;
    }
  }
  exits[0]=i;
  exits[1]=j;
}
void run_scalar_chain(int offset,int start,int n,int m,int alpha,int beta,int gamma) {
  int values[BUFFER_SIZE],exits[2],limits[2];
  seed(values,0);
  scalar_chain(offset<0 ? 0 : values+offset,start,n,m,exits,alpha,beta,gamma);
  limits[0]=n;
  limits[1]=m;
  emit("scalar_chain",offset,values,exits,limits,2,alpha,beta,gamma);
}
void scalar_recurrence(int *buf,int start,int n,int m,int *exits,int alpha,int beta,int gamma) {
  int i=start,j=77;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      buf[i*8+j]=buf[i*8+j]+buf[i*8+j+1]*alpha+beta;
    }
  }
  exits[0]=i;
  exits[1]=j;
}
void run_scalar_recurrence(int offset,int start,int n,int m,int alpha,int beta,int gamma) {
  int values[BUFFER_SIZE],exits[2],limits[2];
  seed(values,0);
  scalar_recurrence(offset<0 ? 0 : values+offset,start,n,m,exits,alpha,beta,gamma);
  limits[0]=n;
  limits[1]=m;
  emit("scalar_recurrence",offset,values,exits,limits,2,alpha,beta,gamma);
}
void scalar_bound(int *buf,int start,int n,int m,int *exits,int alpha,int beta,int gamma) {
  int i=start,j=77;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      buf[i*8+j]=buf[i*8+j]*n+m+i*j+7;
    }
  }
  exits[0]=i;
  exits[1]=j;
}
void run_scalar_bound(int offset,int start,int n,int m,int alpha,int beta,int gamma) {
  int values[BUFFER_SIZE],exits[2],limits[2];
  seed(values,0);
  scalar_bound(offset<0 ? 0 : values+offset,start,n,m,exits,alpha,beta,gamma);
  limits[0]=n;
  limits[1]=m;
  emit("scalar_bound",offset,values,exits,limits,2,alpha,beta,gamma);
}
void scalar_many(int *buf,int start,int n,int m,int *exits,int alpha,int beta,int gamma) {
  int i=start,j=77;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      buf[i*8+j]=buf[i*8+j]*alpha+beta*gamma+i*j+7;
    }
  }
  exits[0]=i;
  exits[1]=j;
}
void run_scalar_many(int offset,int start,int n,int m,int alpha,int beta,int gamma) {
  int values[BUFFER_SIZE],exits[2],limits[2];
  seed(values,0);
  scalar_many(offset<0 ? 0 : values+offset,start,n,m,exits,alpha,beta,gamma);
  limits[0]=n;
  limits[1]=m;
  emit("scalar_many",offset,values,exits,limits,2,alpha,beta,gamma);
}
void scalar_three(int *buf,int start,int n,int m,int p,int *exits,int alpha,int beta,int gamma) {
  int i=start,j=77,k=55;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<p;++k) {
        buf[i*128+j*16+k]=buf[i*128+j*16+k]*alpha+beta+i*k+j+9;
      }
    }
  }
  exits[0]=i;
  exits[1]=j;
  exits[2]=k;
}
void run_scalar_three(int offset,int start,int n,int m,int p,int alpha,int beta,int gamma) {
  int values[BUFFER_SIZE],exits[3],limits[3];
  seed(values,0);
  scalar_three(offset<0 ? 0 : values+offset,start,n,m,p,exits,alpha,beta,gamma);
  limits[0]=n;
  limits[1]=m;
  limits[2]=p;
  emit("scalar_three",offset,values,exits,limits,3,alpha,beta,gamma);
}
void scalar_four(int *buf,int start,int n,int m,int p,int q,int *exits,int alpha,int beta,int gamma) {
  int i=start,j=77,k=55,t=33;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<p;++k) {
        for(t=0;t<q;++t) {
          buf[i*512+j*64+k*8+t]=buf[i*512+j*64+k*8+t]*alpha+beta+i*j+k*t+11;
        }
      }
    }
  }
  exits[0]=i;
  exits[1]=j;
  exits[2]=k;
  exits[3]=t;
}
void run_scalar_four(int offset,int start,int n,int m,int p,int q,int alpha,int beta,int gamma) {
  int values[BUFFER_SIZE],exits[4],limits[4];
  seed(values,0);
  scalar_four(offset<0 ? 0 : values+offset,start,n,m,p,q,exits,alpha,beta,gamma);
  limits[0]=n;
  limits[1]=m;
  limits[2]=p;
  limits[3]=q;
  emit("scalar_four",offset,values,exits,limits,4,alpha,beta,gamma);
}
void scalar_undef(int *buf,int start,int n,int m,int *exits,int alpha,int beta,int gamma) {
  int i=start,j=77;
  int unused_alpha;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      buf[i*8+j]=buf[i*8+j]*unused_alpha+beta+i*j+7;
    }
  }
  unused_alpha=9;
  exits[0]=i;
  exits[1]=j;
}
void run_scalar_undef(int offset,int start,int n,int m,int alpha,int beta,int gamma) {
  int values[BUFFER_SIZE],exits[2],limits[2];
  seed(values,0);
  scalar_undef(offset<0 ? 0 : values+offset,start,n,m,exits,alpha,beta,gamma);
  limits[0]=n;
  limits[1]=m;
  emit("scalar_undef",offset,values,exits,limits,2,alpha,beta,gamma);
}
void scalar_nonlinear(int *buf,int start,int n,int m,int *exits,int alpha,int beta,int gamma) {
  int i=start,j=77;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      buf[i*8+j]=buf[i*j]*alpha+beta+i*j+7;
    }
  }
  exits[0]=i;
  exits[1]=j;
}
void run_scalar_nonlinear(int offset,int start,int n,int m,int alpha,int beta,int gamma) {
  int values[BUFFER_SIZE],exits[2],limits[2];
  seed(values,0);
  scalar_nonlinear(offset<0 ? 0 : values+offset,start,n,m,exits,alpha,beta,gamma);
  limits[0]=n;
  limits[1]=m;
  emit("scalar_nonlinear",offset,values,exits,limits,2,alpha,beta,gamma);
}
void scalar_mutated(int *buf,int start,int n,int m,int *exits,int alpha,int beta,int gamma) {
  int i=start,j=77;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      alpha=alpha+1;
      buf[i*8+j]=buf[i*8+j]*alpha+beta+i*j+7;
    }
  }
  exits[0]=i;
  exits[1]=j;
}
void run_scalar_mutated(int offset,int start,int n,int m,int alpha,int beta,int gamma) {
  int values[BUFFER_SIZE],exits[2],limits[2];
  seed(values,0);
  scalar_mutated(offset<0 ? 0 : values+offset,start,n,m,exits,alpha,beta,gamma);
  limits[0]=n;
  limits[1]=m;
  emit("scalar_mutated",offset,values,exits,limits,2,alpha,beta,gamma);
}
void scalar_multi(int *buf,int *src,int start,int n,int m,int *exits,int alpha,int beta,int gamma) {
  int i=start,j=77;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      buf[i*8+j]=buf[i*8+j]+src[i*8+j]*alpha+beta+i*j+7;
    }
  }
  exits[0]=i;
  exits[1]=j;
}
void run_scalar_multi(int offset,int start,int n,int m,int alpha,int beta,int gamma) {
  int values[BUFFER_SIZE],exits[2],limits[2];
  seed(values,0);
  scalar_multi(offset<0 ? 0 : values+offset,values+offset+1,start,n,m,exits,alpha,beta,gamma);
  limits[0]=n;
  limits[1]=m;
  emit("scalar_multi",offset,values,exits,limits,2,alpha,beta,gamma);
}
void run_scalar_tiny(void) {
  int value[1],exits[2];
  value[0]=17;
  scalar_axpy(value,0,1,1,exits,-7,2147483647,0);
  printf("scalar_tiny %d %d %d\n",exits[0],exits[1],value[0]);
}
int main(void) {
  run_scalar_axpy(9,0,2,2,19,-7,3);
  run_scalar_axpy(0,1,2,2,19,-7,3);
  run_scalar_axpy(9,0,2,2,-2147483648,2147483647,-1);
  run_scalar_axpy(0,1,2,2,-2147483648,2147483647,-1);
  run_scalar_axpy(9,0,2,2,-7,-2147483648,0);
  run_scalar_axpy(0,1,2,2,-7,-2147483648,0);
  run_scalar_axpy(9,0,2,2,2147483647,-2147483648,2147483647);
  run_scalar_axpy(0,1,2,2,2147483647,-2147483648,2147483647);
  run_scalar_axpy(9,0,2,2,0,0,0);
  run_scalar_axpy(0,1,2,2,0,0,0);
  run_scalar_axpy(9,0,2,2,-1,1,-1);
  run_scalar_axpy(0,1,2,2,-1,1,-1);
  run_scalar_axpy(9,0,1,1,19,7,3);
  run_scalar_axpy(-1,0,0,-2147483648,-2147483648,2147483647,3);
  run_scalar_axpy(-1,0,2,0,-2147483648,2147483647,3);
  run_scalar_axpy(-1,0,0,0,1,2,3);
  run_scalar_context(9,0,2,2,19,-7,3);
  run_scalar_context(0,1,2,2,19,-7,3);
  run_scalar_context(9,0,2,2,-2147483648,2147483647,-1);
  run_scalar_context(0,1,2,2,-2147483648,2147483647,-1);
  run_scalar_context(9,0,2,2,-7,-2147483648,0);
  run_scalar_context(0,1,2,2,-7,-2147483648,0);
  run_scalar_context(9,0,2,2,2147483647,-2147483648,2147483647);
  run_scalar_context(0,1,2,2,2147483647,-2147483648,2147483647);
  run_scalar_context(9,0,2,2,0,0,0);
  run_scalar_context(0,1,2,2,0,0,0);
  run_scalar_context(9,0,2,2,-1,1,-1);
  run_scalar_context(0,1,2,2,-1,1,-1);
  run_scalar_context(9,0,1,1,19,7,3);
  run_scalar_context(-1,0,0,-2147483648,-2147483648,2147483647,3);
  run_scalar_context(-1,0,2,0,-2147483648,2147483647,3);
  run_scalar_context(-1,0,0,0,1,2,3);
  run_scalar_wrap(9,0,2,2,19,-7,3);
  run_scalar_wrap(0,1,2,2,19,-7,3);
  run_scalar_wrap(9,0,2,2,-2147483648,2147483647,-1);
  run_scalar_wrap(0,1,2,2,-2147483648,2147483647,-1);
  run_scalar_wrap(9,0,2,2,-7,-2147483648,0);
  run_scalar_wrap(0,1,2,2,-7,-2147483648,0);
  run_scalar_wrap(9,0,2,2,2147483647,-2147483648,2147483647);
  run_scalar_wrap(0,1,2,2,2147483647,-2147483648,2147483647);
  run_scalar_wrap(9,0,2,2,0,0,0);
  run_scalar_wrap(0,1,2,2,0,0,0);
  run_scalar_wrap(9,0,2,2,-1,1,-1);
  run_scalar_wrap(0,1,2,2,-1,1,-1);
  run_scalar_wrap(9,0,1,1,19,7,3);
  run_scalar_wrap(-1,0,0,-2147483648,-2147483648,2147483647,3);
  run_scalar_wrap(-1,0,2,0,-2147483648,2147483647,3);
  run_scalar_wrap(-1,0,0,0,1,2,3);
  run_scalar_chain(9,0,2,2,19,-7,3);
  run_scalar_chain(0,1,2,2,19,-7,3);
  run_scalar_chain(9,0,2,2,-2147483648,2147483647,-1);
  run_scalar_chain(0,1,2,2,-2147483648,2147483647,-1);
  run_scalar_chain(9,0,2,2,-7,-2147483648,0);
  run_scalar_chain(0,1,2,2,-7,-2147483648,0);
  run_scalar_chain(9,0,2,2,2147483647,-2147483648,2147483647);
  run_scalar_chain(0,1,2,2,2147483647,-2147483648,2147483647);
  run_scalar_chain(9,0,2,2,0,0,0);
  run_scalar_chain(0,1,2,2,0,0,0);
  run_scalar_chain(9,0,2,2,-1,1,-1);
  run_scalar_chain(0,1,2,2,-1,1,-1);
  run_scalar_chain(9,0,1,1,19,7,3);
  run_scalar_chain(-1,0,0,-2147483648,-2147483648,2147483647,3);
  run_scalar_chain(-1,0,2,0,-2147483648,2147483647,3);
  run_scalar_chain(-1,0,0,0,1,2,3);
  run_scalar_recurrence(9,0,2,2,19,-7,3);
  run_scalar_recurrence(0,1,2,2,19,-7,3);
  run_scalar_recurrence(9,0,2,2,-2147483648,2147483647,-1);
  run_scalar_recurrence(0,1,2,2,-2147483648,2147483647,-1);
  run_scalar_recurrence(9,0,2,2,-7,-2147483648,0);
  run_scalar_recurrence(0,1,2,2,-7,-2147483648,0);
  run_scalar_recurrence(9,0,2,2,2147483647,-2147483648,2147483647);
  run_scalar_recurrence(0,1,2,2,2147483647,-2147483648,2147483647);
  run_scalar_recurrence(9,0,2,2,0,0,0);
  run_scalar_recurrence(0,1,2,2,0,0,0);
  run_scalar_recurrence(9,0,2,2,-1,1,-1);
  run_scalar_recurrence(0,1,2,2,-1,1,-1);
  run_scalar_recurrence(9,0,1,1,19,7,3);
  run_scalar_recurrence(-1,0,0,-2147483648,-2147483648,2147483647,3);
  run_scalar_recurrence(-1,0,2,0,-2147483648,2147483647,3);
  run_scalar_recurrence(-1,0,0,0,1,2,3);
  run_scalar_bound(9,0,2,2,19,-7,3);
  run_scalar_bound(0,1,2,2,19,-7,3);
  run_scalar_bound(9,0,2,2,-2147483648,2147483647,-1);
  run_scalar_bound(0,1,2,2,-2147483648,2147483647,-1);
  run_scalar_bound(9,0,2,2,-7,-2147483648,0);
  run_scalar_bound(0,1,2,2,-7,-2147483648,0);
  run_scalar_bound(9,0,2,2,2147483647,-2147483648,2147483647);
  run_scalar_bound(0,1,2,2,2147483647,-2147483648,2147483647);
  run_scalar_bound(9,0,2,2,0,0,0);
  run_scalar_bound(0,1,2,2,0,0,0);
  run_scalar_bound(9,0,2,2,-1,1,-1);
  run_scalar_bound(0,1,2,2,-1,1,-1);
  run_scalar_bound(9,0,1,1,19,7,3);
  run_scalar_bound(-1,0,0,-2147483648,-2147483648,2147483647,3);
  run_scalar_bound(-1,0,2,0,-2147483648,2147483647,3);
  run_scalar_bound(-1,0,0,0,1,2,3);
  run_scalar_many(9,0,2,2,19,-7,3);
  run_scalar_many(0,1,2,2,19,-7,3);
  run_scalar_many(9,0,2,2,-2147483648,2147483647,-1);
  run_scalar_many(0,1,2,2,-2147483648,2147483647,-1);
  run_scalar_many(9,0,2,2,-7,-2147483648,0);
  run_scalar_many(0,1,2,2,-7,-2147483648,0);
  run_scalar_many(9,0,2,2,2147483647,-2147483648,2147483647);
  run_scalar_many(0,1,2,2,2147483647,-2147483648,2147483647);
  run_scalar_many(9,0,2,2,0,0,0);
  run_scalar_many(0,1,2,2,0,0,0);
  run_scalar_many(9,0,2,2,-1,1,-1);
  run_scalar_many(0,1,2,2,-1,1,-1);
  run_scalar_many(9,0,1,1,19,7,3);
  run_scalar_many(-1,0,0,-2147483648,-2147483648,2147483647,3);
  run_scalar_many(-1,0,2,0,-2147483648,2147483647,3);
  run_scalar_many(-1,0,0,0,1,2,3);
  run_scalar_three(9,0,2,2,2,19,-7,3);
  run_scalar_three(0,1,2,2,2,19,-7,3);
  run_scalar_three(9,0,2,2,2,-2147483648,2147483647,-1);
  run_scalar_three(0,1,2,2,2,-2147483648,2147483647,-1);
  run_scalar_three(9,0,2,2,2,-7,-2147483648,0);
  run_scalar_three(0,1,2,2,2,-7,-2147483648,0);
  run_scalar_three(9,0,2,2,2,2147483647,-2147483648,2147483647);
  run_scalar_three(0,1,2,2,2,2147483647,-2147483648,2147483647);
  run_scalar_three(9,0,2,2,2,0,0,0);
  run_scalar_three(0,1,2,2,2,0,0,0);
  run_scalar_three(9,0,2,2,2,-1,1,-1);
  run_scalar_three(0,1,2,2,2,-1,1,-1);
  run_scalar_three(9,0,1,1,1,19,7,3);
  run_scalar_three(-1,0,0,-2147483648,-2147483648,-2147483648,2147483647,3);
  run_scalar_three(-1,0,2,0,-2147483648,-2147483648,2147483647,3);
  run_scalar_three(-1,0,2,2,0,-2147483648,2147483647,3);
  run_scalar_three(-1,0,0,0,0,1,2,3);
  run_scalar_four(9,0,2,2,2,2,19,-7,3);
  run_scalar_four(0,1,2,2,2,2,19,-7,3);
  run_scalar_four(9,0,2,2,2,2,-2147483648,2147483647,-1);
  run_scalar_four(0,1,2,2,2,2,-2147483648,2147483647,-1);
  run_scalar_four(9,0,2,2,2,2,-7,-2147483648,0);
  run_scalar_four(0,1,2,2,2,2,-7,-2147483648,0);
  run_scalar_four(9,0,2,2,2,2,2147483647,-2147483648,2147483647);
  run_scalar_four(0,1,2,2,2,2,2147483647,-2147483648,2147483647);
  run_scalar_four(9,0,2,2,2,2,0,0,0);
  run_scalar_four(0,1,2,2,2,2,0,0,0);
  run_scalar_four(9,0,2,2,2,2,-1,1,-1);
  run_scalar_four(0,1,2,2,2,2,-1,1,-1);
  run_scalar_four(9,0,1,1,1,1,19,7,3);
  run_scalar_four(-1,0,0,-2147483648,-2147483648,-2147483648,-2147483648,2147483647,3);
  run_scalar_four(-1,0,2,0,-2147483648,-2147483648,-2147483648,2147483647,3);
  run_scalar_four(-1,0,2,2,0,-2147483648,-2147483648,2147483647,3);
  run_scalar_four(-1,0,2,2,2,0,-2147483648,2147483647,3);
  run_scalar_four(-1,0,0,0,0,0,1,2,3);
  run_scalar_undef(-1,0,0,-2147483648,-2147483648,2147483647,3);
  run_scalar_undef(-1,0,2,0,-2147483648,2147483647,3);
  run_scalar_undef(-1,0,0,0,1,2,3);
  run_scalar_nonlinear(9,0,2,2,19,-7,3);
  run_scalar_nonlinear(0,1,2,2,19,-7,3);
  run_scalar_nonlinear(9,0,2,2,-2147483648,2147483647,-1);
  run_scalar_nonlinear(0,1,2,2,-2147483648,2147483647,-1);
  run_scalar_nonlinear(9,0,2,2,-7,-2147483648,0);
  run_scalar_nonlinear(0,1,2,2,-7,-2147483648,0);
  run_scalar_nonlinear(9,0,2,2,2147483647,-2147483648,2147483647);
  run_scalar_nonlinear(0,1,2,2,2147483647,-2147483648,2147483647);
  run_scalar_nonlinear(9,0,2,2,0,0,0);
  run_scalar_nonlinear(0,1,2,2,0,0,0);
  run_scalar_nonlinear(9,0,2,2,-1,1,-1);
  run_scalar_nonlinear(0,1,2,2,-1,1,-1);
  run_scalar_nonlinear(9,0,1,1,19,7,3);
  run_scalar_nonlinear(-1,0,0,-2147483648,-2147483648,2147483647,3);
  run_scalar_nonlinear(-1,0,2,0,-2147483648,2147483647,3);
  run_scalar_nonlinear(-1,0,0,0,1,2,3);
  run_scalar_mutated(9,0,2,2,19,-7,3);
  run_scalar_mutated(0,1,2,2,19,-7,3);
  run_scalar_mutated(9,0,2,2,-2147483648,2147483647,-1);
  run_scalar_mutated(0,1,2,2,-2147483648,2147483647,-1);
  run_scalar_mutated(9,0,2,2,-7,-2147483648,0);
  run_scalar_mutated(0,1,2,2,-7,-2147483648,0);
  run_scalar_mutated(9,0,2,2,2147483647,-2147483648,2147483647);
  run_scalar_mutated(0,1,2,2,2147483647,-2147483648,2147483647);
  run_scalar_mutated(9,0,2,2,0,0,0);
  run_scalar_mutated(0,1,2,2,0,0,0);
  run_scalar_mutated(9,0,2,2,-1,1,-1);
  run_scalar_mutated(0,1,2,2,-1,1,-1);
  run_scalar_mutated(9,0,1,1,19,7,3);
  run_scalar_mutated(-1,0,0,-2147483648,-2147483648,2147483647,3);
  run_scalar_mutated(-1,0,2,0,-2147483648,2147483647,3);
  run_scalar_mutated(-1,0,0,0,1,2,3);
  run_scalar_multi(9,0,2,2,19,-7,3);
  run_scalar_multi(0,1,2,2,19,-7,3);
  run_scalar_multi(9,0,2,2,-2147483648,2147483647,-1);
  run_scalar_multi(0,1,2,2,-2147483648,2147483647,-1);
  run_scalar_multi(9,0,2,2,-7,-2147483648,0);
  run_scalar_multi(0,1,2,2,-7,-2147483648,0);
  run_scalar_multi(9,0,2,2,2147483647,-2147483648,2147483647);
  run_scalar_multi(0,1,2,2,2147483647,-2147483648,2147483647);
  run_scalar_multi(9,0,2,2,0,0,0);
  run_scalar_multi(0,1,2,2,0,0,0);
  run_scalar_multi(9,0,2,2,-1,1,-1);
  run_scalar_multi(0,1,2,2,-1,1,-1);
  run_scalar_multi(9,0,1,1,19,7,3);
  run_scalar_tiny();
  return 0;
}
