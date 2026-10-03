#include <stdio.h>

#define BUFFER_SIZE 1568
static void seed(int *values,int overflow) {
  int x;
  for(x=0;x<BUFFER_SIZE;++x) values[x]=overflow ? 2147483647-x : 3*x+1;
}
static void emit(const char *name,int offset,int *values,int *exits,int *limits,int dimensions) {
  int x;
  printf("%s %d",name,offset);
  for(x=0;x<dimensions;++x) printf(" %d",exits[x]);
  for(x=0;x<dimensions;++x) printf(" %d",limits[x]);
  for(x=0;x<BUFFER_SIZE;++x) printf(" %d",values[x]);
  putchar(10);
}
void pointer_two(int *buf,int start,int n,int m,int *exits) {
  int i=start,j=77;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      buf[i*8+j]=buf[i*8+j]+i*j+7;
    }
  }
  exits[0]=i;
  exits[1]=j;
}
void run_pointer_two(int offset,int start,int n,int m) {
  int values[BUFFER_SIZE],exits[2],limits[2];
  seed(values,0);
  pointer_two(offset<0 ? 0 : values+offset,start,n,m,exits);
  limits[0]=n;
  limits[1]=m;
  emit("pointer_two",offset,values,exits,limits,2);
}
void pointer_context(int *buf,int start,int n,int m,int *exits) {
  int i=start,j=77;
  int repeat;
  for(repeat=0;repeat<2;++repeat) {
    i=start;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      buf[i*8+j]=buf[i*8+j]+i*j+7;
    }
  }
  }
  exits[0]=i;
  exits[1]=j;
}
void run_pointer_context(int offset,int start,int n,int m) {
  int values[BUFFER_SIZE],exits[2],limits[2];
  seed(values,0);
  pointer_context(offset<0 ? 0 : values+offset,start,n,m,exits);
  limits[0]=n;
  limits[1]=m;
  emit("pointer_context",offset,values,exits,limits,2);
}
void pointer_wrap(int *buf,int start,int n,int m,int *exits) {
  int i=start,j=77;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      buf[i*8+j]=buf[i*8+j]+i*j+7;
    }
  }
  exits[0]=i;
  exits[1]=j;
}
void run_pointer_wrap(int offset,int start,int n,int m) {
  int values[BUFFER_SIZE],exits[2],limits[2];
  seed(values,1);
  pointer_wrap(offset<0 ? 0 : values+offset,start,n,m,exits);
  limits[0]=n;
  limits[1]=m;
  emit("pointer_wrap",offset,values,exits,limits,2);
}
void pointer_chain(int *buf,int start,int n,int m,int *exits) {
  int i=start,j=77;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      buf[i*8+j]=buf[i*8+j]+i*j+7;
      buf[i*8+j]=buf[i*8+j]+buf[i*8+j+1];
      buf[i*8+j+1]=buf[i*8+j];
    }
  }
  exits[0]=i;
  exits[1]=j;
}
void run_pointer_chain(int offset,int start,int n,int m) {
  int values[BUFFER_SIZE],exits[2],limits[2];
  seed(values,0);
  pointer_chain(offset<0 ? 0 : values+offset,start,n,m,exits);
  limits[0]=n;
  limits[1]=m;
  emit("pointer_chain",offset,values,exits,limits,2);
}
void pointer_recurrence(int *buf,int start,int n,int m,int *exits) {
  int i=start,j=77;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      buf[i*8+j]=buf[i*8+j]+buf[i*8+j+1];
    }
  }
  exits[0]=i;
  exits[1]=j;
}
void run_pointer_recurrence(int offset,int start,int n,int m) {
  int values[BUFFER_SIZE],exits[2],limits[2];
  seed(values,0);
  pointer_recurrence(offset<0 ? 0 : values+offset,start,n,m,exits);
  limits[0]=n;
  limits[1]=m;
  emit("pointer_recurrence",offset,values,exits,limits,2);
}
void pointer_nonlinear(int *buf,int start,int n,int m,int *exits) {
  int i=start,j=77;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      buf[i*8+j]=buf[i*j]+i*j+7;
    }
  }
  exits[0]=i;
  exits[1]=j;
}
void run_pointer_nonlinear(int offset,int start,int n,int m) {
  int values[BUFFER_SIZE],exits[2],limits[2];
  seed(values,0);
  pointer_nonlinear(offset<0 ? 0 : values+offset,start,n,m,exits);
  limits[0]=n;
  limits[1]=m;
  emit("pointer_nonlinear",offset,values,exits,limits,2);
}
void pointer_scalar(int *buf,int start,int n,int m,int *exits,int alpha) {
  int i=start,j=77;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      buf[i*8+j]=buf[i*8+j]*alpha+i*j+7;
    }
  }
  exits[0]=i;
  exits[1]=j;
}
void run_pointer_scalar(int offset,int start,int n,int m) {
  int values[BUFFER_SIZE],exits[2],limits[2];
  seed(values,0);
  pointer_scalar(offset<0 ? 0 : values+offset,start,n,m,exits,19);
  limits[0]=n;
  limits[1]=m;
  emit("pointer_scalar",offset,values,exits,limits,2);
}
void pointer_multi(int *dst,int *src,int start,int n,int m,int *exits) {
  int i=start,j=77;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      dst[i*8+j]=dst[i*8+j]+src[i*8+j]+i*j+7;
    }
  }
  exits[0]=i;
  exits[1]=j;
}
void run_pointer_multi(int offset,int start,int n,int m) {
  int values[BUFFER_SIZE],exits[2],limits[2];
  seed(values,0);
  pointer_multi(values+offset,values+offset+1,start,n,m,exits);
  limits[0]=n;
  limits[1]=m;
  emit("pointer_multi",offset,values,exits,limits,2);
}
void pointer_three(int *buf,int start,int n,int m,int p,int *exits) {
  int i=start,j=77,k=55;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<p;++k) {
        buf[i*128+j*16+k]=buf[i*128+j*16+k]+i*k+j+9;
      }
    }
  }
  exits[0]=i;
  exits[1]=j;
  exits[2]=k;
}
void run_pointer_three(int offset,int start,int n,int m,int p) {
  int values[BUFFER_SIZE],exits[3],limits[3];
  seed(values,0);
  pointer_three(offset<0 ? 0 : values+offset,start,n,m,p,exits);
  limits[0]=n;
  limits[1]=m;
  limits[2]=p;
  emit("pointer_three",offset,values,exits,limits,3);
}
void pointer_four(int *buf,int start,int n,int m,int p,int q,int *exits) {
  int i=start,j=77,k=55,t=33;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<p;++k) {
        for(t=0;t<q;++t) {
          buf[i*512+j*64+k*8+t]=buf[i*512+j*64+k*8+t]+i*j+k*t+11;
        }
      }
    }
  }
  exits[0]=i;
  exits[1]=j;
  exits[2]=k;
  exits[3]=t;
}
void run_pointer_four(int offset,int start,int n,int m,int p,int q) {
  int values[BUFFER_SIZE],exits[4],limits[4];
  seed(values,0);
  pointer_four(offset<0 ? 0 : values+offset,start,n,m,p,q,exits);
  limits[0]=n;
  limits[1]=m;
  limits[2]=p;
  limits[3]=q;
  emit("pointer_four",offset,values,exits,limits,4);
}
void pointer_undef(int *buf,int start,int n,int m,int p,int *exits) {
  int i=start,j=77,k=55;
  int unused_bound;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<unused_bound;++k) {
        buf[i*128+j*16+k]=buf[i*128+j*16+k]+i*k+j+9;
      }
    }
  }
  unused_bound=9;
  exits[0]=i;
  exits[1]=j;
  exits[2]=k;
}
void run_pointer_undef(int offset,int start,int n,int m,int p) {
  int values[BUFFER_SIZE],exits[3],limits[3];
  seed(values,0);
  pointer_undef(offset<0 ? 0 : values+offset,start,n,m,p,exits);
  limits[0]=n;
  limits[1]=m;
  limits[2]=9;
  emit("pointer_undef",offset,values,exits,limits,3);
}
void run_pointer_tiny(void) {
  int value[1]={17},exits[2];
  pointer_two(value,0,1,1,exits);
  printf("pointer_tiny %d %d %d\n",exits[0],exits[1],value[0]);
}
int main(void) {
  run_pointer_two(0,0,1,1);
  run_pointer_two(0,0,2,2);
  run_pointer_two(0,0,3,3);
  run_pointer_two(0,1,3,3);
  run_pointer_two(0,0,2,9);
  run_pointer_two(0,0,9,2);
  run_pointer_two(0,0,1,9);
  run_pointer_two(0,0,3,1);
  run_pointer_two(0,0,0,-2147483648);
  run_pointer_two(0,0,2,0);
  run_pointer_two(0,0,-1,2147483647);
  run_pointer_two(9,0,1,1);
  run_pointer_two(9,0,2,2);
  run_pointer_two(9,0,3,3);
  run_pointer_two(9,1,3,3);
  run_pointer_two(9,0,2,9);
  run_pointer_two(9,0,9,2);
  run_pointer_two(9,0,1,9);
  run_pointer_two(9,0,3,1);
  run_pointer_two(9,0,0,-2147483648);
  run_pointer_two(9,0,2,0);
  run_pointer_two(9,0,-1,2147483647);
  run_pointer_two(-1,0,0,-2147483648);
  run_pointer_context(0,0,1,1);
  run_pointer_context(0,0,2,2);
  run_pointer_context(0,0,3,3);
  run_pointer_context(0,1,3,3);
  run_pointer_context(0,0,2,9);
  run_pointer_context(0,0,9,2);
  run_pointer_context(0,0,1,9);
  run_pointer_context(0,0,3,1);
  run_pointer_context(0,0,0,-2147483648);
  run_pointer_context(0,0,2,0);
  run_pointer_context(0,0,-1,2147483647);
  run_pointer_context(9,0,1,1);
  run_pointer_context(9,0,2,2);
  run_pointer_context(9,0,3,3);
  run_pointer_context(9,1,3,3);
  run_pointer_context(9,0,2,9);
  run_pointer_context(9,0,9,2);
  run_pointer_context(9,0,1,9);
  run_pointer_context(9,0,3,1);
  run_pointer_context(9,0,0,-2147483648);
  run_pointer_context(9,0,2,0);
  run_pointer_context(9,0,-1,2147483647);
  run_pointer_context(-1,0,0,-2147483648);
  run_pointer_wrap(0,0,1,1);
  run_pointer_wrap(0,0,2,2);
  run_pointer_wrap(0,0,3,3);
  run_pointer_wrap(0,1,3,3);
  run_pointer_wrap(0,0,2,9);
  run_pointer_wrap(0,0,9,2);
  run_pointer_wrap(0,0,1,9);
  run_pointer_wrap(0,0,3,1);
  run_pointer_wrap(0,0,0,-2147483648);
  run_pointer_wrap(0,0,2,0);
  run_pointer_wrap(0,0,-1,2147483647);
  run_pointer_wrap(9,0,1,1);
  run_pointer_wrap(9,0,2,2);
  run_pointer_wrap(9,0,3,3);
  run_pointer_wrap(9,1,3,3);
  run_pointer_wrap(9,0,2,9);
  run_pointer_wrap(9,0,9,2);
  run_pointer_wrap(9,0,1,9);
  run_pointer_wrap(9,0,3,1);
  run_pointer_wrap(9,0,0,-2147483648);
  run_pointer_wrap(9,0,2,0);
  run_pointer_wrap(9,0,-1,2147483647);
  run_pointer_wrap(-1,0,0,-2147483648);
  run_pointer_chain(0,0,1,1);
  run_pointer_chain(0,0,2,2);
  run_pointer_chain(0,0,3,3);
  run_pointer_chain(0,1,3,3);
  run_pointer_chain(0,0,2,9);
  run_pointer_chain(0,0,9,2);
  run_pointer_chain(0,0,1,9);
  run_pointer_chain(0,0,3,1);
  run_pointer_chain(0,0,0,-2147483648);
  run_pointer_chain(0,0,2,0);
  run_pointer_chain(0,0,-1,2147483647);
  run_pointer_chain(9,0,1,1);
  run_pointer_chain(9,0,2,2);
  run_pointer_chain(9,0,3,3);
  run_pointer_chain(9,1,3,3);
  run_pointer_chain(9,0,2,9);
  run_pointer_chain(9,0,9,2);
  run_pointer_chain(9,0,1,9);
  run_pointer_chain(9,0,3,1);
  run_pointer_chain(9,0,0,-2147483648);
  run_pointer_chain(9,0,2,0);
  run_pointer_chain(9,0,-1,2147483647);
  run_pointer_chain(-1,0,0,-2147483648);
  run_pointer_recurrence(0,0,1,1);
  run_pointer_recurrence(0,0,2,2);
  run_pointer_recurrence(0,0,3,3);
  run_pointer_recurrence(0,1,3,3);
  run_pointer_recurrence(0,0,2,9);
  run_pointer_recurrence(0,0,9,2);
  run_pointer_recurrence(0,0,1,9);
  run_pointer_recurrence(0,0,3,1);
  run_pointer_recurrence(0,0,0,-2147483648);
  run_pointer_recurrence(0,0,2,0);
  run_pointer_recurrence(0,0,-1,2147483647);
  run_pointer_recurrence(9,0,1,1);
  run_pointer_recurrence(9,0,2,2);
  run_pointer_recurrence(9,0,3,3);
  run_pointer_recurrence(9,1,3,3);
  run_pointer_recurrence(9,0,2,9);
  run_pointer_recurrence(9,0,9,2);
  run_pointer_recurrence(9,0,1,9);
  run_pointer_recurrence(9,0,3,1);
  run_pointer_recurrence(9,0,0,-2147483648);
  run_pointer_recurrence(9,0,2,0);
  run_pointer_recurrence(9,0,-1,2147483647);
  run_pointer_recurrence(-1,0,0,-2147483648);
  run_pointer_nonlinear(0,0,1,1);
  run_pointer_nonlinear(0,0,2,2);
  run_pointer_nonlinear(0,0,3,3);
  run_pointer_nonlinear(0,1,3,3);
  run_pointer_nonlinear(0,0,2,9);
  run_pointer_nonlinear(0,0,9,2);
  run_pointer_nonlinear(0,0,1,9);
  run_pointer_nonlinear(0,0,3,1);
  run_pointer_nonlinear(0,0,0,-2147483648);
  run_pointer_nonlinear(0,0,2,0);
  run_pointer_nonlinear(0,0,-1,2147483647);
  run_pointer_nonlinear(9,0,1,1);
  run_pointer_nonlinear(9,0,2,2);
  run_pointer_nonlinear(9,0,3,3);
  run_pointer_nonlinear(9,1,3,3);
  run_pointer_nonlinear(9,0,2,9);
  run_pointer_nonlinear(9,0,9,2);
  run_pointer_nonlinear(9,0,1,9);
  run_pointer_nonlinear(9,0,3,1);
  run_pointer_nonlinear(9,0,0,-2147483648);
  run_pointer_nonlinear(9,0,2,0);
  run_pointer_nonlinear(9,0,-1,2147483647);
  run_pointer_nonlinear(-1,0,0,-2147483648);
  run_pointer_scalar(0,0,1,1);
  run_pointer_scalar(0,0,2,2);
  run_pointer_scalar(0,0,3,3);
  run_pointer_scalar(0,1,3,3);
  run_pointer_scalar(0,0,2,9);
  run_pointer_scalar(0,0,9,2);
  run_pointer_scalar(0,0,1,9);
  run_pointer_scalar(0,0,3,1);
  run_pointer_scalar(0,0,0,-2147483648);
  run_pointer_scalar(0,0,2,0);
  run_pointer_scalar(0,0,-1,2147483647);
  run_pointer_scalar(9,0,1,1);
  run_pointer_scalar(9,0,2,2);
  run_pointer_scalar(9,0,3,3);
  run_pointer_scalar(9,1,3,3);
  run_pointer_scalar(9,0,2,9);
  run_pointer_scalar(9,0,9,2);
  run_pointer_scalar(9,0,1,9);
  run_pointer_scalar(9,0,3,1);
  run_pointer_scalar(9,0,0,-2147483648);
  run_pointer_scalar(9,0,2,0);
  run_pointer_scalar(9,0,-1,2147483647);
  run_pointer_scalar(-1,0,0,-2147483648);
  run_pointer_multi(0,0,1,1);
  run_pointer_multi(0,0,2,2);
  run_pointer_multi(0,0,3,3);
  run_pointer_multi(0,1,3,3);
  run_pointer_multi(0,0,2,9);
  run_pointer_multi(0,0,9,2);
  run_pointer_multi(0,0,1,9);
  run_pointer_multi(0,0,3,1);
  run_pointer_multi(0,0,0,-2147483648);
  run_pointer_multi(0,0,2,0);
  run_pointer_multi(0,0,-1,2147483647);
  run_pointer_multi(9,0,1,1);
  run_pointer_multi(9,0,2,2);
  run_pointer_multi(9,0,3,3);
  run_pointer_multi(9,1,3,3);
  run_pointer_multi(9,0,2,9);
  run_pointer_multi(9,0,9,2);
  run_pointer_multi(9,0,1,9);
  run_pointer_multi(9,0,3,1);
  run_pointer_multi(9,0,0,-2147483648);
  run_pointer_multi(9,0,2,0);
  run_pointer_multi(9,0,-1,2147483647);
  run_pointer_three(0,0,1,1,1);
  run_pointer_three(0,0,2,2,2);
  run_pointer_three(0,0,3,3,3);
  run_pointer_three(0,1,3,3,3);
  run_pointer_three(0,0,0,-2147483648,-2147483648);
  run_pointer_three(0,0,2,0,-2147483648);
  run_pointer_three(0,0,2,2,0);
  run_pointer_three(0,0,-1,2147483647,2147483647);
  run_pointer_three(9,0,1,1,1);
  run_pointer_three(9,0,2,2,2);
  run_pointer_three(9,0,3,3,3);
  run_pointer_three(9,1,3,3,3);
  run_pointer_three(9,0,0,-2147483648,-2147483648);
  run_pointer_three(9,0,2,0,-2147483648);
  run_pointer_three(9,0,2,2,0);
  run_pointer_three(9,0,-1,2147483647,2147483647);
  run_pointer_three(-1,0,0,-2147483648,-2147483648);
  run_pointer_four(0,0,1,1,1,1);
  run_pointer_four(0,0,2,2,2,2);
  run_pointer_four(0,0,3,3,3,3);
  run_pointer_four(0,1,3,3,3,3);
  run_pointer_four(0,0,0,-2147483648,-2147483648,-2147483648);
  run_pointer_four(0,0,2,0,-2147483648,-2147483648);
  run_pointer_four(0,0,2,2,0,-2147483648);
  run_pointer_four(0,0,2,2,2,0);
  run_pointer_four(0,0,-1,2147483647,2147483647,2147483647);
  run_pointer_four(9,0,1,1,1,1);
  run_pointer_four(9,0,2,2,2,2);
  run_pointer_four(9,0,3,3,3,3);
  run_pointer_four(9,1,3,3,3,3);
  run_pointer_four(9,0,0,-2147483648,-2147483648,-2147483648);
  run_pointer_four(9,0,2,0,-2147483648,-2147483648);
  run_pointer_four(9,0,2,2,0,-2147483648);
  run_pointer_four(9,0,2,2,2,0);
  run_pointer_four(9,0,-1,2147483647,2147483647,2147483647);
  run_pointer_four(-1,0,0,-2147483648,-2147483648,-2147483648);
  run_pointer_undef(0,0,0,-2147483648,2147483647);
  run_pointer_undef(0,0,2,0,-2147483648);
  run_pointer_undef(0,1,0,2147483647,-2147483648);
  run_pointer_undef(9,0,0,-2147483648,2147483647);
  run_pointer_undef(9,0,2,0,-2147483648);
  run_pointer_undef(9,1,0,2147483647,-2147483648);
  run_pointer_undef(-1,0,0,-2147483648,-2147483648);
  run_pointer_tiny();
  return 0;
}
