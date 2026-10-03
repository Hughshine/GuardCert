#include <stdio.h>

int deep_ga[256],deep_gb[256],deep_gc[256];
static void seed(int *a,int *b,int *c,int extent,int overflow) {
  int x;
  for(x=0;x<extent;++x) {
    a[x]=overflow ? 2147483647-x : 3*x+1;
    b[x]=overflow ? 2147483647-2*x : 5*x+2;
    c[x]=overflow ? 2147483647-3*x : -777;
  }
}
static void emit(const char *name,int *a,int *b,int *c,int extent,
  int *counters,int *bounds,int dimensions) {
  int x,which;
  for(which=0;which<3;++which) {
    int *values=which==0 ? a : which==1 ? b : c;
    printf("%s-%c",name,'a'+which);
    for(x=0;x<dimensions;++x) printf(" %d",counters[x]);
    for(x=0;x<dimensions;++x) printf(" %d",bounds[x]);
    for(x=0;x<extent;++x) printf(" %d",values[x]);
    putchar(10);
  }
}
void deep_four(int start,int n,int m,int p,int q) {
  int a[256],b[256],c[256];
  int i=start,j=99,k=55,t=44;
  int counters[4],limits[4];
  seed(a,b,c,256,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<p;++k) {
        for(t=0;t<q;++t) {
          c[i*64+j*16+k*4+t]=a[i*64+j*16+k*4+t]+b[i*64+j*16+k*4+t]+i*j+k*t;
        }
      }
    }
  }
  counters[0]=i; limits[0]=n;
  counters[1]=j; limits[1]=m;
  counters[2]=k; limits[2]=p;
  counters[3]=t; limits[3]=q;
  emit("deep_four",a,b,c,256,counters,limits,4);
}
void deep_four_global(int start,int n,int m,int p,int q) {
  int i=start,j=99,k=55,t=44;
  int counters[4],limits[4];
  seed(deep_ga,deep_gb,deep_gc,256,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<p;++k) {
        for(t=0;t<q;++t) {
          deep_gc[i*64+j*16+k*4+t]=deep_ga[i*64+j*16+k*4+t]+deep_gb[i*64+j*16+k*4+t]+i*j+k*t;
        }
      }
    }
  }
  counters[0]=i; limits[0]=n;
  counters[1]=j; limits[1]=m;
  counters[2]=k; limits[2]=p;
  counters[3]=t; limits[3]=q;
  emit("deep_four_global",deep_ga,deep_gb,deep_gc,256,counters,limits,4);
}
void deep_four_context(int start,int n,int m,int p,int q) {
  int a[256],b[256],c[256];
  int i=start,j=99,k=55,t=44;
  int counters[4],limits[4];
  seed(a,b,c,256,0);
  int repeat;
  for(repeat=0;repeat<2;++repeat) {
    i=start;
    for(;i<n;++i) {
      for(j=0;j<m;++j) {
        for(k=0;k<p;++k) {
          for(t=0;t<q;++t) {
            c[i*64+j*16+k*4+t]=a[i*64+j*16+k*4+t]+b[i*64+j*16+k*4+t]+i*j+k*t;
          }
        }
      }
    }
  }
  counters[0]=i; limits[0]=n;
  counters[1]=j; limits[1]=m;
  counters[2]=k; limits[2]=p;
  counters[3]=t; limits[3]=q;
  emit("deep_four_context",a,b,c,256,counters,limits,4);
}
void deep_four_wrap(int start,int n,int m,int p,int q) {
  int a[256],b[256],c[256];
  int i=start,j=99,k=55,t=44;
  int counters[4],limits[4];
  seed(a,b,c,256,1);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<p;++k) {
        for(t=0;t<q;++t) {
          c[i*64+j*16+k*4+t]=a[i*64+j*16+k*4+t]+b[i*64+j*16+k*4+t]+i*j+k*t;
        }
      }
    }
  }
  counters[0]=i; limits[0]=n;
  counters[1]=j; limits[1]=m;
  counters[2]=k; limits[2]=p;
  counters[3]=t; limits[3]=q;
  emit("deep_four_wrap",a,b,c,256,counters,limits,4);
}
void deep_four_chain(int start,int n,int m,int p,int q) {
  int a[256],b[256],c[256];
  int i=start,j=99,k=55,t=44;
  int counters[4],limits[4];
  seed(a,b,c,256,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<p;++k) {
        for(t=0;t<q;++t) {
          b[i*64+j*16+k*4+t]=a[i*64+j*16+k*4+t]+i*j+k*t;
          c[i*64+j*16+k*4+t]=b[i*64+j*16+k*4+t]+b[i*64+j*16+k*4+t+1];
          b[i*64+j*16+k*4+t]=c[i*64+j*16+k*4+t];
        }
      }
    }
  }
  counters[0]=i; limits[0]=n;
  counters[1]=j; limits[1]=m;
  counters[2]=k; limits[2]=p;
  counters[3]=t; limits[3]=q;
  emit("deep_four_chain",a,b,c,256,counters,limits,4);
}
void deep_four_recurrence(int start,int n,int m,int p,int q) {
  int a[256],b[256],c[256];
  int i=start,j=99,k=55,t=44;
  int counters[4],limits[4];
  seed(a,b,c,256,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<p;++k) {
        for(t=0;t<q;++t) {
          b[i*64+j*16+k*4+t]=b[i*64+j*16+k*4+t]+b[i*64+j*16+k*4+t+1];
        }
      }
    }
  }
  counters[0]=i; limits[0]=n;
  counters[1]=j; limits[1]=m;
  counters[2]=k; limits[2]=p;
  counters[3]=t; limits[3]=q;
  emit("deep_four_recurrence",a,b,c,256,counters,limits,4);
}
void deep_four_nonlinear(int start,int n,int m,int p,int q) {
  int a[256],b[256],c[256];
  int i=start,j=99,k=55,t=44;
  int counters[4],limits[4];
  seed(a,b,c,256,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<p;++k) {
        for(t=0;t<q;++t) {
          c[i*64+j*16+k*4+t]=a[i*j+k*4+t]+b[i*64+j*16+k*4+t];
        }
      }
    }
  }
  counters[0]=i; limits[0]=n;
  counters[1]=j; limits[1]=m;
  counters[2]=k; limits[2]=p;
  counters[3]=t; limits[3]=q;
  emit("deep_four_nonlinear",a,b,c,256,counters,limits,4);
}
void deep_four_unanchored(int start,int n,int m,int p,int q) {
  int a[256],b[256],c[256];
  int i=start,j=99,k=55,t=44;
  int counters[4],limits[4];
  seed(a,b,c,256,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<p;++k) {
        for(t=0;t<q;++t) {
          c[i*64+j*16+k*4+t]=a[i*64+j*16+k*4+t+1]+b[i*64+j*16+k*4+t]+i*j+k*t;
        }
      }
    }
  }
  counters[0]=i; limits[0]=n;
  counters[1]=j; limits[1]=m;
  counters[2]=k; limits[2]=p;
  counters[3]=t; limits[3]=q;
  emit("deep_four_unanchored",a,b,c,256,counters,limits,4);
}
void deep_four_undef(int start,int n,int m,int p,int ignored) {
  int a[256],b[256],c[256];
  int i=start,j=99,k=55,t=44;
  int q;
  int counters[4],limits[4];
  seed(a,b,c,256,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<p;++k) {
        for(t=0;t<q;++t) {
          c[i*64+j*16+k*4+t]=a[i*64+j*16+k*4+t]+b[i*64+j*16+k*4+t]+i*j+k*t;
        }
      }
    }
  }
  q=9;
  counters[0]=i; limits[0]=n;
  counters[1]=j; limits[1]=m;
  counters[2]=k; limits[2]=p;
  counters[3]=t; limits[3]=q;
  emit("deep_four_undef",a,b,c,256,counters,limits,4);
}
void deep_five(int start,int n,int m,int p,int q,int r) {
  int a[243],b[243],c[243];
  int i=start,j=99,k=55,t=44,u=33;
  int counters[5],limits[5];
  seed(a,b,c,243,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<p;++k) {
        for(t=0;t<q;++t) {
          for(u=0;u<r;++u) {
            c[i*81+j*27+k*9+t*3+u]=a[i*81+j*27+k*9+t*3+u]+b[i*81+j*27+k*9+t*3+u]+i*j+k*t+u;
          }
        }
      }
    }
  }
  counters[0]=i; limits[0]=n;
  counters[1]=j; limits[1]=m;
  counters[2]=k; limits[2]=p;
  counters[3]=t; limits[3]=q;
  counters[4]=u; limits[4]=r;
  emit("deep_five",a,b,c,243,counters,limits,5);
}
void deep_six(int start,int n,int m,int p,int q,int r,int s) {
  int a[729],b[729],c[729];
  int i=start,j=99,k=55,t=44,u=33,v=22;
  int counters[6],limits[6];
  seed(a,b,c,729,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<p;++k) {
        for(t=0;t<q;++t) {
          for(u=0;u<r;++u) {
            for(v=0;v<s;++v) {
              c[i*243+j*81+k*27+t*9+u*3+v]=a[i*243+j*81+k*27+t*9+u*3+v]+b[i*243+j*81+k*27+t*9+u*3+v]+i*j+k*t+u*v;
            }
          }
        }
      }
    }
  }
  counters[0]=i; limits[0]=n;
  counters[1]=j; limits[1]=m;
  counters[2]=k; limits[2]=p;
  counters[3]=t; limits[3]=q;
  counters[4]=u; limits[4]=r;
  counters[5]=v; limits[5]=s;
  emit("deep_six",a,b,c,729,counters,limits,6);
}
void deep_eight(int start,int n,int m,int p,int q,int r,int s,int h,int z) {
  int a[256],b[256],c[256];
  int i=start,j=99,k=55,t=44,u=33,v=22,w=11,x=8;
  int counters[8],limits[8];
  seed(a,b,c,256,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<p;++k) {
        for(t=0;t<q;++t) {
          for(u=0;u<r;++u) {
            for(v=0;v<s;++v) {
              for(w=0;w<h;++w) {
                for(x=0;x<z;++x) {
                  c[i*128+j*64+k*32+t*16+u*8+v*4+w*2+x]=a[i*128+j*64+k*32+t*16+u*8+v*4+w*2+x]+b[i*128+j*64+k*32+t*16+u*8+v*4+w*2+x]+i*j+k*t+u*v+w*x;
                }
              }
            }
          }
        }
      }
    }
  }
  counters[0]=i; limits[0]=n;
  counters[1]=j; limits[1]=m;
  counters[2]=k; limits[2]=p;
  counters[3]=t; limits[3]=q;
  counters[4]=u; limits[4]=r;
  counters[5]=v; limits[5]=s;
  counters[6]=w; limits[6]=h;
  counters[7]=x; limits[7]=z;
  emit("deep_eight",a,b,c,256,counters,limits,8);
}
void deep_nine(int start,int n,int m,int p,int q,int r,int s,int h,int z,int g) {
  int a[512],b[512],c[512];
  int i=start,j=99,k=55,t=44,u=33,v=22,w=11,x=8,y=7;
  int counters[9],limits[9];
  seed(a,b,c,512,0);
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      for(k=0;k<p;++k) {
        for(t=0;t<q;++t) {
          for(u=0;u<r;++u) {
            for(v=0;v<s;++v) {
              for(w=0;w<h;++w) {
                for(x=0;x<z;++x) {
                  for(y=0;y<g;++y) {
                    c[i*256+j*128+k*64+t*32+u*16+v*8+w*4+x*2+y]=a[i*256+j*128+k*64+t*32+u*16+v*8+w*4+x*2+y]+b[i*256+j*128+k*64+t*32+u*16+v*8+w*4+x*2+y]+i*j+k*t+u*v+w*x+y;
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  counters[0]=i; limits[0]=n;
  counters[1]=j; limits[1]=m;
  counters[2]=k; limits[2]=p;
  counters[3]=t; limits[3]=q;
  counters[4]=u; limits[4]=r;
  counters[5]=v; limits[5]=s;
  counters[6]=w; limits[6]=h;
  counters[7]=x; limits[7]=z;
  counters[8]=y; limits[8]=g;
  emit("deep_nine",a,b,c,512,counters,limits,9);
}

int main(void) {
  deep_four(0,0,0,0,0);
  deep_four_global(0,0,0,0,0);
  deep_four_context(0,0,0,0,0);
  deep_four_wrap(0,0,0,0,0);
  deep_four_chain(0,0,0,0,0);
  deep_four_recurrence(0,0,0,0,0);
  deep_four_nonlinear(0,0,0,0,0);
  deep_four_unanchored(0,0,0,0,0);
  deep_four(0,0,0,0,1);
  deep_four_global(0,0,0,0,1);
  deep_four_context(0,0,0,0,1);
  deep_four_wrap(0,0,0,0,1);
  deep_four_chain(0,0,0,0,1);
  deep_four_recurrence(0,0,0,0,1);
  deep_four_nonlinear(0,0,0,0,1);
  deep_four_unanchored(0,0,0,0,1);
  deep_four(0,0,0,0,2);
  deep_four_global(0,0,0,0,2);
  deep_four_context(0,0,0,0,2);
  deep_four_wrap(0,0,0,0,2);
  deep_four_chain(0,0,0,0,2);
  deep_four_recurrence(0,0,0,0,2);
  deep_four_nonlinear(0,0,0,0,2);
  deep_four_unanchored(0,0,0,0,2);
  deep_four(0,0,0,1,0);
  deep_four_global(0,0,0,1,0);
  deep_four_context(0,0,0,1,0);
  deep_four_wrap(0,0,0,1,0);
  deep_four_chain(0,0,0,1,0);
  deep_four_recurrence(0,0,0,1,0);
  deep_four_nonlinear(0,0,0,1,0);
  deep_four_unanchored(0,0,0,1,0);
  deep_four(0,0,0,1,1);
  deep_four_global(0,0,0,1,1);
  deep_four_context(0,0,0,1,1);
  deep_four_wrap(0,0,0,1,1);
  deep_four_chain(0,0,0,1,1);
  deep_four_recurrence(0,0,0,1,1);
  deep_four_nonlinear(0,0,0,1,1);
  deep_four_unanchored(0,0,0,1,1);
  deep_four(0,0,0,1,2);
  deep_four_global(0,0,0,1,2);
  deep_four_context(0,0,0,1,2);
  deep_four_wrap(0,0,0,1,2);
  deep_four_chain(0,0,0,1,2);
  deep_four_recurrence(0,0,0,1,2);
  deep_four_nonlinear(0,0,0,1,2);
  deep_four_unanchored(0,0,0,1,2);
  deep_four(0,0,0,2,0);
  deep_four_global(0,0,0,2,0);
  deep_four_context(0,0,0,2,0);
  deep_four_wrap(0,0,0,2,0);
  deep_four_chain(0,0,0,2,0);
  deep_four_recurrence(0,0,0,2,0);
  deep_four_nonlinear(0,0,0,2,0);
  deep_four_unanchored(0,0,0,2,0);
  deep_four(0,0,0,2,1);
  deep_four_global(0,0,0,2,1);
  deep_four_context(0,0,0,2,1);
  deep_four_wrap(0,0,0,2,1);
  deep_four_chain(0,0,0,2,1);
  deep_four_recurrence(0,0,0,2,1);
  deep_four_nonlinear(0,0,0,2,1);
  deep_four_unanchored(0,0,0,2,1);
  deep_four(0,0,0,2,2);
  deep_four_global(0,0,0,2,2);
  deep_four_context(0,0,0,2,2);
  deep_four_wrap(0,0,0,2,2);
  deep_four_chain(0,0,0,2,2);
  deep_four_recurrence(0,0,0,2,2);
  deep_four_nonlinear(0,0,0,2,2);
  deep_four_unanchored(0,0,0,2,2);
  deep_four(0,0,1,0,0);
  deep_four_global(0,0,1,0,0);
  deep_four_context(0,0,1,0,0);
  deep_four_wrap(0,0,1,0,0);
  deep_four_chain(0,0,1,0,0);
  deep_four_recurrence(0,0,1,0,0);
  deep_four_nonlinear(0,0,1,0,0);
  deep_four_unanchored(0,0,1,0,0);
  deep_four(0,0,1,0,1);
  deep_four_global(0,0,1,0,1);
  deep_four_context(0,0,1,0,1);
  deep_four_wrap(0,0,1,0,1);
  deep_four_chain(0,0,1,0,1);
  deep_four_recurrence(0,0,1,0,1);
  deep_four_nonlinear(0,0,1,0,1);
  deep_four_unanchored(0,0,1,0,1);
  deep_four(0,0,1,0,2);
  deep_four_global(0,0,1,0,2);
  deep_four_context(0,0,1,0,2);
  deep_four_wrap(0,0,1,0,2);
  deep_four_chain(0,0,1,0,2);
  deep_four_recurrence(0,0,1,0,2);
  deep_four_nonlinear(0,0,1,0,2);
  deep_four_unanchored(0,0,1,0,2);
  deep_four(0,0,1,1,0);
  deep_four_global(0,0,1,1,0);
  deep_four_context(0,0,1,1,0);
  deep_four_wrap(0,0,1,1,0);
  deep_four_chain(0,0,1,1,0);
  deep_four_recurrence(0,0,1,1,0);
  deep_four_nonlinear(0,0,1,1,0);
  deep_four_unanchored(0,0,1,1,0);
  deep_four(0,0,1,1,1);
  deep_four_global(0,0,1,1,1);
  deep_four_context(0,0,1,1,1);
  deep_four_wrap(0,0,1,1,1);
  deep_four_chain(0,0,1,1,1);
  deep_four_recurrence(0,0,1,1,1);
  deep_four_nonlinear(0,0,1,1,1);
  deep_four_unanchored(0,0,1,1,1);
  deep_four(0,0,1,1,2);
  deep_four_global(0,0,1,1,2);
  deep_four_context(0,0,1,1,2);
  deep_four_wrap(0,0,1,1,2);
  deep_four_chain(0,0,1,1,2);
  deep_four_recurrence(0,0,1,1,2);
  deep_four_nonlinear(0,0,1,1,2);
  deep_four_unanchored(0,0,1,1,2);
  deep_four(0,0,1,2,0);
  deep_four_global(0,0,1,2,0);
  deep_four_context(0,0,1,2,0);
  deep_four_wrap(0,0,1,2,0);
  deep_four_chain(0,0,1,2,0);
  deep_four_recurrence(0,0,1,2,0);
  deep_four_nonlinear(0,0,1,2,0);
  deep_four_unanchored(0,0,1,2,0);
  deep_four(0,0,1,2,1);
  deep_four_global(0,0,1,2,1);
  deep_four_context(0,0,1,2,1);
  deep_four_wrap(0,0,1,2,1);
  deep_four_chain(0,0,1,2,1);
  deep_four_recurrence(0,0,1,2,1);
  deep_four_nonlinear(0,0,1,2,1);
  deep_four_unanchored(0,0,1,2,1);
  deep_four(0,0,1,2,2);
  deep_four_global(0,0,1,2,2);
  deep_four_context(0,0,1,2,2);
  deep_four_wrap(0,0,1,2,2);
  deep_four_chain(0,0,1,2,2);
  deep_four_recurrence(0,0,1,2,2);
  deep_four_nonlinear(0,0,1,2,2);
  deep_four_unanchored(0,0,1,2,2);
  deep_four(0,0,2,0,0);
  deep_four_global(0,0,2,0,0);
  deep_four_context(0,0,2,0,0);
  deep_four_wrap(0,0,2,0,0);
  deep_four_chain(0,0,2,0,0);
  deep_four_recurrence(0,0,2,0,0);
  deep_four_nonlinear(0,0,2,0,0);
  deep_four_unanchored(0,0,2,0,0);
  deep_four(0,0,2,0,1);
  deep_four_global(0,0,2,0,1);
  deep_four_context(0,0,2,0,1);
  deep_four_wrap(0,0,2,0,1);
  deep_four_chain(0,0,2,0,1);
  deep_four_recurrence(0,0,2,0,1);
  deep_four_nonlinear(0,0,2,0,1);
  deep_four_unanchored(0,0,2,0,1);
  deep_four(0,0,2,0,2);
  deep_four_global(0,0,2,0,2);
  deep_four_context(0,0,2,0,2);
  deep_four_wrap(0,0,2,0,2);
  deep_four_chain(0,0,2,0,2);
  deep_four_recurrence(0,0,2,0,2);
  deep_four_nonlinear(0,0,2,0,2);
  deep_four_unanchored(0,0,2,0,2);
  deep_four(0,0,2,1,0);
  deep_four_global(0,0,2,1,0);
  deep_four_context(0,0,2,1,0);
  deep_four_wrap(0,0,2,1,0);
  deep_four_chain(0,0,2,1,0);
  deep_four_recurrence(0,0,2,1,0);
  deep_four_nonlinear(0,0,2,1,0);
  deep_four_unanchored(0,0,2,1,0);
  deep_four(0,0,2,1,1);
  deep_four_global(0,0,2,1,1);
  deep_four_context(0,0,2,1,1);
  deep_four_wrap(0,0,2,1,1);
  deep_four_chain(0,0,2,1,1);
  deep_four_recurrence(0,0,2,1,1);
  deep_four_nonlinear(0,0,2,1,1);
  deep_four_unanchored(0,0,2,1,1);
  deep_four(0,0,2,1,2);
  deep_four_global(0,0,2,1,2);
  deep_four_context(0,0,2,1,2);
  deep_four_wrap(0,0,2,1,2);
  deep_four_chain(0,0,2,1,2);
  deep_four_recurrence(0,0,2,1,2);
  deep_four_nonlinear(0,0,2,1,2);
  deep_four_unanchored(0,0,2,1,2);
  deep_four(0,0,2,2,0);
  deep_four_global(0,0,2,2,0);
  deep_four_context(0,0,2,2,0);
  deep_four_wrap(0,0,2,2,0);
  deep_four_chain(0,0,2,2,0);
  deep_four_recurrence(0,0,2,2,0);
  deep_four_nonlinear(0,0,2,2,0);
  deep_four_unanchored(0,0,2,2,0);
  deep_four(0,0,2,2,1);
  deep_four_global(0,0,2,2,1);
  deep_four_context(0,0,2,2,1);
  deep_four_wrap(0,0,2,2,1);
  deep_four_chain(0,0,2,2,1);
  deep_four_recurrence(0,0,2,2,1);
  deep_four_nonlinear(0,0,2,2,1);
  deep_four_unanchored(0,0,2,2,1);
  deep_four(0,0,2,2,2);
  deep_four_global(0,0,2,2,2);
  deep_four_context(0,0,2,2,2);
  deep_four_wrap(0,0,2,2,2);
  deep_four_chain(0,0,2,2,2);
  deep_four_recurrence(0,0,2,2,2);
  deep_four_nonlinear(0,0,2,2,2);
  deep_four_unanchored(0,0,2,2,2);
  deep_four(0,1,0,0,0);
  deep_four_global(0,1,0,0,0);
  deep_four_context(0,1,0,0,0);
  deep_four_wrap(0,1,0,0,0);
  deep_four_chain(0,1,0,0,0);
  deep_four_recurrence(0,1,0,0,0);
  deep_four_nonlinear(0,1,0,0,0);
  deep_four_unanchored(0,1,0,0,0);
  deep_four(0,1,0,0,1);
  deep_four_global(0,1,0,0,1);
  deep_four_context(0,1,0,0,1);
  deep_four_wrap(0,1,0,0,1);
  deep_four_chain(0,1,0,0,1);
  deep_four_recurrence(0,1,0,0,1);
  deep_four_nonlinear(0,1,0,0,1);
  deep_four_unanchored(0,1,0,0,1);
  deep_four(0,1,0,0,2);
  deep_four_global(0,1,0,0,2);
  deep_four_context(0,1,0,0,2);
  deep_four_wrap(0,1,0,0,2);
  deep_four_chain(0,1,0,0,2);
  deep_four_recurrence(0,1,0,0,2);
  deep_four_nonlinear(0,1,0,0,2);
  deep_four_unanchored(0,1,0,0,2);
  deep_four(0,1,0,1,0);
  deep_four_global(0,1,0,1,0);
  deep_four_context(0,1,0,1,0);
  deep_four_wrap(0,1,0,1,0);
  deep_four_chain(0,1,0,1,0);
  deep_four_recurrence(0,1,0,1,0);
  deep_four_nonlinear(0,1,0,1,0);
  deep_four_unanchored(0,1,0,1,0);
  deep_four(0,1,0,1,1);
  deep_four_global(0,1,0,1,1);
  deep_four_context(0,1,0,1,1);
  deep_four_wrap(0,1,0,1,1);
  deep_four_chain(0,1,0,1,1);
  deep_four_recurrence(0,1,0,1,1);
  deep_four_nonlinear(0,1,0,1,1);
  deep_four_unanchored(0,1,0,1,1);
  deep_four(0,1,0,1,2);
  deep_four_global(0,1,0,1,2);
  deep_four_context(0,1,0,1,2);
  deep_four_wrap(0,1,0,1,2);
  deep_four_chain(0,1,0,1,2);
  deep_four_recurrence(0,1,0,1,2);
  deep_four_nonlinear(0,1,0,1,2);
  deep_four_unanchored(0,1,0,1,2);
  deep_four(0,1,0,2,0);
  deep_four_global(0,1,0,2,0);
  deep_four_context(0,1,0,2,0);
  deep_four_wrap(0,1,0,2,0);
  deep_four_chain(0,1,0,2,0);
  deep_four_recurrence(0,1,0,2,0);
  deep_four_nonlinear(0,1,0,2,0);
  deep_four_unanchored(0,1,0,2,0);
  deep_four(0,1,0,2,1);
  deep_four_global(0,1,0,2,1);
  deep_four_context(0,1,0,2,1);
  deep_four_wrap(0,1,0,2,1);
  deep_four_chain(0,1,0,2,1);
  deep_four_recurrence(0,1,0,2,1);
  deep_four_nonlinear(0,1,0,2,1);
  deep_four_unanchored(0,1,0,2,1);
  deep_four(0,1,0,2,2);
  deep_four_global(0,1,0,2,2);
  deep_four_context(0,1,0,2,2);
  deep_four_wrap(0,1,0,2,2);
  deep_four_chain(0,1,0,2,2);
  deep_four_recurrence(0,1,0,2,2);
  deep_four_nonlinear(0,1,0,2,2);
  deep_four_unanchored(0,1,0,2,2);
  deep_four(0,1,1,0,0);
  deep_four_global(0,1,1,0,0);
  deep_four_context(0,1,1,0,0);
  deep_four_wrap(0,1,1,0,0);
  deep_four_chain(0,1,1,0,0);
  deep_four_recurrence(0,1,1,0,0);
  deep_four_nonlinear(0,1,1,0,0);
  deep_four_unanchored(0,1,1,0,0);
  deep_four(0,1,1,0,1);
  deep_four_global(0,1,1,0,1);
  deep_four_context(0,1,1,0,1);
  deep_four_wrap(0,1,1,0,1);
  deep_four_chain(0,1,1,0,1);
  deep_four_recurrence(0,1,1,0,1);
  deep_four_nonlinear(0,1,1,0,1);
  deep_four_unanchored(0,1,1,0,1);
  deep_four(0,1,1,0,2);
  deep_four_global(0,1,1,0,2);
  deep_four_context(0,1,1,0,2);
  deep_four_wrap(0,1,1,0,2);
  deep_four_chain(0,1,1,0,2);
  deep_four_recurrence(0,1,1,0,2);
  deep_four_nonlinear(0,1,1,0,2);
  deep_four_unanchored(0,1,1,0,2);
  deep_four(0,1,1,1,0);
  deep_four_global(0,1,1,1,0);
  deep_four_context(0,1,1,1,0);
  deep_four_wrap(0,1,1,1,0);
  deep_four_chain(0,1,1,1,0);
  deep_four_recurrence(0,1,1,1,0);
  deep_four_nonlinear(0,1,1,1,0);
  deep_four_unanchored(0,1,1,1,0);
  deep_four(0,1,1,1,1);
  deep_four_global(0,1,1,1,1);
  deep_four_context(0,1,1,1,1);
  deep_four_wrap(0,1,1,1,1);
  deep_four_chain(0,1,1,1,1);
  deep_four_recurrence(0,1,1,1,1);
  deep_four_nonlinear(0,1,1,1,1);
  deep_four_unanchored(0,1,1,1,1);
  deep_four(0,1,1,1,2);
  deep_four_global(0,1,1,1,2);
  deep_four_context(0,1,1,1,2);
  deep_four_wrap(0,1,1,1,2);
  deep_four_chain(0,1,1,1,2);
  deep_four_recurrence(0,1,1,1,2);
  deep_four_nonlinear(0,1,1,1,2);
  deep_four_unanchored(0,1,1,1,2);
  deep_four(0,1,1,2,0);
  deep_four_global(0,1,1,2,0);
  deep_four_context(0,1,1,2,0);
  deep_four_wrap(0,1,1,2,0);
  deep_four_chain(0,1,1,2,0);
  deep_four_recurrence(0,1,1,2,0);
  deep_four_nonlinear(0,1,1,2,0);
  deep_four_unanchored(0,1,1,2,0);
  deep_four(0,1,1,2,1);
  deep_four_global(0,1,1,2,1);
  deep_four_context(0,1,1,2,1);
  deep_four_wrap(0,1,1,2,1);
  deep_four_chain(0,1,1,2,1);
  deep_four_recurrence(0,1,1,2,1);
  deep_four_nonlinear(0,1,1,2,1);
  deep_four_unanchored(0,1,1,2,1);
  deep_four(0,1,1,2,2);
  deep_four_global(0,1,1,2,2);
  deep_four_context(0,1,1,2,2);
  deep_four_wrap(0,1,1,2,2);
  deep_four_chain(0,1,1,2,2);
  deep_four_recurrence(0,1,1,2,2);
  deep_four_nonlinear(0,1,1,2,2);
  deep_four_unanchored(0,1,1,2,2);
  deep_four(0,1,2,0,0);
  deep_four_global(0,1,2,0,0);
  deep_four_context(0,1,2,0,0);
  deep_four_wrap(0,1,2,0,0);
  deep_four_chain(0,1,2,0,0);
  deep_four_recurrence(0,1,2,0,0);
  deep_four_nonlinear(0,1,2,0,0);
  deep_four_unanchored(0,1,2,0,0);
  deep_four(0,1,2,0,1);
  deep_four_global(0,1,2,0,1);
  deep_four_context(0,1,2,0,1);
  deep_four_wrap(0,1,2,0,1);
  deep_four_chain(0,1,2,0,1);
  deep_four_recurrence(0,1,2,0,1);
  deep_four_nonlinear(0,1,2,0,1);
  deep_four_unanchored(0,1,2,0,1);
  deep_four(0,1,2,0,2);
  deep_four_global(0,1,2,0,2);
  deep_four_context(0,1,2,0,2);
  deep_four_wrap(0,1,2,0,2);
  deep_four_chain(0,1,2,0,2);
  deep_four_recurrence(0,1,2,0,2);
  deep_four_nonlinear(0,1,2,0,2);
  deep_four_unanchored(0,1,2,0,2);
  deep_four(0,1,2,1,0);
  deep_four_global(0,1,2,1,0);
  deep_four_context(0,1,2,1,0);
  deep_four_wrap(0,1,2,1,0);
  deep_four_chain(0,1,2,1,0);
  deep_four_recurrence(0,1,2,1,0);
  deep_four_nonlinear(0,1,2,1,0);
  deep_four_unanchored(0,1,2,1,0);
  deep_four(0,1,2,1,1);
  deep_four_global(0,1,2,1,1);
  deep_four_context(0,1,2,1,1);
  deep_four_wrap(0,1,2,1,1);
  deep_four_chain(0,1,2,1,1);
  deep_four_recurrence(0,1,2,1,1);
  deep_four_nonlinear(0,1,2,1,1);
  deep_four_unanchored(0,1,2,1,1);
  deep_four(0,1,2,1,2);
  deep_four_global(0,1,2,1,2);
  deep_four_context(0,1,2,1,2);
  deep_four_wrap(0,1,2,1,2);
  deep_four_chain(0,1,2,1,2);
  deep_four_recurrence(0,1,2,1,2);
  deep_four_nonlinear(0,1,2,1,2);
  deep_four_unanchored(0,1,2,1,2);
  deep_four(0,1,2,2,0);
  deep_four_global(0,1,2,2,0);
  deep_four_context(0,1,2,2,0);
  deep_four_wrap(0,1,2,2,0);
  deep_four_chain(0,1,2,2,0);
  deep_four_recurrence(0,1,2,2,0);
  deep_four_nonlinear(0,1,2,2,0);
  deep_four_unanchored(0,1,2,2,0);
  deep_four(0,1,2,2,1);
  deep_four_global(0,1,2,2,1);
  deep_four_context(0,1,2,2,1);
  deep_four_wrap(0,1,2,2,1);
  deep_four_chain(0,1,2,2,1);
  deep_four_recurrence(0,1,2,2,1);
  deep_four_nonlinear(0,1,2,2,1);
  deep_four_unanchored(0,1,2,2,1);
  deep_four(0,1,2,2,2);
  deep_four_global(0,1,2,2,2);
  deep_four_context(0,1,2,2,2);
  deep_four_wrap(0,1,2,2,2);
  deep_four_chain(0,1,2,2,2);
  deep_four_recurrence(0,1,2,2,2);
  deep_four_nonlinear(0,1,2,2,2);
  deep_four_unanchored(0,1,2,2,2);
  deep_four(0,2,0,0,0);
  deep_four_global(0,2,0,0,0);
  deep_four_context(0,2,0,0,0);
  deep_four_wrap(0,2,0,0,0);
  deep_four_chain(0,2,0,0,0);
  deep_four_recurrence(0,2,0,0,0);
  deep_four_nonlinear(0,2,0,0,0);
  deep_four_unanchored(0,2,0,0,0);
  deep_four(0,2,0,0,1);
  deep_four_global(0,2,0,0,1);
  deep_four_context(0,2,0,0,1);
  deep_four_wrap(0,2,0,0,1);
  deep_four_chain(0,2,0,0,1);
  deep_four_recurrence(0,2,0,0,1);
  deep_four_nonlinear(0,2,0,0,1);
  deep_four_unanchored(0,2,0,0,1);
  deep_four(0,2,0,0,2);
  deep_four_global(0,2,0,0,2);
  deep_four_context(0,2,0,0,2);
  deep_four_wrap(0,2,0,0,2);
  deep_four_chain(0,2,0,0,2);
  deep_four_recurrence(0,2,0,0,2);
  deep_four_nonlinear(0,2,0,0,2);
  deep_four_unanchored(0,2,0,0,2);
  deep_four(0,2,0,1,0);
  deep_four_global(0,2,0,1,0);
  deep_four_context(0,2,0,1,0);
  deep_four_wrap(0,2,0,1,0);
  deep_four_chain(0,2,0,1,0);
  deep_four_recurrence(0,2,0,1,0);
  deep_four_nonlinear(0,2,0,1,0);
  deep_four_unanchored(0,2,0,1,0);
  deep_four(0,2,0,1,1);
  deep_four_global(0,2,0,1,1);
  deep_four_context(0,2,0,1,1);
  deep_four_wrap(0,2,0,1,1);
  deep_four_chain(0,2,0,1,1);
  deep_four_recurrence(0,2,0,1,1);
  deep_four_nonlinear(0,2,0,1,1);
  deep_four_unanchored(0,2,0,1,1);
  deep_four(0,2,0,1,2);
  deep_four_global(0,2,0,1,2);
  deep_four_context(0,2,0,1,2);
  deep_four_wrap(0,2,0,1,2);
  deep_four_chain(0,2,0,1,2);
  deep_four_recurrence(0,2,0,1,2);
  deep_four_nonlinear(0,2,0,1,2);
  deep_four_unanchored(0,2,0,1,2);
  deep_four(0,2,0,2,0);
  deep_four_global(0,2,0,2,0);
  deep_four_context(0,2,0,2,0);
  deep_four_wrap(0,2,0,2,0);
  deep_four_chain(0,2,0,2,0);
  deep_four_recurrence(0,2,0,2,0);
  deep_four_nonlinear(0,2,0,2,0);
  deep_four_unanchored(0,2,0,2,0);
  deep_four(0,2,0,2,1);
  deep_four_global(0,2,0,2,1);
  deep_four_context(0,2,0,2,1);
  deep_four_wrap(0,2,0,2,1);
  deep_four_chain(0,2,0,2,1);
  deep_four_recurrence(0,2,0,2,1);
  deep_four_nonlinear(0,2,0,2,1);
  deep_four_unanchored(0,2,0,2,1);
  deep_four(0,2,0,2,2);
  deep_four_global(0,2,0,2,2);
  deep_four_context(0,2,0,2,2);
  deep_four_wrap(0,2,0,2,2);
  deep_four_chain(0,2,0,2,2);
  deep_four_recurrence(0,2,0,2,2);
  deep_four_nonlinear(0,2,0,2,2);
  deep_four_unanchored(0,2,0,2,2);
  deep_four(0,2,1,0,0);
  deep_four_global(0,2,1,0,0);
  deep_four_context(0,2,1,0,0);
  deep_four_wrap(0,2,1,0,0);
  deep_four_chain(0,2,1,0,0);
  deep_four_recurrence(0,2,1,0,0);
  deep_four_nonlinear(0,2,1,0,0);
  deep_four_unanchored(0,2,1,0,0);
  deep_four(0,2,1,0,1);
  deep_four_global(0,2,1,0,1);
  deep_four_context(0,2,1,0,1);
  deep_four_wrap(0,2,1,0,1);
  deep_four_chain(0,2,1,0,1);
  deep_four_recurrence(0,2,1,0,1);
  deep_four_nonlinear(0,2,1,0,1);
  deep_four_unanchored(0,2,1,0,1);
  deep_four(0,2,1,0,2);
  deep_four_global(0,2,1,0,2);
  deep_four_context(0,2,1,0,2);
  deep_four_wrap(0,2,1,0,2);
  deep_four_chain(0,2,1,0,2);
  deep_four_recurrence(0,2,1,0,2);
  deep_four_nonlinear(0,2,1,0,2);
  deep_four_unanchored(0,2,1,0,2);
  deep_four(0,2,1,1,0);
  deep_four_global(0,2,1,1,0);
  deep_four_context(0,2,1,1,0);
  deep_four_wrap(0,2,1,1,0);
  deep_four_chain(0,2,1,1,0);
  deep_four_recurrence(0,2,1,1,0);
  deep_four_nonlinear(0,2,1,1,0);
  deep_four_unanchored(0,2,1,1,0);
  deep_four(0,2,1,1,1);
  deep_four_global(0,2,1,1,1);
  deep_four_context(0,2,1,1,1);
  deep_four_wrap(0,2,1,1,1);
  deep_four_chain(0,2,1,1,1);
  deep_four_recurrence(0,2,1,1,1);
  deep_four_nonlinear(0,2,1,1,1);
  deep_four_unanchored(0,2,1,1,1);
  deep_four(0,2,1,1,2);
  deep_four_global(0,2,1,1,2);
  deep_four_context(0,2,1,1,2);
  deep_four_wrap(0,2,1,1,2);
  deep_four_chain(0,2,1,1,2);
  deep_four_recurrence(0,2,1,1,2);
  deep_four_nonlinear(0,2,1,1,2);
  deep_four_unanchored(0,2,1,1,2);
  deep_four(0,2,1,2,0);
  deep_four_global(0,2,1,2,0);
  deep_four_context(0,2,1,2,0);
  deep_four_wrap(0,2,1,2,0);
  deep_four_chain(0,2,1,2,0);
  deep_four_recurrence(0,2,1,2,0);
  deep_four_nonlinear(0,2,1,2,0);
  deep_four_unanchored(0,2,1,2,0);
  deep_four(0,2,1,2,1);
  deep_four_global(0,2,1,2,1);
  deep_four_context(0,2,1,2,1);
  deep_four_wrap(0,2,1,2,1);
  deep_four_chain(0,2,1,2,1);
  deep_four_recurrence(0,2,1,2,1);
  deep_four_nonlinear(0,2,1,2,1);
  deep_four_unanchored(0,2,1,2,1);
  deep_four(0,2,1,2,2);
  deep_four_global(0,2,1,2,2);
  deep_four_context(0,2,1,2,2);
  deep_four_wrap(0,2,1,2,2);
  deep_four_chain(0,2,1,2,2);
  deep_four_recurrence(0,2,1,2,2);
  deep_four_nonlinear(0,2,1,2,2);
  deep_four_unanchored(0,2,1,2,2);
  deep_four(0,2,2,0,0);
  deep_four_global(0,2,2,0,0);
  deep_four_context(0,2,2,0,0);
  deep_four_wrap(0,2,2,0,0);
  deep_four_chain(0,2,2,0,0);
  deep_four_recurrence(0,2,2,0,0);
  deep_four_nonlinear(0,2,2,0,0);
  deep_four_unanchored(0,2,2,0,0);
  deep_four(0,2,2,0,1);
  deep_four_global(0,2,2,0,1);
  deep_four_context(0,2,2,0,1);
  deep_four_wrap(0,2,2,0,1);
  deep_four_chain(0,2,2,0,1);
  deep_four_recurrence(0,2,2,0,1);
  deep_four_nonlinear(0,2,2,0,1);
  deep_four_unanchored(0,2,2,0,1);
  deep_four(0,2,2,0,2);
  deep_four_global(0,2,2,0,2);
  deep_four_context(0,2,2,0,2);
  deep_four_wrap(0,2,2,0,2);
  deep_four_chain(0,2,2,0,2);
  deep_four_recurrence(0,2,2,0,2);
  deep_four_nonlinear(0,2,2,0,2);
  deep_four_unanchored(0,2,2,0,2);
  deep_four(0,2,2,1,0);
  deep_four_global(0,2,2,1,0);
  deep_four_context(0,2,2,1,0);
  deep_four_wrap(0,2,2,1,0);
  deep_four_chain(0,2,2,1,0);
  deep_four_recurrence(0,2,2,1,0);
  deep_four_nonlinear(0,2,2,1,0);
  deep_four_unanchored(0,2,2,1,0);
  deep_four(0,2,2,1,1);
  deep_four_global(0,2,2,1,1);
  deep_four_context(0,2,2,1,1);
  deep_four_wrap(0,2,2,1,1);
  deep_four_chain(0,2,2,1,1);
  deep_four_recurrence(0,2,2,1,1);
  deep_four_nonlinear(0,2,2,1,1);
  deep_four_unanchored(0,2,2,1,1);
  deep_four(0,2,2,1,2);
  deep_four_global(0,2,2,1,2);
  deep_four_context(0,2,2,1,2);
  deep_four_wrap(0,2,2,1,2);
  deep_four_chain(0,2,2,1,2);
  deep_four_recurrence(0,2,2,1,2);
  deep_four_nonlinear(0,2,2,1,2);
  deep_four_unanchored(0,2,2,1,2);
  deep_four(0,2,2,2,0);
  deep_four_global(0,2,2,2,0);
  deep_four_context(0,2,2,2,0);
  deep_four_wrap(0,2,2,2,0);
  deep_four_chain(0,2,2,2,0);
  deep_four_recurrence(0,2,2,2,0);
  deep_four_nonlinear(0,2,2,2,0);
  deep_four_unanchored(0,2,2,2,0);
  deep_four(0,2,2,2,1);
  deep_four_global(0,2,2,2,1);
  deep_four_context(0,2,2,2,1);
  deep_four_wrap(0,2,2,2,1);
  deep_four_chain(0,2,2,2,1);
  deep_four_recurrence(0,2,2,2,1);
  deep_four_nonlinear(0,2,2,2,1);
  deep_four_unanchored(0,2,2,2,1);
  deep_four(0,2,2,2,2);
  deep_four_global(0,2,2,2,2);
  deep_four_context(0,2,2,2,2);
  deep_four_wrap(0,2,2,2,2);
  deep_four_chain(0,2,2,2,2);
  deep_four_recurrence(0,2,2,2,2);
  deep_four_nonlinear(0,2,2,2,2);
  deep_four_unanchored(0,2,2,2,2);
  deep_four(0,0,-2147483648,-2147483648,-2147483648);
  deep_four(1,2,2,2,2);
  deep_four(0,4,4,4,4);
  deep_four(0,2,0,-2147483648,-2147483648);
  deep_four(0,2,2,0,-2147483648);
  deep_four(0,2,2,2,0);
  deep_four(0,1,1,1,5);
  deep_four_global(0,0,-2147483648,-2147483648,-2147483648);
  deep_four_global(1,2,2,2,2);
  deep_four_global(0,4,4,4,4);
  deep_four_global(0,2,0,-2147483648,-2147483648);
  deep_four_global(0,2,2,0,-2147483648);
  deep_four_global(0,2,2,2,0);
  deep_four_global(0,1,1,1,5);
  deep_four_context(0,0,-2147483648,-2147483648,-2147483648);
  deep_four_context(1,2,2,2,2);
  deep_four_context(0,4,4,4,4);
  deep_four_context(0,2,0,-2147483648,-2147483648);
  deep_four_context(0,2,2,0,-2147483648);
  deep_four_context(0,2,2,2,0);
  deep_four_context(0,1,1,1,5);
  deep_four_wrap(0,0,-2147483648,-2147483648,-2147483648);
  deep_four_wrap(1,2,2,2,2);
  deep_four_wrap(0,4,4,4,4);
  deep_four_wrap(0,2,0,-2147483648,-2147483648);
  deep_four_wrap(0,2,2,0,-2147483648);
  deep_four_wrap(0,2,2,2,0);
  deep_four_wrap(0,1,1,1,5);
  deep_four_chain(0,0,-2147483648,-2147483648,-2147483648);
  deep_four_chain(1,2,2,2,2);
  deep_four_chain(0,2,0,-2147483648,-2147483648);
  deep_four_chain(0,2,2,0,-2147483648);
  deep_four_chain(0,2,2,2,0);
  deep_four_chain(0,1,1,1,5);
  deep_four_recurrence(0,0,-2147483648,-2147483648,-2147483648);
  deep_four_recurrence(1,2,2,2,2);
  deep_four_recurrence(0,2,0,-2147483648,-2147483648);
  deep_four_recurrence(0,2,2,0,-2147483648);
  deep_four_recurrence(0,2,2,2,0);
  deep_four_recurrence(0,1,1,1,5);
  deep_four_nonlinear(0,0,-2147483648,-2147483648,-2147483648);
  deep_four_nonlinear(1,2,2,2,2);
  deep_four_nonlinear(0,4,4,4,4);
  deep_four_nonlinear(0,2,0,-2147483648,-2147483648);
  deep_four_nonlinear(0,2,2,0,-2147483648);
  deep_four_nonlinear(0,2,2,2,0);
  deep_four_unanchored(0,0,-2147483648,-2147483648,-2147483648);
  deep_four_unanchored(1,2,2,2,2);
  deep_four_unanchored(0,2,0,-2147483648,-2147483648);
  deep_four_unanchored(0,2,2,0,-2147483648);
  deep_four_unanchored(0,2,2,2,0);
  deep_four_undef(0,0,0,99,-2147483648);
  deep_four_undef(0,2,2,0,0);
  deep_four_undef(0,1,0,99,2147483647);
  deep_five(0,0,-2147483648,-2147483648,-2147483648,-2147483648);
  deep_five(1,2,2,2,2,2);
  deep_five(0,1,1,1,1,1);
  deep_five(0,2,2,2,2,2);
  deep_five(0,3,3,3,3,3);
  deep_five(0,2,0,-2147483648,-2147483648,-2147483648);
  deep_five(0,2,2,0,-2147483648,-2147483648);
  deep_five(0,2,2,2,0,-2147483648);
  deep_five(0,2,2,2,2,0);
  deep_five(0,1,1,1,1,4);
  deep_six(0,0,-2147483648,-2147483648,-2147483648,-2147483648,-2147483648);
  deep_six(1,2,2,2,2,2,2);
  deep_six(0,1,1,1,1,1,1);
  deep_six(0,2,2,2,2,2,2);
  deep_six(0,3,3,3,3,3,3);
  deep_six(0,2,0,-2147483648,-2147483648,-2147483648,-2147483648);
  deep_six(0,2,2,0,-2147483648,-2147483648,-2147483648);
  deep_six(0,2,2,2,0,-2147483648,-2147483648);
  deep_six(0,2,2,2,2,0,-2147483648);
  deep_six(0,2,2,2,2,2,0);
  deep_six(0,1,1,1,1,1,4);
  deep_eight(0,0,-2147483648,-2147483648,-2147483648,-2147483648,-2147483648,-2147483648,-2147483648);
  deep_eight(1,2,2,2,2,2,2,2,2);
  deep_eight(0,1,1,1,1,1,1,1,1);
  deep_eight(0,2,2,2,2,2,2,2,2);
  deep_eight(0,2,2,2,2,2,2,2,2);
  deep_eight(0,2,0,-2147483648,-2147483648,-2147483648,-2147483648,-2147483648,-2147483648);
  deep_eight(0,2,2,0,-2147483648,-2147483648,-2147483648,-2147483648,-2147483648);
  deep_eight(0,2,2,2,0,-2147483648,-2147483648,-2147483648,-2147483648);
  deep_eight(0,2,2,2,2,0,-2147483648,-2147483648,-2147483648);
  deep_eight(0,2,2,2,2,2,0,-2147483648,-2147483648);
  deep_eight(0,2,2,2,2,2,2,0,-2147483648);
  deep_eight(0,2,2,2,2,2,2,2,0);
  deep_eight(0,1,1,1,1,1,1,1,3);
  deep_nine(0,0,-2147483648,-2147483648,-2147483648,-2147483648,-2147483648,-2147483648,-2147483648,-2147483648);
  deep_nine(1,2,2,2,2,2,2,2,2,2);
  deep_nine(0,1,1,1,1,1,1,1,1,1);
  deep_nine(0,2,2,2,2,2,2,2,2,2);
  deep_nine(0,2,2,2,2,2,2,2,2,2);
  deep_nine(0,2,0,-2147483648,-2147483648,-2147483648,-2147483648,-2147483648,-2147483648,-2147483648);
  deep_nine(0,2,2,0,-2147483648,-2147483648,-2147483648,-2147483648,-2147483648,-2147483648);
  deep_nine(0,2,2,2,0,-2147483648,-2147483648,-2147483648,-2147483648,-2147483648);
  deep_nine(0,2,2,2,2,0,-2147483648,-2147483648,-2147483648,-2147483648);
  deep_nine(0,2,2,2,2,2,0,-2147483648,-2147483648,-2147483648);
  deep_nine(0,2,2,2,2,2,2,0,-2147483648,-2147483648);
  deep_nine(0,2,2,2,2,2,2,2,0,-2147483648);
  deep_nine(0,2,2,2,2,2,2,2,2,0);
  deep_nine(0,1,1,1,1,1,1,1,1,3);
  return 0;
}
