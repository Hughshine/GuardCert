#include <stdio.h>
#include <limits.h>
int global_cut[120];
void emit(char *tag, int *a, int i, int j) {
  int k;
  printf("%s %d %d", tag, i, j);
  for (k = 0; k < 120; ++k) printf(" %d", a[k]);
  printf("\n");
}
void cut_triangle(int i, int n, int m) {
  int a[120], j=99, k;
  for (k=0; k<120; ++k) a[k]=-999;
  for (; i<n; ++i) {
    for (j=0; j<m; ++j) {
      if (i+j<=6) a[i*10+j]=i*37+j+7;
    }
  }
  emit("triangle",a,i,j);
}
void cut_skew(int i, int n, int m) {
  int a[120], j=99, k;
  for (k=0; k<120; ++k) a[k]=-999;
  for (; i<n; ++i) {
    for (j=0; j<m; ++j) {
      if (2*i+3*j<=14) a[i*10+j]=i*37+j+7;
    }
  }
  emit("skew",a,i,j);
}
void cut_row(int i, int n, int m) {
  int a[120], j=99, k;
  for (k=0; k<120; ++k) a[k]=-999;
  for (; i<n; ++i) {
    for (j=0; j<m; ++j) {
      if (i<=3) a[i*10+j]=i*37+j+7;
    }
  }
  emit("row",a,i,j);
}
void cut_column(int i, int n, int m) {
  int a[120], j=99, k;
  for (k=0; k<120; ++k) a[k]=-999;
  for (; i<n; ++i) {
    for (j=0; j<m; ++j) {
      if (j<=4) a[i*10+j]=i*37+j+7;
    }
  }
  emit("column",a,i,j);
}
void cut_single(int i, int n, int m) {
  int a[120], j=99, k;
  for (k=0; k<120; ++k) a[k]=-999;
  for (; i<n; ++i) {
    for (j=0; j<m; ++j) {
      if (i+j<=0) a[i*10+j]=i*37+j+7;
    }
  }
  emit("single",a,i,j);
}
void cut_goto(int n, int m) {
  int a[120], i=0, j=99, k;
  for (k=0; k<120; ++k) a[k]=-999;
  goto work;
work:
  for (; i<n; ++i) {
    for (j=0; j<m; ++j) {
      if (i+j<=6) a[i*10+j]=i*37+j+7;
    }
  }
  emit("goto",a,i,j);
}
void cut_global(int n, int m) {
  int i=0, j=99, k;
  for (k=0; k<120; ++k) global_cut[k]=-999;
  for (; i<n; ++i) {
    for (j=0; j<m; ++j) {
      if (i+j<=6) global_cut[i*10+j]=i*37+j+7;
    }
  }
  emit("global",global_cut,i,j);
}
void cut_enclosing(int n, int m) {
  int a[120], i=0, j=99, k, repeat;
  for (k=0; k<120; ++k) a[k]=-999;
  for (repeat=0; repeat<2; ++repeat) {
    for (i=0; i<n; ++i) {
      for (j=0; j<m; ++j) {
        if (i+j<=6) a[i*10+j]=i*37+j+7;
      }
    }
  }
  emit("enclosing",a,i,j);
}
int cut_unread_bound(int i, int n) {
  int a[120], j=99, m;
  for (; i<n; ++i) {
    for (j=0; j<m; ++j) {
      if (i+j<=6) a[i*10+j]=i*37+j+7;
    }
  }
  return j;
}
void cut_empty(int n, int m) {
  int a[120], i=0, j=99, k;
  for (k=0; k<120; ++k) a[k]=-999;
  for (; i<n; ++i) {
    for (j=0; j<m; ++j) {
      if (i+j<=-1) a[i*10+j]=i*37+j+7;
    }
  }
  emit("empty",a,i,j);
}
void cut_nonlinear(int n, int m) {
  int a[120], i=0, j=99, k;
  for (k=0; k<120; ++k) a[k]=-999;
  for (; i<n; ++i) {
    for (j=0; j<m; ++j) {
      if (i*j<=6) a[i*10+j]=i*37+j+7;
    }
  }
  emit("nonlinear",a,i,j);
}
void cut_unsigned(int n, int m) {
  int a[120], i=0, j=99, k;
  for (k=0; k<120; ++k) a[k]=-999;
  for (; i<n; ++i) {
    for (j=0; j<m; ++j) {
      if ((unsigned)(i+j)<=6U) a[i*10+j]=i*37+j+7;
    }
  }
  emit("unsigned",a,i,j);
}
void cut_overflow_condition(int n, int m) {
  int a[120], i=0, j=99, k;
  for (k=0; k<120; ++k) a[k]=-999;
  for (; i<n; ++i) {
    for (j=0; j<m; ++j) {
      if (INT_MAX*i+j<=6) a[i*10+j]=i*37+j+7;
    }
  }
  emit("overflow",a,i,j);
}
int main(void) {
  int n,m;
  for (n=0; n<=12; ++n) {
    for (m=0; m<=10; ++m) {
      cut_triangle(0,n,m); cut_triangle(2,n,m);
      cut_skew(0,n,m); cut_row(0,n,m); cut_column(0,n,m); cut_single(0,n,m);
      cut_goto(n,m); cut_global(n,m); cut_enclosing(n,m);
    }
  }
  cut_triangle(0,-1,10); cut_triangle(0,5,-1);
  cut_empty(12,10); cut_nonlinear(12,10); cut_unsigned(12,10);
  cut_overflow_condition(1,10);
  printf("unread %d %d\n",cut_unread_bound(0,0),cut_unread_bound(2,1));
  return 0;
}
