#include <stdio.h>
int global_sequence[120];
void emit(char *tag, int *a, int i, int j) {
  int k; printf("%s %d %d",tag,i,j);
  for(k=0;k<120;++k) printf(" %d",a[k]);
  printf("\n");
}
void sequence_pair(int i,int n,int m) {
  int a[120],j=99,k;
  for(k=0;k<120;++k) a[k]=-999;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      a[i*10+j]=i*37+j+7;
      a[i*10+j]=i*11+j+19;
    }
  }
  emit("pair",a,i,j);
}
void sequence_triple(int i,int n,int m) {
  int a[120],j=99,k;
  for(k=0;k<120;++k) a[k]=-999;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      a[i*10+j]=i*37+j+7;
      a[i*10+j]=i*11+j+19;
      a[i*10+j]=i*23+j+3;
    }
  }
  emit("triple",a,i,j);
}
void sequence_duplicate(int i,int n,int m) {
  int a[120],j=99,k;
  for(k=0;k<120;++k) a[k]=-999;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      a[i*10+j]=i*37+j+7;
      a[i*10+j]=i*37+j+7;
      a[i*10+j]=i*11+j+19;
      a[i*10+j]=i*37+j+7;
    }
  }
  emit("duplicate",a,i,j);
}
void sequence_goto(int n,int m) {
  int a[120],i=0,j=99,k;
  for(k=0;k<120;++k) a[k]=-999;
  goto work;
work:
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      a[i*10+j]=i*37+j+7;
      a[i*10+j]=i*11+j+19;
    }
  }
  emit("goto",a,i,j);
}
void sequence_global(int n,int m) {
  int i=0,j=99,k;
  for(k=0;k<120;++k) global_sequence[k]=-999;
  for(;i<n;++i) {
    for(j=0;j<m;++j) {
      global_sequence[i*10+j]=i*37+j+7;
      global_sequence[i*10+j]=i*11+j+19;
    }
  }
  emit("global",global_sequence,i,j);
}
void sequence_enclosing(int n,int m) {
  int a[120],i=0,j=99,k,repeat;
  for(k=0;k<120;++k) a[k]=-999;
  for(repeat=0;repeat<2;++repeat) {
    for(i=0;i<n;++i) {
    for(j=0;j<m;++j) {
      a[i*10+j]=i*37+j+7;
      a[i*10+j]=i*11+j+19;
    }
  }
  }
  emit("enclosing",a,i,j);
}
int sequence_unread_bound(int i,int n) {
  int a[120],j=99,m;
  for(;i<n;++i) { for(j=0;j<m;++j) {
    a[i*10+j]=i*37+j+7; a[i*10+j]=i*11+j+19;
  }}
  return j;
}
void sequence_other_layout(int i,int n,int m) {
  int a[105],j=99,k;
  for(k=0;k<105;++k) a[k]=-999;
  for(;i<n;++i) { for(j=0;j<m;++j) {
    a[i*7+j]=i*37+j+7; a[i*7+j]=i*11+j+19;
  }}
  printf("other %d %d",i,j);
  for(k=0;k<105;++k) printf(" %d",a[k]);
  printf("\n");
}
void sequence_update(int n,int m) {
  int a[120],i=0,j=99,k;
  for(k=0;k<120;++k) a[k]=-999;
  for(;i<n;++i) { for(j=0;j<m;++j) {
    a[i*10+j]=i*37+j+7; a[i*10+j]=a[i*10+j]*2+i*11+j+19;
  }}
  emit("update",a,i,j);
}
void sequence_two_arrays(int n,int m) {
  int a[120],b[120],i=0,j=99,k;
  for(k=0;k<120;++k) { a[k]=-999; b[k]=-999; }
  for(;i<n;++i) { for(j=0;j<m;++j) {
    a[i*10+j]=i*37+j+7; b[i*10+j]=i*11+j+19;
  }}
  emit("array-a",a,i,j); emit("array-b",b,i,j);
}
void sequence_offset(int n,int m) {
  int a[120],i=0,j=99,k;
  for(k=0;k<120;++k) a[k]=-999;
  for(;i<n;++i) { for(j=0;j<m;++j) {
    a[i*10+j]=i*37+j+7; a[i*10+j+1]=i*11+j+19;
  }}
  emit("offset",a,i,j);
}
void sequence_temp_write(int n,int m) {
  int a[120],i=0,j=99,k;
  for(k=0;k<120;++k) a[k]=-999;
  for(;i<n;++i) { for(j=0;j<m;++j) {
    a[i*10+j]=i*37+j+7; k=i; a[i*10+j]=i*11+j+19;
  }}
  emit("temp",a,i,j); printf("temp-k %d\n",k);
}
int main(void) {
  int n,m;
  for(n=0;n<=12;++n) { for(m=0;m<=10;++m) {
    sequence_pair(0,n,m); sequence_pair(2,n,m);
    sequence_triple(0,n,m); sequence_duplicate(0,n,m);
    sequence_goto(n,m); sequence_global(n,m); sequence_enclosing(n,m);
  }}
  for(n=0;n<=15;++n) { for(m=0;m<=7;++m) sequence_other_layout(0,n,m); }
  sequence_pair(0,-1,10); sequence_pair(0,5,-1);
  sequence_update(12,10); sequence_two_arrays(12,10); sequence_offset(10,9); sequence_temp_write(12,10);
  printf("unread %d %d\n",sequence_unread_bound(0,0),sequence_unread_bound(2,1));
  return 0;
}
