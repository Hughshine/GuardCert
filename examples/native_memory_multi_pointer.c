#include <stdio.h>

int final_i, final_j;

void multi_copy(int *p, int *q, int *r, int start, int n, int m, int alpha, int beta) {
  int i, j;
  i = start; j = 77;
  for (; i<n; i++) {
    for (j=0; j<m; j++) {
      p[8*i+j] = q[8*i+j]*alpha+beta;
    }
  }
  final_i = i; final_j = j;
}

void multi_combine(int *p, int *q, int *r, int start, int n, int m, int alpha, int beta) {
  int i, j;
  i = start; j = 77;
  for (; i<n; i++) {
    for (j=0; j<m; j++) {
      p[8*i+j] = q[8*i+j]*alpha+r[8*i+j]*beta+i*j;
    }
  }
  final_i = i; final_j = j;
}

void multi_chain(int *p, int *q, int *r, int start, int n, int m, int alpha, int beta) {
  int i, j;
  i = start; j = 77;
  for (; i<n; i++) {
    for (j=0; j<m; j++) {
      p[8*i+j] = q[8*i+j]*alpha+beta;
      q[8*i+j+1] = p[8*i+j]+q[8*i+j+1]*beta;
    }
  }
  final_i = i; final_j = j;
}

void multi_reflected(int *p, int *q, int *r, int start, int n, int m, int alpha, int beta) {
  int i, j;
  i = start; j = 77;
  for (; i<n; i++) {
    for (j=0; j<m; j++) {
      p[8*i+j] = q[63-8*i-j]*alpha+beta;
    }
  }
  final_i = i; final_j = j;
}

void multi_context(int *p, int *q, int *r, int start, int n, int m, int alpha, int beta) {
  int i, j;
  i = start; j = 77;
  for (; i<n; i++) {
    for (j=0; j<m; j++) {
      p[8*i+j] = q[8*i+j]*alpha+p[8*i+j]+beta;
    }
  }
  i = start;
  for (; i<n; i++) {
    for (j=0; j<m; j++) {
      p[8*i+j] = q[8*i+j]*alpha+p[8*i+j]+beta;
    }
  }
  final_i = i; final_j = j;
}

void multi_undef(int *p, int *q, int *r, int start, int n, int m, int alpha, int beta) {
  int i, j;
  int unused_alpha;
  i = start; j = 77;
  for (; i<n; i++) {
    for (j=0; j<m; j++) {
      p[8*i+j] = q[8*i+j]*unused_alpha;
    }
  }
  final_i = i; final_j = j;
}

void multi_tiny(int *p, int *q, int *r, int start, int n, int m, int alpha, int beta) {
  int i, j;
  i = start; j = 77;
  for (; i<n; i++) {
    for (j=0; j<m; j++) {
      p[2*i+j] = q[2*i+j]*alpha+beta;
    }
  }
  final_i = i; final_j = j;
}

void run(const char *name, void (*kernel)(int *,int *,int *,int,int,int,int,int),
  int kind, int p_offset, int q_offset, int start, int n, int m, int alpha, int beta) {
  int a[256], b[256], c[256]; int x; int *p, *q, *r;
  for (x=0; x<256; x++) { a[x]=3*x+1; b[x]=5*x+7; c[x]=7*x+11; }
  p=a+p_offset; q=(kind==1?a:b)+q_offset; r=(kind==2?b+q_offset:c);
  if (kind==3) { p=0; q=0; r=0; }
  kernel(p,q,r,start,n,m,alpha,beta);
  printf("%s %d %d %d %d %d %d %d %d %d %d",name,kind,p_offset,q_offset,start,n,m,alpha,beta,final_i,final_j);
  for (x=0; x<256; x++) printf(" %d %d %d",a[x],b[x],c[x]);
  printf("\n");
}
void run_tiny(int start,int n,int m,int alpha,int beta) {
  int a[2], b[2]; a[0]=1; a[1]=4; b[0]=7; b[1]=12;
  multi_tiny(a,b,0,start,n,m,alpha,beta);
  printf("multi_tiny %d %d %d %d %d %d %d %d %d %d %d\n",start,n,m,alpha,beta,final_i,final_j,a[0],a[1],b[0],b[1]);
}
int main(void) {

  run("multi_copy",multi_copy,0,0,0,0,1,2,-7,11);
  run("multi_copy",multi_copy,0,0,0,0,2,1,-7,11);
  run("multi_copy",multi_copy,0,0,0,0,2,3,-7,11);
  run("multi_copy",multi_copy,0,0,0,0,3,2,-7,11);
  run("multi_copy",multi_copy,0,0,0,0,3,3,-7,11);
  run("multi_copy",multi_copy,0,0,0,0,4,4,-7,11);
  run("multi_copy",multi_copy,0,0,0,0,5,3,-7,11);
  run("multi_copy",multi_copy,0,3,17,0,1,2,-7,11);
  run("multi_copy",multi_copy,0,3,17,0,2,1,-7,11);
  run("multi_copy",multi_copy,0,3,17,0,2,3,-7,11);
  run("multi_copy",multi_copy,0,3,17,0,3,2,-7,11);
  run("multi_copy",multi_copy,0,3,17,0,3,3,-7,11);
  run("multi_copy",multi_copy,0,3,17,0,4,4,-7,11);
  run("multi_copy",multi_copy,0,3,17,0,5,3,-7,11);
  run("multi_copy",multi_copy,1,0,0,0,1,2,-7,11);
  run("multi_copy",multi_copy,1,0,0,0,2,1,-7,11);
  run("multi_copy",multi_copy,1,0,0,0,2,3,-7,11);
  run("multi_copy",multi_copy,1,0,0,0,3,2,-7,11);
  run("multi_copy",multi_copy,1,0,0,0,3,3,-7,11);
  run("multi_copy",multi_copy,1,0,0,0,4,4,-7,11);
  run("multi_copy",multi_copy,1,0,0,0,5,3,-7,11);
  run("multi_copy",multi_copy,1,0,1,0,1,2,-7,11);
  run("multi_copy",multi_copy,1,0,1,0,2,1,-7,11);
  run("multi_copy",multi_copy,1,0,1,0,2,3,-7,11);
  run("multi_copy",multi_copy,1,0,1,0,3,2,-7,11);
  run("multi_copy",multi_copy,1,0,1,0,3,3,-7,11);
  run("multi_copy",multi_copy,1,0,1,0,4,4,-7,11);
  run("multi_copy",multi_copy,1,0,1,0,5,3,-7,11);
  run("multi_copy",multi_copy,1,0,4,0,1,2,-7,11);
  run("multi_copy",multi_copy,1,0,4,0,2,1,-7,11);
  run("multi_copy",multi_copy,1,0,4,0,2,3,-7,11);
  run("multi_copy",multi_copy,1,0,4,0,3,2,-7,11);
  run("multi_copy",multi_copy,1,0,4,0,3,3,-7,11);
  run("multi_copy",multi_copy,1,0,4,0,4,4,-7,11);
  run("multi_copy",multi_copy,1,0,4,0,5,3,-7,11);
  run("multi_copy",multi_copy,1,3,40,0,1,2,-7,11);
  run("multi_copy",multi_copy,1,3,40,0,2,1,-7,11);
  run("multi_copy",multi_copy,1,3,40,0,2,3,-7,11);
  run("multi_copy",multi_copy,1,3,40,0,3,2,-7,11);
  run("multi_copy",multi_copy,1,3,40,0,3,3,-7,11);
  run("multi_copy",multi_copy,1,3,40,0,4,4,-7,11);
  run("multi_copy",multi_copy,1,3,40,0,5,3,-7,11);
  run("multi_copy",multi_copy,2,0,0,0,1,2,-7,11);
  run("multi_copy",multi_copy,2,0,0,0,2,1,-7,11);
  run("multi_copy",multi_copy,2,0,0,0,2,3,-7,11);
  run("multi_copy",multi_copy,2,0,0,0,3,2,-7,11);
  run("multi_copy",multi_copy,2,0,0,0,3,3,-7,11);
  run("multi_copy",multi_copy,2,0,0,0,4,4,-7,11);
  run("multi_copy",multi_copy,2,0,0,0,5,3,-7,11);
  run("multi_copy",multi_copy,0,0,0,2,3,3,-2147483647-1,2147483647);
  run("multi_copy",multi_copy,3,0,0,0,0,3,-2147483647-1,2147483647);
  run("multi_copy",multi_copy,3,0,0,0,3,0,-2147483647-1,2147483647);
  run("multi_copy",multi_copy,3,0,0,0,-1,3,-2147483647-1,2147483647);
  run("multi_copy",multi_copy,3,0,0,0,3,-1,-2147483647-1,2147483647);
  run("multi_combine",multi_combine,0,0,0,0,1,2,-7,11);
  run("multi_combine",multi_combine,0,0,0,0,2,1,-7,11);
  run("multi_combine",multi_combine,0,0,0,0,2,3,-7,11);
  run("multi_combine",multi_combine,0,0,0,0,3,2,-7,11);
  run("multi_combine",multi_combine,0,0,0,0,3,3,-7,11);
  run("multi_combine",multi_combine,0,0,0,0,4,4,-7,11);
  run("multi_combine",multi_combine,0,0,0,0,5,3,-7,11);
  run("multi_combine",multi_combine,0,3,17,0,1,2,-7,11);
  run("multi_combine",multi_combine,0,3,17,0,2,1,-7,11);
  run("multi_combine",multi_combine,0,3,17,0,2,3,-7,11);
  run("multi_combine",multi_combine,0,3,17,0,3,2,-7,11);
  run("multi_combine",multi_combine,0,3,17,0,3,3,-7,11);
  run("multi_combine",multi_combine,0,3,17,0,4,4,-7,11);
  run("multi_combine",multi_combine,0,3,17,0,5,3,-7,11);
  run("multi_combine",multi_combine,1,0,0,0,1,2,-7,11);
  run("multi_combine",multi_combine,1,0,0,0,2,1,-7,11);
  run("multi_combine",multi_combine,1,0,0,0,2,3,-7,11);
  run("multi_combine",multi_combine,1,0,0,0,3,2,-7,11);
  run("multi_combine",multi_combine,1,0,0,0,3,3,-7,11);
  run("multi_combine",multi_combine,1,0,0,0,4,4,-7,11);
  run("multi_combine",multi_combine,1,0,0,0,5,3,-7,11);
  run("multi_combine",multi_combine,1,0,1,0,1,2,-7,11);
  run("multi_combine",multi_combine,1,0,1,0,2,1,-7,11);
  run("multi_combine",multi_combine,1,0,1,0,2,3,-7,11);
  run("multi_combine",multi_combine,1,0,1,0,3,2,-7,11);
  run("multi_combine",multi_combine,1,0,1,0,3,3,-7,11);
  run("multi_combine",multi_combine,1,0,1,0,4,4,-7,11);
  run("multi_combine",multi_combine,1,0,1,0,5,3,-7,11);
  run("multi_combine",multi_combine,1,0,4,0,1,2,-7,11);
  run("multi_combine",multi_combine,1,0,4,0,2,1,-7,11);
  run("multi_combine",multi_combine,1,0,4,0,2,3,-7,11);
  run("multi_combine",multi_combine,1,0,4,0,3,2,-7,11);
  run("multi_combine",multi_combine,1,0,4,0,3,3,-7,11);
  run("multi_combine",multi_combine,1,0,4,0,4,4,-7,11);
  run("multi_combine",multi_combine,1,0,4,0,5,3,-7,11);
  run("multi_combine",multi_combine,1,3,40,0,1,2,-7,11);
  run("multi_combine",multi_combine,1,3,40,0,2,1,-7,11);
  run("multi_combine",multi_combine,1,3,40,0,2,3,-7,11);
  run("multi_combine",multi_combine,1,3,40,0,3,2,-7,11);
  run("multi_combine",multi_combine,1,3,40,0,3,3,-7,11);
  run("multi_combine",multi_combine,1,3,40,0,4,4,-7,11);
  run("multi_combine",multi_combine,1,3,40,0,5,3,-7,11);
  run("multi_combine",multi_combine,2,0,0,0,1,2,-7,11);
  run("multi_combine",multi_combine,2,0,0,0,2,1,-7,11);
  run("multi_combine",multi_combine,2,0,0,0,2,3,-7,11);
  run("multi_combine",multi_combine,2,0,0,0,3,2,-7,11);
  run("multi_combine",multi_combine,2,0,0,0,3,3,-7,11);
  run("multi_combine",multi_combine,2,0,0,0,4,4,-7,11);
  run("multi_combine",multi_combine,2,0,0,0,5,3,-7,11);
  run("multi_combine",multi_combine,0,0,0,2,3,3,-2147483647-1,2147483647);
  run("multi_combine",multi_combine,3,0,0,0,0,3,-2147483647-1,2147483647);
  run("multi_combine",multi_combine,3,0,0,0,3,0,-2147483647-1,2147483647);
  run("multi_combine",multi_combine,3,0,0,0,-1,3,-2147483647-1,2147483647);
  run("multi_combine",multi_combine,3,0,0,0,3,-1,-2147483647-1,2147483647);
  run("multi_chain",multi_chain,0,0,0,0,1,2,-7,11);
  run("multi_chain",multi_chain,0,0,0,0,2,1,-7,11);
  run("multi_chain",multi_chain,0,0,0,0,2,3,-7,11);
  run("multi_chain",multi_chain,0,0,0,0,3,2,-7,11);
  run("multi_chain",multi_chain,0,0,0,0,3,3,-7,11);
  run("multi_chain",multi_chain,0,0,0,0,4,4,-7,11);
  run("multi_chain",multi_chain,0,0,0,0,5,3,-7,11);
  run("multi_chain",multi_chain,0,3,17,0,1,2,-7,11);
  run("multi_chain",multi_chain,0,3,17,0,2,1,-7,11);
  run("multi_chain",multi_chain,0,3,17,0,2,3,-7,11);
  run("multi_chain",multi_chain,0,3,17,0,3,2,-7,11);
  run("multi_chain",multi_chain,0,3,17,0,3,3,-7,11);
  run("multi_chain",multi_chain,0,3,17,0,4,4,-7,11);
  run("multi_chain",multi_chain,0,3,17,0,5,3,-7,11);
  run("multi_chain",multi_chain,1,0,0,0,1,2,-7,11);
  run("multi_chain",multi_chain,1,0,0,0,2,1,-7,11);
  run("multi_chain",multi_chain,1,0,0,0,2,3,-7,11);
  run("multi_chain",multi_chain,1,0,0,0,3,2,-7,11);
  run("multi_chain",multi_chain,1,0,0,0,3,3,-7,11);
  run("multi_chain",multi_chain,1,0,0,0,4,4,-7,11);
  run("multi_chain",multi_chain,1,0,0,0,5,3,-7,11);
  run("multi_chain",multi_chain,1,0,1,0,1,2,-7,11);
  run("multi_chain",multi_chain,1,0,1,0,2,1,-7,11);
  run("multi_chain",multi_chain,1,0,1,0,2,3,-7,11);
  run("multi_chain",multi_chain,1,0,1,0,3,2,-7,11);
  run("multi_chain",multi_chain,1,0,1,0,3,3,-7,11);
  run("multi_chain",multi_chain,1,0,1,0,4,4,-7,11);
  run("multi_chain",multi_chain,1,0,1,0,5,3,-7,11);
  run("multi_chain",multi_chain,1,0,4,0,1,2,-7,11);
  run("multi_chain",multi_chain,1,0,4,0,2,1,-7,11);
  run("multi_chain",multi_chain,1,0,4,0,2,3,-7,11);
  run("multi_chain",multi_chain,1,0,4,0,3,2,-7,11);
  run("multi_chain",multi_chain,1,0,4,0,3,3,-7,11);
  run("multi_chain",multi_chain,1,0,4,0,4,4,-7,11);
  run("multi_chain",multi_chain,1,0,4,0,5,3,-7,11);
  run("multi_chain",multi_chain,1,3,40,0,1,2,-7,11);
  run("multi_chain",multi_chain,1,3,40,0,2,1,-7,11);
  run("multi_chain",multi_chain,1,3,40,0,2,3,-7,11);
  run("multi_chain",multi_chain,1,3,40,0,3,2,-7,11);
  run("multi_chain",multi_chain,1,3,40,0,3,3,-7,11);
  run("multi_chain",multi_chain,1,3,40,0,4,4,-7,11);
  run("multi_chain",multi_chain,1,3,40,0,5,3,-7,11);
  run("multi_chain",multi_chain,2,0,0,0,1,2,-7,11);
  run("multi_chain",multi_chain,2,0,0,0,2,1,-7,11);
  run("multi_chain",multi_chain,2,0,0,0,2,3,-7,11);
  run("multi_chain",multi_chain,2,0,0,0,3,2,-7,11);
  run("multi_chain",multi_chain,2,0,0,0,3,3,-7,11);
  run("multi_chain",multi_chain,2,0,0,0,4,4,-7,11);
  run("multi_chain",multi_chain,2,0,0,0,5,3,-7,11);
  run("multi_chain",multi_chain,0,0,0,2,3,3,-2147483647-1,2147483647);
  run("multi_chain",multi_chain,3,0,0,0,0,3,-2147483647-1,2147483647);
  run("multi_chain",multi_chain,3,0,0,0,3,0,-2147483647-1,2147483647);
  run("multi_chain",multi_chain,3,0,0,0,-1,3,-2147483647-1,2147483647);
  run("multi_chain",multi_chain,3,0,0,0,3,-1,-2147483647-1,2147483647);
  run("multi_reflected",multi_reflected,0,0,0,0,1,2,-7,11);
  run("multi_reflected",multi_reflected,0,0,0,0,2,1,-7,11);
  run("multi_reflected",multi_reflected,0,0,0,0,2,3,-7,11);
  run("multi_reflected",multi_reflected,0,0,0,0,3,2,-7,11);
  run("multi_reflected",multi_reflected,0,0,0,0,3,3,-7,11);
  run("multi_reflected",multi_reflected,0,0,0,0,4,4,-7,11);
  run("multi_reflected",multi_reflected,0,0,0,0,5,3,-7,11);
  run("multi_reflected",multi_reflected,0,3,17,0,1,2,-7,11);
  run("multi_reflected",multi_reflected,0,3,17,0,2,1,-7,11);
  run("multi_reflected",multi_reflected,0,3,17,0,2,3,-7,11);
  run("multi_reflected",multi_reflected,0,3,17,0,3,2,-7,11);
  run("multi_reflected",multi_reflected,0,3,17,0,3,3,-7,11);
  run("multi_reflected",multi_reflected,0,3,17,0,4,4,-7,11);
  run("multi_reflected",multi_reflected,0,3,17,0,5,3,-7,11);
  run("multi_reflected",multi_reflected,1,0,0,0,1,2,-7,11);
  run("multi_reflected",multi_reflected,1,0,0,0,2,1,-7,11);
  run("multi_reflected",multi_reflected,1,0,0,0,2,3,-7,11);
  run("multi_reflected",multi_reflected,1,0,0,0,3,2,-7,11);
  run("multi_reflected",multi_reflected,1,0,0,0,3,3,-7,11);
  run("multi_reflected",multi_reflected,1,0,0,0,4,4,-7,11);
  run("multi_reflected",multi_reflected,1,0,0,0,5,3,-7,11);
  run("multi_reflected",multi_reflected,1,0,1,0,1,2,-7,11);
  run("multi_reflected",multi_reflected,1,0,1,0,2,1,-7,11);
  run("multi_reflected",multi_reflected,1,0,1,0,2,3,-7,11);
  run("multi_reflected",multi_reflected,1,0,1,0,3,2,-7,11);
  run("multi_reflected",multi_reflected,1,0,1,0,3,3,-7,11);
  run("multi_reflected",multi_reflected,1,0,1,0,4,4,-7,11);
  run("multi_reflected",multi_reflected,1,0,1,0,5,3,-7,11);
  run("multi_reflected",multi_reflected,1,0,4,0,1,2,-7,11);
  run("multi_reflected",multi_reflected,1,0,4,0,2,1,-7,11);
  run("multi_reflected",multi_reflected,1,0,4,0,2,3,-7,11);
  run("multi_reflected",multi_reflected,1,0,4,0,3,2,-7,11);
  run("multi_reflected",multi_reflected,1,0,4,0,3,3,-7,11);
  run("multi_reflected",multi_reflected,1,0,4,0,4,4,-7,11);
  run("multi_reflected",multi_reflected,1,0,4,0,5,3,-7,11);
  run("multi_reflected",multi_reflected,1,3,40,0,1,2,-7,11);
  run("multi_reflected",multi_reflected,1,3,40,0,2,1,-7,11);
  run("multi_reflected",multi_reflected,1,3,40,0,2,3,-7,11);
  run("multi_reflected",multi_reflected,1,3,40,0,3,2,-7,11);
  run("multi_reflected",multi_reflected,1,3,40,0,3,3,-7,11);
  run("multi_reflected",multi_reflected,1,3,40,0,4,4,-7,11);
  run("multi_reflected",multi_reflected,1,3,40,0,5,3,-7,11);
  run("multi_reflected",multi_reflected,2,0,0,0,1,2,-7,11);
  run("multi_reflected",multi_reflected,2,0,0,0,2,1,-7,11);
  run("multi_reflected",multi_reflected,2,0,0,0,2,3,-7,11);
  run("multi_reflected",multi_reflected,2,0,0,0,3,2,-7,11);
  run("multi_reflected",multi_reflected,2,0,0,0,3,3,-7,11);
  run("multi_reflected",multi_reflected,2,0,0,0,4,4,-7,11);
  run("multi_reflected",multi_reflected,2,0,0,0,5,3,-7,11);
  run("multi_reflected",multi_reflected,0,0,0,2,3,3,-2147483647-1,2147483647);
  run("multi_reflected",multi_reflected,3,0,0,0,0,3,-2147483647-1,2147483647);
  run("multi_reflected",multi_reflected,3,0,0,0,3,0,-2147483647-1,2147483647);
  run("multi_reflected",multi_reflected,3,0,0,0,-1,3,-2147483647-1,2147483647);
  run("multi_reflected",multi_reflected,3,0,0,0,3,-1,-2147483647-1,2147483647);
  run("multi_context",multi_context,0,0,0,0,1,2,-7,11);
  run("multi_context",multi_context,0,0,0,0,2,1,-7,11);
  run("multi_context",multi_context,0,0,0,0,2,3,-7,11);
  run("multi_context",multi_context,0,0,0,0,3,2,-7,11);
  run("multi_context",multi_context,0,0,0,0,3,3,-7,11);
  run("multi_context",multi_context,0,0,0,0,4,4,-7,11);
  run("multi_context",multi_context,0,0,0,0,5,3,-7,11);
  run("multi_context",multi_context,0,3,17,0,1,2,-7,11);
  run("multi_context",multi_context,0,3,17,0,2,1,-7,11);
  run("multi_context",multi_context,0,3,17,0,2,3,-7,11);
  run("multi_context",multi_context,0,3,17,0,3,2,-7,11);
  run("multi_context",multi_context,0,3,17,0,3,3,-7,11);
  run("multi_context",multi_context,0,3,17,0,4,4,-7,11);
  run("multi_context",multi_context,0,3,17,0,5,3,-7,11);
  run("multi_context",multi_context,1,0,0,0,1,2,-7,11);
  run("multi_context",multi_context,1,0,0,0,2,1,-7,11);
  run("multi_context",multi_context,1,0,0,0,2,3,-7,11);
  run("multi_context",multi_context,1,0,0,0,3,2,-7,11);
  run("multi_context",multi_context,1,0,0,0,3,3,-7,11);
  run("multi_context",multi_context,1,0,0,0,4,4,-7,11);
  run("multi_context",multi_context,1,0,0,0,5,3,-7,11);
  run("multi_context",multi_context,1,0,1,0,1,2,-7,11);
  run("multi_context",multi_context,1,0,1,0,2,1,-7,11);
  run("multi_context",multi_context,1,0,1,0,2,3,-7,11);
  run("multi_context",multi_context,1,0,1,0,3,2,-7,11);
  run("multi_context",multi_context,1,0,1,0,3,3,-7,11);
  run("multi_context",multi_context,1,0,1,0,4,4,-7,11);
  run("multi_context",multi_context,1,0,1,0,5,3,-7,11);
  run("multi_context",multi_context,1,0,4,0,1,2,-7,11);
  run("multi_context",multi_context,1,0,4,0,2,1,-7,11);
  run("multi_context",multi_context,1,0,4,0,2,3,-7,11);
  run("multi_context",multi_context,1,0,4,0,3,2,-7,11);
  run("multi_context",multi_context,1,0,4,0,3,3,-7,11);
  run("multi_context",multi_context,1,0,4,0,4,4,-7,11);
  run("multi_context",multi_context,1,0,4,0,5,3,-7,11);
  run("multi_context",multi_context,1,3,40,0,1,2,-7,11);
  run("multi_context",multi_context,1,3,40,0,2,1,-7,11);
  run("multi_context",multi_context,1,3,40,0,2,3,-7,11);
  run("multi_context",multi_context,1,3,40,0,3,2,-7,11);
  run("multi_context",multi_context,1,3,40,0,3,3,-7,11);
  run("multi_context",multi_context,1,3,40,0,4,4,-7,11);
  run("multi_context",multi_context,1,3,40,0,5,3,-7,11);
  run("multi_context",multi_context,2,0,0,0,1,2,-7,11);
  run("multi_context",multi_context,2,0,0,0,2,1,-7,11);
  run("multi_context",multi_context,2,0,0,0,2,3,-7,11);
  run("multi_context",multi_context,2,0,0,0,3,2,-7,11);
  run("multi_context",multi_context,2,0,0,0,3,3,-7,11);
  run("multi_context",multi_context,2,0,0,0,4,4,-7,11);
  run("multi_context",multi_context,2,0,0,0,5,3,-7,11);
  run("multi_context",multi_context,0,0,0,2,3,3,-2147483647-1,2147483647);
  run("multi_context",multi_context,3,0,0,0,0,3,-2147483647-1,2147483647);
  run("multi_context",multi_context,3,0,0,0,3,0,-2147483647-1,2147483647);
  run("multi_context",multi_context,3,0,0,0,-1,3,-2147483647-1,2147483647);
  run("multi_context",multi_context,3,0,0,0,3,-1,-2147483647-1,2147483647);
  run("multi_undef",multi_undef,3,0,0,0,0,3,1,0);
  run("multi_undef",multi_undef,3,0,0,0,3,0,1,0);
  run("multi_undef",multi_undef,3,0,0,0,-1,3,1,0);
  run("multi_undef",multi_undef,3,0,0,0,3,-1,1,0);
  run_tiny(0,1,2,-7,11);
  run_tiny(0,1,1,-7,11);
  run_tiny(0,0,2,-7,11);
  run_tiny(0,1,0,-7,11);
  run_tiny(1,1,2,-7,11);
  return 0;
}
