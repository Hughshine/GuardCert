#include <stdio.h>
#include <limits.h>

void emit_strip(char *tag, int i, int n, int *a, int *b) {
  int k;
  printf("%s %d %d", tag, i, n);
  for (k = 0; k < 64; ++k) printf(" %d", a[k]);
  for (k = 0; k < 64; ++k) printf(" %d", b[k]);
  printf("\n");
}

void dependent_strip(int i, int n) {
  int a[64], b[64], k;
  for (k = 0; k < 64; ++k) { a[k] = -100; b[k] = k % 5 + 1; }
  a[0] = 1;
  for (; i < n; ++i) {
    a[i+1] = a[i] + b[i];
    if (i % 2 == 0) b[i] = a[i+1] - b[i]; else b[i] = a[i+1] + b[i];
  }
  emit_strip("dependent", i, n, a, b);
}

int pointer_strip(int *dst, int *src, int n) {
  int i = 0;
  for (; i < n; ++i) dst[i+1] = src[i] + 2;
  return i;
}

void alias_case(int n, int alias) {
  int a[64], b[64], k, i;
  for (k = 0; k < 64; ++k) { a[k] = -100; b[k] = k % 5 + 1; }
  a[0] = 1;
  i = pointer_strip(a, alias ? a : b, n);
  emit_strip(alias ? "alias" : "separate", i, n, a, b);
}

void goto_strip(int n) {
  int a[64], b[64], i = 0, k;
  for (k = 0; k < 64; ++k) { a[k] = -100; b[k] = k % 5 + 1; }
  a[0] = 1;
  goto work;
work:
  for (; i < n; ++i) a[i+1] = a[i] + b[i];
  emit_strip("goto", i, n, a, b);
}

void switch_strip(int n) {
  int a[64], b[64], i = 0, k;
  for (k = 0; k < 64; ++k) { a[k] = -100; b[k] = k % 5 + 1; }
  a[0] = 1;
  switch (n % 2) {
  case 0:
    for (; i < n; ++i) a[i+1] = a[i] + b[i];
    break;
  default:
    for (; i < n; ++i) a[i+1] = a[i] - b[i];
  }
  emit_strip("switch", i, n, a, b);
}

void enclosing_strip(int n) {
  int a[64], b[64], i = 0, k, repeat;
  for (k = 0; k < 64; ++k) { a[k] = -100; b[k] = k % 5 + 1; }
  a[0] = 1;
  for (repeat = 0; repeat < 2; ++repeat) {
    for (i = 0; i < n; ++i) { a[i+1] = a[i] + b[i]; b[i] = b[i] + 1; }
  }
  emit_strip("enclosing", i, n, a, b);
}

void recursive_strip(int depth, int n) {
  int a[64], b[64], i = 0, k;
  for (k = 0; k < 64; ++k) { a[k] = -100; b[k] = k % 5 + 1; }
  a[0] = 1;
  for (; i < n; ++i) a[i+1] = a[i] + b[i];
  if (depth > 0) recursive_strip(depth - 1, n - 1);
  emit_strip("recursive", i, n, a, b);
}

void volatile_strip(int n) {
  volatile int a[64];
  int i = 0, k;
  for (k = 0; k < 64; ++k) a[k] = -100;
  a[0] = 1;
  for (; i < n; ++i) a[i+1] = a[i] + 1;
  printf("volatile %d", i);
  for (k = 0; k < 64; ++k) printf(" %d", a[k]);
  printf("\n");
}

int call_in_loop(int n) {
  int i = 0;
  for (; i < n; ++i) printf("call %d\n", i);
  return i;
}

int bound_mutation(int n) {
  int i = 0;
  for (; i < n; ++i) n = n - 1;
  return i + n;
}

int early_break(int n) {
  int i = 0;
  for (; i < n; ++i) { if (i == 3) break; }
  return i;
}

int main(void) {
  int n;
  for (n = 1; n <= 63; ++n) { dependent_strip(0,n); alias_case(n,0); alias_case(n,1); }
  dependent_strip(1,7); dependent_strip(0,0); dependent_strip(0,-3);
  dependent_strip(INT_MAX,INT_MAX); dependent_strip(INT_MIN,INT_MIN);
  goto_strip(7); switch_strip(6); switch_strip(7); enclosing_strip(9); recursive_strip(2,9);
  volatile_strip(9); printf("called %d\n", call_in_loop(3));
  printf("refused %d %d\n", bound_mutation(9), early_break(9));
  return 0;
}
