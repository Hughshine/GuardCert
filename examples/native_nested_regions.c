#include <stdio.h>
#include <limits.h>

int nested_ordinary(int i, int n, int start_j, int m, int *last_j) {
  int a[1], j = 99;
  a[0] = 0;
  for (; i < n; ++i) {
    for (j = start_j; j < m; ++j) { a[0] = a[0] + 1; }
  }
  *last_j = j;
  return a[0];
}

int nested_goto(int i, int n, int start_j, int m, int *last_j) {
  int a[1], j = 99;
  a[0] = 0;
  goto work;
work:
  for (; i < n; ++i) {
    for (j = start_j; j < m; ++j) { a[0] = a[0] + 1; }
  }
  *last_j = j;
  return a[0];
}

int nested_context(int start_i, int n, int start_j, int m) {
  int a[1], i, j, k;
  a[0] = 0;
  for (k = 0; k < 2; ++k) {
    for (i = start_i; i < n; ++i) {
      for (j = start_j; j < m; ++j) { a[0] = a[0] + 1; }
    }
  }
  return a[0];
}

int nested_null(int i, int n, int m, int *p) {
  int j = 99;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) { *p = *p + 1; }
  }
  return j;
}

int nested_array(int n, int m) {
  int a[4] = {0, 0, 0, 0}, i, j;
  for (i = 0; i < n; ++i) {
    for (j = 0; j < m; ++j) { a[i * 2 + j] = i * 10 + j + 1; }
  }
  return a[0] + a[1] + a[2] + a[3];
}

int nested_outer_mutation(int i, int n, int m) {
  int a[1], j;
  a[0] = 0;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) { ++i; a[0] = a[0] + 1; }
  }
  return a[0];
}

int nested_bound_mutation(int i, int n, int m) {
  int j;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) { --n; }
  }
  return i;
}

int main(void) {
  int starts[7] = {0, 1, -2, INT_MAX-1, INT_MAX, INT_MIN, 0};
  int ends[7] = {2, 0, 1, INT_MAX, INT_MAX, INT_MIN+1, 1};
  int inner_starts[7] = {0, 0, -1, INT_MAX-1, INT_MIN, INT_MIN, 2};
  int inner_ends[7] = {2, 3, 1, INT_MAX, INT_MIN+1, INT_MIN+1, 1};
  int k, j1, j2, c1, c2, value;
  for (k = 0; k < 7; ++k) {
    c1 = nested_ordinary(starts[k], ends[k], inner_starts[k], inner_ends[k], &j1);
    c2 = nested_goto(starts[k], ends[k], inner_starts[k], inner_ends[k], &j2);
    printf("nested %d %d %d %d %d\n", c1, j1, c2, j2,
      nested_context(starts[k], ends[k], inner_starts[k], inner_ends[k]));
  }
  value = 3;
  printf("null %d %d\n", nested_null(1, 1, INT_MAX, 0), nested_null(0, 1, 0, 0));
  j1 = nested_null(0, 2, 2, &value);
  printf("memory %d %d\n", j1, value);
  printf("array %d %d %d\n", nested_array(2, 2), nested_array(1, 2), nested_array(0, 2));
  printf("refused %d %d\n", nested_outer_mutation(0, 2, 1), nested_bound_mutation(0, 3, 1));
  return 0;
}
