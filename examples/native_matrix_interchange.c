#include <stdio.h>
#include <limits.h>

int global_matrix[4];

int matrix_dynamic(int i, int n, int m, int *last_i, int *last_j) {
  int a[4] = {0, 0, 0, 0}, j = 99;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) { a[i * 2 + j] = i * 10 + j + 1; }
  }
  *last_i = i;
  *last_j = j;
  return a[0] + a[1] + a[2] + a[3];
}

int matrix_goto(int n, int m) {
  int a[4] = {0, 0, 0, 0}, i = 0, j = 99;
  goto work;
work:
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) { a[i * 2 + j] = i * 10 + j + 1; }
  }
  return a[0] + a[1] + a[2] + a[3] + i * 100 + j;
}

int matrix_global(int n, int m) {
  int i = 0, j = 99;
  global_matrix[0] = 0; global_matrix[1] = 0;
  global_matrix[2] = 0; global_matrix[3] = 0;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) { global_matrix[i * 2 + j] = i * 10 + j + 1; }
  }
  return global_matrix[0] + global_matrix[1] + global_matrix[2] + global_matrix[3];
}

int matrix_context(int n, int m) {
  int a[4] = {0, 0, 0, 0}, i, j = 99, k;
  for (k = 0; k < 2; ++k) {
    for (i = 0; i < n; ++i) {
      for (j = 0; j < m; ++j) { a[i * 2 + j] = i * 10 + j + 1; }
    }
  }
  return a[0] + a[1] + a[2] + a[3] + i * 100 + j;
}

/* A defined zero-trip execution never reads the uninitialized inner bound. */
int matrix_unread_bound(int i, int n) {
  int a[4] = {0, 0, 0, 0}, j = 99, m;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) { a[i * 2 + j] = i * 10 + j + 1; }
  }
  return j + a[0] + a[1] + a[2] + a[3];
}

int matrix_different_value(int n, int m) {
  int a[4] = {0, 0, 0, 0}, i, j;
  for (i = 0; i < n; ++i) {
    for (j = 0; j < m; ++j) { a[i * 2 + j] = 99; }
  }
  return a[0] + a[1] + a[2] + a[3];
}

int matrix_dependent_value(int n, int m) {
  int a[4] = {0, 0, 0, 0}, i, j;
  for (i = 0; i < n; ++i) {
    for (j = 0; j < m; ++j) { a[i * 2 + j] = a[0] + i * 10 + j + 1; }
  }
  return a[0] + a[1] + a[2] + a[3];
}

int matrix_volatile(int n, int m) {
  volatile int a[4] = {0, 0, 0, 0};
  int i, j;
  for (i = 0; i < n; ++i) {
    for (j = 0; j < m; ++j) { a[i * 2 + j] = i * 10 + j + 1; }
  }
  return a[0] + a[1] + a[2] + a[3];
}

int main(void) {
  int starts[9] = {0, 0, 0, 0, 1, 3, 0, INT_MAX, INT_MIN};
  int ends[9] = {2, 1, 2, 0, 2, 2, 2, INT_MAX, INT_MIN};
  int inner_ends[9] = {2, 2, 1, 2, 2, 2, 0, INT_MIN, INT_MAX};
  int k, value, i, j;
  for (k = 0; k < 9; ++k) {
    value = matrix_dynamic(starts[k], ends[k], inner_ends[k], &i, &j);
    printf("matrix %d %d %d\n", value, i, j);
  }
  printf("contexts %d %d %d\n", matrix_goto(2, 2), matrix_global(2, 2), matrix_context(2, 2));
  printf("fallbacks %d %d %d\n", matrix_goto(1, 2), matrix_global(2, 1), matrix_context(1, 2));
  printf("unread %d %d %d\n", matrix_unread_bound(0, 0), matrix_unread_bound(1, 0),
    matrix_unread_bound(INT_MAX, INT_MAX));
  printf("refused %d %d %d\n", matrix_different_value(2, 2), matrix_dependent_value(2, 2), matrix_volatile(2, 2));
  return 0;
}
