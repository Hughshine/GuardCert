#include <stdio.h>
#include <limits.h>

int ordinary(int i, int n) {
  int a[1];
  a[0] = 0;
  for (; i < n; ++i) { a[0] = a[0] + 1; }
  return a[0];
}

int loop_context(int start, int n) {
  int a[1];
  int i, k;
  a[0] = 0;
  for (k = 0; k < 2; ++k) {
    i = start;
    for (; i < n; ++i) { a[0] = a[0] + 1; }
  }
  return a[0];
}

int goto_context(int i, int n) {
  int a[1];
  a[0] = 0;
  goto work;
work:
  for (; i < n; ++i) { a[0] = a[0] + 1; }
  return a[0];
}

int zero_trip_null(int i, int n, int *p) {
  for (; i < n; ++i) { *p = 8; }
  return i;
}

int counter_body_excluded(int i, int n) {
  int a[1];
  a[0] = 0;
  for (; i < n; ++i) { ++i; a[0] = a[0] + 1; }
  return a[0];
}

int nonstrict_excluded(int i, int n) {
  int a[1];
  a[0] = 0;
  for (; i <= n; ++i) { a[0] = a[0] + 1; }
  return a[0];
}

int main(void) {
  int starts[8] = {0, 1, -2, 4, INT_MAX-1, INT_MAX, INT_MIN, INT_MIN};
  int bounds[8] = {0, 0, 1, 7, INT_MAX, INT_MAX, INT_MIN, INT_MIN+1};
  int j, value, final_i;
  for (j = 0; j < 8; ++j) {
    printf("zero %d %d %d %d %d\n", starts[j], bounds[j],
      ordinary(starts[j], bounds[j]), loop_context(starts[j], bounds[j]),
      goto_context(starts[j], bounds[j]));
  }
  value = 3;
  final_i = zero_trip_null(0, 1, &value);
  printf("pointer %d %d %d\n", final_i, value, zero_trip_null(1, 1, 0));
  printf("excluded %d %d\n", counter_body_excluded(0, 2), nonstrict_excluded(0, 1));
  return 0;
}
