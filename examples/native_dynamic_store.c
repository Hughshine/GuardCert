#include <stdio.h>

int dynamic_pair(int i, int j) {
  int a[2];
  a[0] = 0; a[1] = 0;
  { a[i] = 7; a[j] = 8; }
  return 100 * a[0] + a[1];
}

int dynamic_pair_in_loop(int i, int j) {
  int a[2];
  int k;
  a[0] = 0; a[1] = 0;
  for (k = 0; k < 3; ++k) {
    { a[i] = 7; a[j] = 8; }
  }
  return 100 * a[0] + a[1];
}

int dynamic_pair_after_goto(int i, int j) {
  int a[2];
  a[0] = 0; a[1] = 0;
  goto work;
work:
  { a[i] = 7; a[j] = 8; }
  return 100 * a[0] + a[1];
}

int different_value(int i, int j) {
  int a[2];
  a[0] = 0; a[1] = 0;
  { a[i] = 6; a[j] = 8; }
  return 100 * a[0] + a[1];
}

int volatile_indices(int i, int j) {
  volatile int a[2];
  a[0] = 0; a[1] = 0;
  { a[i] = 7; a[j] = 8; }
  return 100 * a[0] + a[1];
}

int main(void) {
  int i, j;
  for (i = 0; i < 2; ++i) {
    for (j = 0; j < 2; ++j) {
      printf("dynamic %d %d %d %d %d %d %d\n", i, j,
        dynamic_pair(i, j), dynamic_pair_in_loop(i, j), dynamic_pair_after_goto(i, j),
        different_value(i, j), volatile_indices(i, j));
    }
  }
  return 0;
}
