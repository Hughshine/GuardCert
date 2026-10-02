#include <stdio.h>

int pair_direct(void) {
  int a[2];
  { a[0] = 7; a[1] = 8; }
  return 100 * a[0] + a[1];
}

int pair_in_loop(void) {
  int a[2];
  int i;
  for (i = 0; i < 3; ++i) {
    { a[0] = 7; a[1] = 8; }
  }
  return 100 * a[0] + a[1];
}

int pair_after_goto(void) {
  int a[2];
  goto work;
work:
  { a[0] = 7; a[1] = 8; }
  return 100 * a[0] + a[1];
}

int different_value(void) {
  int a[2];
  { a[0] = 6; a[1] = 8; }
  return 100 * a[0] + a[1];
}

int same_cell(void) {
  int a[2];
  a[1] = 0;
  { a[0] = 7; a[0] = 8; }
  return 100 * a[0] + a[1];
}

int different_extent(void) {
  int a[3];
  a[2] = 9;
  { a[0] = 7; a[1] = 8; }
  return 10000 * a[0] + 100 * a[1] + a[2];
}

int volatile_array(void) {
  volatile int a[2];
  { a[0] = 7; a[1] = 8; }
  return 100 * a[0] + a[1];
}

int longer_sequence(void) {
  int a[2];
  a[0] = 7;
  a[1] = 8;
  return 100 * a[0] + a[1];
}

int main(void) {
  printf("store %d %d %d %d %d %d %d %d\n",
    pair_direct(), pair_in_loop(), pair_after_goto(), different_value(),
    same_cell(), different_extent(), volatile_array(), longer_sequence());
  return 0;
}
