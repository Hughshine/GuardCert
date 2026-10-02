#include <stdio.h>

volatile int inputs[] = {
  (-2147483647 - 1), -1073741825, -1073741824, -1, 0, 1,
  1073741823, 1073741824, 2147483647
};

int signed_cancel(int x) { return (x * 2) / 2; }
int signed_nested(int x) { return 3 + (x * 2) / 2; }
int signed_local(int x) {
  int y = (x * 2) / 2;
  return y;
}
int signed_labeled(int x) {
  if (x == 0) goto rewrite;
  return (x * 2) / 2;
rewrite:
  return (x * 2) / 2;
}
unsigned unsigned_excluded(unsigned x) { return (x * 2u) / 2u; }
int three_excluded(int x) { return (x * 3) / 3; }

int main(void) {
  unsigned i;
  int x;
  for (i = 0; i < 9; ++i) {
    x = inputs[i];
    printf("signed %d %d %d %d %d\n", x, signed_cancel(x),
      signed_nested(x), signed_local(x), signed_labeled(x));
  }
  printf("excluded %u %d\n", unsigned_excluded(2147483648u), three_excluded(7));
  return 0;
}
