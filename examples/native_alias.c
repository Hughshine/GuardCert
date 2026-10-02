#include <stdio.h>

volatile unsigned values[] = {0u, 1u, 2147483647u, 2147483648u, 4294967295u};

unsigned load_pair(unsigned *p, unsigned *q) { return *p + *q; }
unsigned nested_pair(unsigned *p, unsigned *q) { return 3u + (*p + *q); }
unsigned stored_pair(unsigned *p, unsigned *q, unsigned *out) {
  *out = *p + *q;
  return *out;
}
unsigned nullable_pair(unsigned *p, unsigned *q) {
  if (!p || !q) return 777u;
  return *p + *q;
}
int signed_pair(int *p, int *q) { return *p + *q; }
unsigned volatile_pair(volatile unsigned *p, volatile unsigned *q) { return *p + *q; }

int main(void) {
  unsigned i, j, left, right, result;
  unsigned overwritten = 4294967295u, unchanged = 1u;
  int signed_left = 7, signed_right = 9;
  for (i = 0u; i < 5u; ++i) {
    left = values[i];
    printf("same %u %u %u %u\n", left, load_pair(&left, &left),
      nested_pair(&left, &left), stored_pair(&left, &left, &result));
    for (j = 0u; j < 5u; ++j) {
      right = values[j];
      printf("separate %u %u %u %u\n", left, right,
        load_pair(&left, &right), nested_pair(&left, &right));
    }
  }
  printf("null %u signed %d volatile %u\n", nullable_pair(0, &left),
    signed_pair(&signed_left, &signed_right), volatile_pair(&left, &right));
  result = stored_pair(&overwritten, &unchanged, &overwritten);
  printf("store-alias %u %u %u\n", result, overwritten, unchanged);
  return 0;
}
