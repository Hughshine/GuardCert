#include <stdio.h>

volatile unsigned inputs[] = {0u, 1u, 254u, 2147483647u, 2147483648u, 4294967295u};
volatile unsigned divisors[] = {1u, 2u, 3u, 4294967295u};
unsigned sink;

unsigned divide(unsigned x, unsigned y) { return x / y; }
unsigned modulo(unsigned x, unsigned y) { return x % y; }
unsigned cancel(unsigned x) { return (x + x) / 2u; }
unsigned identity(unsigned x) { return x - x; }
unsigned nested(unsigned x, unsigned y) { return 3u + (x / y) * 5u; }
unsigned assigned(unsigned x, unsigned y) { unsigned z; z = x / y; return z; }
unsigned stored(unsigned x) { sink = (x + x) / 2u; return sink; }
unsigned in_loop(unsigned x, unsigned y) {
  unsigned result = 0u, i;
  for (i = 0u; i < 2u; ++i) result += x / y;
  return result;
}
unsigned labeled(unsigned x, unsigned y) {
  if (x == 123u) goto calculate;
  x += 1u;
calculate:
  return x / y;
}
unsigned guarded_divide(unsigned x, unsigned y) {
  if (y == 0u) return 777u;
  return x / y;
}
unsigned switch_case(unsigned x, unsigned y) {
  switch (y) { case 2u: return x / y; default: return x % y; }
}

int main(void) {
  unsigned i, j, x, y, c;
  for (i = 0u; i < 6u; ++i) {
    x = inputs[i];
    c = cancel(x);
    if (c != (x + x) / 2u || stored(x) != c || identity(x) != 0u) return 1;
    printf("cancel %u %u\n", x, c);
    for (j = 0u; j < 4u; ++j) {
      y = divisors[j];
      printf("ops %u %u %u %u %u %u %u %u\n", x, y, divide(x, y), modulo(x, y),
        nested(x, y), assigned(x, y), in_loop(x, y), switch_case(x, y));
    }
  }
  printf("goto %u zero %u\n", labeled(123u, 2u), guarded_divide(123u, 0u));
  return 0;
}
