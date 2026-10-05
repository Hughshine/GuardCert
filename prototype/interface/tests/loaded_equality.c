#include <stdio.h>
#include <limits.h>

void loaded_equality(int start, unsigned int *bound, unsigned int *out) {
  int i = start;
  for (; i != (int)*bound; ++i) *out = (unsigned int)i + 1U;
  printf("load %d %d %u %u\n", start, i, *bound, out ? *out : 77U);
}
void loaded_equality_jump(int start, unsigned int *bound, unsigned int *out) {
  int i = start;
  goto work;
work:
  for (; i != (int)*bound; ++i) *out = (unsigned int)i + 1U;
  printf("jump %d %d %u %u\n", start, i, *bound, out ? *out : 77U);
}
void loaded_equality_enclosing(int start, unsigned int *bound, unsigned int *out) {
  int i, repeat;
  for (repeat = 0; repeat < 2; ++repeat) {
    i = start;
    for (; i != (int)*bound; ++i) *out = (unsigned int)i + 1U;
  }
  printf("nested %d %d %u %u\n", start, i, *bound, out ? *out : 77U);
}
int compare_loaded(int i, unsigned int *bound) {
  return i != (int)*bound;
}
int compare_expression(int i, int mask, int n) {
  return (i & mask) != n;
}
void constant_signed_head(unsigned int *out) {
  int i = 0;
  for (; i != 6; i += 2) *out = (unsigned int)i + 1U;
  printf("constant %d %u\n", i, *out);
}
void loaded_equality_infinite(unsigned int *bound, unsigned int *out) {
  int i = 0;
  while (1) {
    for (; i != (int)*bound; ++i) *out = (unsigned int)i + 1U;
    i = 0;
  }
}
int unsupported_unsigned_values(unsigned int i, unsigned int n) {
  return i != n;
}
int unsupported_float_values(double i, double n) {
  return i != n;
}
int compare_volatile_snapshot(int i, volatile int *bound) {
  return i != (int)*bound;
}
int main(void) {
  unsigned int bound, out, values[7] = {0U, 1U, 2U, (unsigned int)INT_MAX, (unsigned int)INT_MIN, UINT_MAX-1U, UINT_MAX};
  int start, n, alias, k, j;
  volatile int volatile_bound = 1;
  for (n = 0; n <= 12; ++n) {
    for (start = 0; start <= n; ++start) {
      for (alias = 0; alias <= 1; ++alias) {
        bound = (unsigned int)n; out = 77U;
        loaded_equality(start, &bound, alias ? &bound : &out);
        bound = (unsigned int)n; out = 77U;
        loaded_equality_jump(start, &bound, alias ? &bound : &out);
        bound = (unsigned int)n; out = 77U;
        loaded_equality_enclosing(start, &bound, alias ? &bound : &out);
      }
    }
  }
  bound = (unsigned int)-3; loaded_equality(0, &bound, &bound);
  bound = (unsigned int)INT_MIN; loaded_equality_jump(0, &bound, &bound);
  bound = (unsigned int)INT_MAX; loaded_equality_enclosing(0, &bound, &bound);
  bound = 0U; loaded_equality(0, &bound, (unsigned int *)0);
  bound = (unsigned int)-3; loaded_equality_jump(-3, &bound, (unsigned int *)0);
  bound = (unsigned int)INT_MIN; loaded_equality_enclosing(INT_MIN, &bound, (unsigned int *)0);
  for (k = 0; k < 7; ++k) {
    bound = values[k];
    for (start = -2; start <= 2; ++start) {
      printf("value %d %u %d\n", start, bound, compare_loaded(start, &bound));
    }
  }
  for (k = -3; k <= 8; ++k) {
    for (j = -2; j <= 9; ++j) {
      printf("expr %d %d %d\n", k, j, compare_expression(k, 7, j));
    }
  }
  for (start = -2; start <= 2; ++start) printf("volatile-value %d %d\n", start, compare_volatile_snapshot(start, &volatile_bound));
  out = 77U; constant_signed_head(&out);
  return 0;
}
