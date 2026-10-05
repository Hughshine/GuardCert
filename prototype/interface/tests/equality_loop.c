#include <stdio.h>
#include <limits.h>

void equality_loop(unsigned int start, unsigned int n, unsigned int *out) {
  unsigned int i = start;
  for (; (int)i != (int)n; i = i + 1U) *out = i + 1U;
  printf("plain %u %u %u %u\n", start, n, i, out ? *out : 77U);
}
void equality_goto(unsigned int start, unsigned int n, unsigned int *out) {
  unsigned int i = start;
  goto work;
work:
  for (; (int)i != (int)n; i = i + 1U) *out = i + 1U;
  printf("jump %u %u %u %u\n", start, n, i, out ? *out : 77U);
}
void equality_enclosing(unsigned int start, unsigned int n, unsigned int *out) {
  unsigned int i, repeat;
  for (repeat = 0U; repeat < 2U; repeat = repeat + 1U) {
    i = start;
    for (; (int)i != (int)n; i = i + 1U) *out = i + 1U;
  }
  printf("nested %u %u %u %u\n", start, n, i, out ? *out : 77U);
}
void equality_forever(unsigned int n, unsigned int *out) {
  unsigned int i;
  while (1) {
    i = 0U;
    for (; (int)i != (int)n; i = i + 1U) *out = i + 1U;
  }
}
void equality_twice(unsigned int n, unsigned int *out) {
  unsigned int i = 0U;
  for (; (int)i != (int)n; i = i + 1U) *out = i + 1U;
  n = n + 2U;
  i = 0U;
  for (; (int)i != (int)n; i = i + 1U) *out = i + 1U;
  printf("twice %u %u %u\n", n, i, *out);
}
void equality_rmw(unsigned int start, unsigned int n, unsigned int *out) {
  unsigned int i = start;
  for (; (int)i != (int)n; i = i + 1U) *out = *out + i + 1U;
  printf("rmw %u %u %u %u\n", start, n, i, *out);
}
void equality_changed(unsigned int n, unsigned int *out) {
  unsigned int i = 0U;
  for (; (int)i != (int)n; i = i + 1U) {
    *out = i + 1U;
    n = n + 1U;
  }
}
void equality_step2(unsigned int n, unsigned int *out) {
  unsigned int i = 0U;
  for (; (int)i != (int)n; i = i + 2U) *out = i + 1U;
}
void equality_volatile(unsigned int n, volatile unsigned int *out) {
  unsigned int i = 0U;
  for (; (int)i != (int)n; i = i + 1U) *out = i + 1U;
}
int main(void) {
  unsigned int out, n, start;
  for (n = 0U; n <= 20U; n = n + 1U) {
    for (start = 0U; start <= n; start = start + 1U) {
      out = 77U; equality_loop(start, n, &out);
      out = 77U; equality_goto(start, n, &out);
      out = 77U; equality_enclosing(start, n, &out);
    }
  }
  out = 77U; equality_loop(UINT_MAX-1U, 1U, &out);
  out = 77U; equality_goto(UINT_MAX, 0U, &out);
  out = 77U; equality_enclosing(UINT_MAX-1U, 1U, &out);
  out = 77U; equality_loop((unsigned int)INT_MAX, (unsigned int)INT_MIN, &out);
  equality_loop(0U, 0U, (unsigned int *)0);
  equality_goto(UINT_MAX, UINT_MAX, (unsigned int *)0);
  equality_enclosing((unsigned int)INT_MIN, (unsigned int)INT_MIN, (unsigned int *)0);
  out = 77U; equality_twice(4U, &out);
  out = UINT_MAX-2U; equality_rmw(0U, 5U, &out);
  out = UINT_MAX-2U; equality_rmw(UINT_MAX-1U, 1U, &out);
  return 0;
}
