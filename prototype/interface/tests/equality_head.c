#include <stdio.h>
#include <limits.h>

void head_step2(unsigned int start, unsigned int n, unsigned int *out) {
  unsigned int i = start;
  for (; (int)i != (int)n; i = i + 2U) *out = i + 1U;
  printf("two %u %u %u %u\n", start, n, i, out ? *out : 77U);
}
void head_change(unsigned int start, unsigned int n, unsigned int delta, unsigned int *out) {
  unsigned int i = start, initial = n;
  for (; (int)i != (int)n; i = i + 1U) {
    *out = i + 1U;
    n = n - delta;
  }
  printf("change %u %u %u %u %u %u\n", start, initial, delta, i, n, out ? *out : 77U);
}
void head_jump(unsigned int start, unsigned int n, unsigned int *out) {
  unsigned int i = start;
  goto work;
work:
  for (; (int)i != (int)n; i = i + 2U) *out = i + 1U;
  printf("jump %u %u %u %u\n", start, n, i, out ? *out : 77U);
}
void head_enclosing(unsigned int start, unsigned int n, unsigned int *out) {
  unsigned int i, repeat;
  for (repeat = 0U; repeat < 2U; repeat = repeat + 1U) {
    i = start;
    for (; (int)i != (int)n; i = i + 2U) *out = i + 1U;
  }
  printf("nested %u %u %u %u\n", start, n, i, out ? *out : 77U);
}
void head_volatile(unsigned int start, unsigned int n, volatile unsigned int *out) {
  unsigned int i = start;
  for (; (int)i != (int)n; i = i + 2U) *out = i + 1U;
  printf("volatile %u %u %u %u\n", start, n, i, *out);
}
int head_value(unsigned int i, unsigned int n) {
  return (int)i != (int)n;
}
int head_assign(unsigned int i, unsigned int n) {
  int value;
  value = (int)i != (int)n;
  return value;
}
void head_odd_forever(unsigned int *out) {
  unsigned int i = 0U, n = 1U;
  for (; (int)i != (int)n; i = i + 2U) *out = i + 1U;
}
void head_target_forever(unsigned int *out) {
  unsigned int i = 0U, n = 1U;
  for (; (int)i != (int)n; i = i + 1U) {
    *out = i + 1U;
    n = n + 1U;
  }
}
void head_no_cast(unsigned int n, unsigned int *out) {
  unsigned int i = 0U;
  for (; i != n; i = i + 2U) *out = i + 1U;
}
void head_constant(unsigned int *out) {
  unsigned int i = 0U;
  for (; (int)i != 6; i = i + 2U) *out = i + 1U;
}
int head_branch_label(unsigned int i, unsigned int n) {
  if ((int)i != (int)n) goto different;
  return 9;
different:
  return 7;
}
int main(void) {
  unsigned int out, start, trips, delta, i, n;
  unsigned int values[7] = {0U, 1U, 2U, (unsigned int)INT_MAX, (unsigned int)INT_MIN, UINT_MAX-1U, UINT_MAX};
  for (start = 0U; start <= 4U; start = start + 1U) {
    for (trips = 0U; trips <= 8U; trips = trips + 1U) {
      n = start + trips * 2U;
      out = 77U; head_step2(start, n, &out);
      out = 77U; head_jump(start, n, &out);
      out = 77U; head_enclosing(start, n, &out);
      for (delta = 1U; delta <= 2U; delta = delta + 1U) {
        n = start + trips * (delta + 1U);
        out = 77U; head_change(start, n, delta, &out);
      }
    }
  }
  out = 77U; head_step2(UINT_MAX-1U, 0U, &out);
  out = 77U; head_jump(UINT_MAX, 1U, &out);
  out = 77U; head_enclosing((unsigned int)INT_MAX-1U, (unsigned int)INT_MIN, &out);
  out = 77U; head_change(UINT_MAX-1U, 1U, 2U, &out);
  out = 77U; head_change((unsigned int)INT_MIN, (unsigned int)INT_MIN+6U, 1U, &out);
  head_step2(0U, 0U, (unsigned int *)0);
  head_jump(UINT_MAX, UINT_MAX, (unsigned int *)0);
  head_enclosing((unsigned int)INT_MIN, (unsigned int)INT_MIN, (unsigned int *)0);
  head_change(0U, 0U, 2U, (unsigned int *)0);
  out = 77U; head_volatile(0U, 6U, &out);
  for (i = 0U; i < 7U; i = i + 1U) {
    for (n = 0U; n < 7U; n = n + 1U) {
      printf("value %u %u %d %d\n", values[i], values[n], head_value(values[i], values[n]), head_assign(values[i], values[n]));
    }
  }
  return 0;
}
