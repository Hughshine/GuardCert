#include <stdio.h>
#include <limits.h>

const unsigned int readonly_upper = 7;

void indexed_bound_loop(unsigned int *out, unsigned int *bound) {
  int i = 0;
  for (; i < (int)*bound; ++i) out[i] = (unsigned int)i + 1U;
  printf("exit %d\n", i);
}
void indexed_bound_goto(unsigned int *out, unsigned int *bound) {
  int i = 0;
  goto work;
work:
  for (; i < (int)*bound; ++i) out[i] = (unsigned int)i + 1U;
  printf("exit %d\n", i);
}
void indexed_bound_enclosing(unsigned int *out, unsigned int *bound) {
  int i = 0, repeat;
  for (repeat = 0; repeat < 2; ++repeat) {
    for (i = 0; i < (int)*bound; ++i) out[i] = (unsigned int)i + 1U;
  }
  printf("exit %d\n", i);
}
void indexed_bound_forever(unsigned int *out, unsigned int *bound) {
  int i;
  while (1) {
    i = 0;
    for (; i < (int)*bound; ++i) out[i] = (unsigned int)i + 1U;
  }
}
void indexed_bound_changed(unsigned int *out, unsigned int *bound) {
  int i = 0;
  for (; i < (int)*bound; ++i) {
    out[i] = (unsigned int)i + 1U;
    bound = bound + 1;
  }
}
void indexed_bound_volatile(unsigned int *out, volatile unsigned int *bound) {
  int i = 0;
  for (; i < (int)*bound; ++i) out[i] = (unsigned int)i + 1U;
}
void indexed_bound_wrong_index(unsigned int *out, unsigned int *bound) {
  int i = 0;
  for (; i < (int)*bound; ++i) out[i+1] = (unsigned int)i + 1U;
}
void emit(unsigned int *buffer, unsigned int other) {
  int k;
  printf("cells");
  for (k = 0; k < 48; ++k) printf(" %u", buffer[k]);
  printf(" other %u\n", other);
}
int main(void) {
  unsigned int buffer[48], other, small[3];
  int n, start, q, k;
  for (n = 0; n <= 20; ++n) {
    for (start = 0; start <= 4; start += 4) {
      for (q = 0; q <= 24; ++q) {
        for (k = 0; k < 48; ++k) buffer[k] = 7U;
        buffer[q] = (unsigned int)n;
        indexed_bound_loop(buffer+start, buffer+q);
        emit(buffer, 7U);
      }
    }
  }
  for (n = 1; n <= 20; ++n) {
    for (k = 0; k < 48; ++k) buffer[k] = 7U;
    other = (unsigned int)n;
    indexed_bound_loop(buffer, &other);
    emit(buffer, other);
  }
  for (k = 0; k < 48; ++k) buffer[k] = 7U;
  indexed_bound_loop(buffer, (unsigned int *)&readonly_upper);
  emit(buffer, readonly_upper);
  other = 0U; indexed_bound_loop((unsigned int *)0, &other);
  other = (unsigned int)-3; indexed_bound_loop((unsigned int *)0, &other);
  other = UINT_MAX; indexed_bound_loop((unsigned int *)0, &other);
  other = (unsigned int)INT_MIN; indexed_bound_loop((unsigned int *)0, &other);
  small[0] = 7U; small[1] = 7U; small[2] = 8U;
  indexed_bound_loop(small, small+2);
  printf("small %u %u %u\n", small[0], small[1], small[2]);
  small[0] = 7U; small[1] = 7U; small[2] = (unsigned int)INT_MAX;
  indexed_bound_loop(small, small+2);
  printf("small %u %u %u\n", small[0], small[1], small[2]);
  for (k = 0; k < 48; ++k) buffer[k] = 7U;
  other = 4U;
  indexed_bound_goto(buffer, &other);
  emit(buffer, other);
  for (k = 0; k < 48; ++k) buffer[k] = 7U;
  buffer[1] = 4U;
  indexed_bound_enclosing(buffer, buffer+1);
  emit(buffer, 7U);
  return 0;
}
