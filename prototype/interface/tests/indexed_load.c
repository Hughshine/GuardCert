#include <stdio.h>
#include <limits.h>

const unsigned int readonly_parameter = 7;

void indexed_loop(unsigned int *out, unsigned int *parameter, int n) {
  int i = 0;
  for (; i < n; ++i) out[i] = *parameter + (unsigned int)i + 1U;
  printf("exit %d\n", i);
}

void indexed_goto(unsigned int *out, unsigned int *parameter, int n) {
  int i = 0;
  goto work;
work:
  for (; i < n; ++i) out[i] = *parameter + (unsigned int)i + 1U;
  printf("exit %d\n", i);
}

void indexed_enclosing(unsigned int *out, unsigned int *parameter, int n) {
  int i = 0, repeat;
  for (repeat = 0; repeat < 2; ++repeat) {
    for (i = 0; i < n; ++i) out[i] = *parameter + (unsigned int)i + 1U;
  }
  printf("exit %d\n", i);
}

void indexed_forever(unsigned int *out, unsigned int *parameter, int n) {
  int i;
  while (1) {
    i = 0;
    for (; i < n; ++i) out[i] = *parameter + (unsigned int)i + 1U;
  }
}

void indexed_changed(unsigned int *out, unsigned int *parameter, int n) {
  int i = 0;
  for (; i < n; ++i) {
    out[i] = *parameter + (unsigned int)i + 1U;
    parameter = parameter + 1;
  }
}
void indexed_volatile(unsigned int *out, volatile unsigned int *parameter, int n) {
  int i = 0;
  for (; i < n; ++i) out[i] = *parameter + (unsigned int)i + 1U;
}
void indexed_wrong_index(unsigned int *out, unsigned int *parameter, int n) {
  int i = 0;
  for (; i < n; ++i) out[i+1] = *parameter + (unsigned int)i + 1U;
}

void emit(unsigned int *buffer, unsigned int other) {
  int k;
  printf("cells");
  for (k = 0; k < 48; ++k) printf(" %u", buffer[k]);
  printf(" other %u\n", other);
}

int main(void) {
  unsigned int buffer[48], other;
  int n, start, q, kind, k;
  for (n = 0; n <= 20; ++n) {
    for (start = 0; start <= 4; start += 4) {
      for (q = 0; q <= 24; ++q) {
        for (k = 0; k < 48; ++k) buffer[k] = 7U;
        other = 7U;
        indexed_loop(buffer+start, buffer+q, n);
        emit(buffer, other);
      }
    }
  }
  for (kind = 0; kind < 2; ++kind) {
    for (n = 1; n <= 20; ++n) {
      for (k = 0; k < 48; ++k) buffer[k] = 7U;
      other = 7U;
      if (kind == 0) indexed_loop(buffer, &other, n);
      else indexed_loop(buffer, (unsigned int *)&readonly_parameter, n);
      emit(buffer, other);
    }
  }
  for (k = 0; k < 48; ++k) buffer[k] = UINT_MAX;
  other = UINT_MAX;
  indexed_loop(buffer, &other, 4);
  emit(buffer, other);
  indexed_loop((unsigned int *)0, (unsigned int *)0, 0);
  indexed_loop((unsigned int *)0, (unsigned int *)0, -3);
  for (k = 0; k < 48; ++k) buffer[k] = 7U;
  other = 7U;
  indexed_goto(buffer, &other, 4);
  emit(buffer, other);
  for (k = 0; k < 48; ++k) buffer[k] = 7U;
  indexed_enclosing(buffer, buffer+1, 4);
  emit(buffer, other);
  return 0;
}
