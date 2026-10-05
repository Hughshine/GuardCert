#include <stdio.h>

typedef int (*Kernel)(unsigned *, unsigned *, int, int);
static const unsigned read_only_parameter = 7U;

int hoist(unsigned *out, unsigned *parameter, int start, int n) {
  int i;
  for (i = start; i < n; ++i) {
    *out = *parameter + (unsigned)i + 1U;
  }
  return i;
}

int jump_hoist(unsigned *out, unsigned *parameter, int start, int n) {
  int i;
  goto before_loop;
before_loop:
  for (i = start; i < n; ++i) {
    *out = *parameter + (unsigned)i + 1U;
  }
  return i;
}

int nested_hoist(unsigned *out, unsigned *parameter, int start, int n) {
  int i, repeat;
  for (repeat = 0; repeat < 2; ++repeat) {
    for (i = start; i < n; ++i) {
      *out = *parameter + (unsigned)i + 1U;
    }
  }
  return i;
}

void forever_hoist(unsigned *out, unsigned *parameter, int n) {
  int i;
  for (;;) {
    for (i = 0; i < n; ++i) {
      *out = *parameter + (unsigned)i + 1U;
    }
  }
}

int volatile_parameter(unsigned *out, volatile unsigned *parameter, int n) {
  int i;
  for (i = 0; i < n; ++i) {
    *out = *parameter + (unsigned)i + 1U;
  }
  return i;
}

int different_bias(unsigned *out, unsigned *parameter, int n) {
  int i;
  for (i = 0; i < n; ++i) {
    *out = *parameter + (unsigned)i + 2U;
  }
  return i;
}

int changing_parameter(unsigned *out, unsigned *parameter, int n) {
  int i;
  for (i = 0; i < n; ++i) {
    *out = *parameter + (unsigned)i + 1U;
    ++parameter;
  }
  return i;
}

static void run_case(const char *tag, Kernel fn, int start, int n, int alias, unsigned seed) {
  unsigned cells[3] = {777U, seed, seed ^ 0xa5a5a5a5U};
  int exit = fn(&cells[1], alias ? &cells[1] : &cells[2], start, n);
  printf("%s %d %d %d %u %d %u %u %u\n", tag, start, n, alias, seed, exit,
         cells[0], cells[1], cells[2]);
}

int main(void) {
  int starts[4] = {-2, 0, 1, 3};
  int counts[6] = {-1, 0, 1, 2, 5, 11};
  unsigned seeds[5] = {0U, 1U, 7U, 4294967294U, 4294967295U};
  int s, n, alias, v;
  for (s = 0; s < 4; ++s) {
    for (n = 0; n < 6; ++n) {
      for (alias = 0; alias < 2; ++alias) {
        for (v = 0; v < 5; ++v) {
          run_case("hoist", hoist, starts[s], counts[n], alias, seeds[v]);
          run_case("jump", jump_hoist, starts[s], counts[n], alias, seeds[v]);
          run_case("nested", nested_hoist, starts[s], counts[n], alias, seeds[v]);
        }
      }
    }
  }
  printf("null hoist %d\n", hoist(0, 0, 0, 0));
  printf("null jump %d\n", jump_hoist(0, 0, 0, 0));
  printf("null nested %d\n", nested_hoist(0, 0, 0, 0));
  for (n = 1; n <= 4; ++n) {
    unsigned out = 99U;
    int exit = hoist(&out, (unsigned *)&read_only_parameter, 0, n);
    printf("readonly %d %d %u %u\n", n, exit, out, read_only_parameter);
  }
  return 0;
}
