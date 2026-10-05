#include <stdio.h>
#include <limits.h>

typedef int (*Kernel)(int *, int *, int);
static const int read_only_bound = 7;

int loaded_bound(int *out, int *bound, int start) {
  int i;
  for (i = start; i < *bound; ++i) {
    *out = i + 1;
  }
  return i;
}
int jump_bound(int *out, int *bound, int start) {
  int i;
  goto before_loop;
before_loop:
  for (i = start; i < *bound; ++i) {
    *out = i + 1;
  }
  return i;
}
int nested_bound(int *out, int *bound, int start) {
  int i, repeat;
  for (repeat = 0; repeat < 2; ++repeat) {
    for (i = start; i < *bound; ++i) {
      *out = i + 1;
    }
  }
  return i;
}
void forever_bound(int *out, int *bound) {
  int i;
  for (;;) {
    for (i = 0; i < *bound; ++i) {
      *out = i + 1;
    }
  }
}
int volatile_bound(int *out, volatile int *bound) {
  int i;
  for (i = 0; i < *bound; ++i) *out = i + 1;
  return i;
}
int different_body(int *out, int *bound) {
  int i;
  for (i = 0; i < *bound; ++i) *out = i + 2;
  return i;
}
int different_increment(int *out, int *bound) {
  int i;
  for (i = 0; i < *bound; i += 2) *out = i + 1;
  return i;
}
int nonstrict_bound(int *out, int *bound) {
  int i;
  for (i = 0; i <= *bound; ++i) *out = i + 1;
  return i;
}
static void run_case(const char *tag, Kernel fn, int start, int upper, int alias, int seed) {
  int cells[3] = {777, alias ? upper : seed, upper};
  int exit = fn(&cells[1], alias ? &cells[1] : &cells[2], start);
  printf("%s %d %d %d %d %d %d %d %d\n", tag, start, upper, alias, seed,
         exit, cells[0], cells[1], cells[2]);
}
int main(void) {
  int starts[4] = {-2, 0, 1, 3};
  int bounds[7] = {-2, -1, 0, 1, 2, 5, 11};
  int seeds[3] = {-99, 0, 99};
  int s, n, alias, v;
  for (s = 0; s < 4; ++s)
    for (n = 0; n < 7; ++n)
      for (alias = 0; alias < 2; ++alias)
        for (v = 0; v < 3; ++v) {
          run_case("bound", loaded_bound, starts[s], bounds[n], alias, seeds[v]);
          run_case("jump", jump_bound, starts[s], bounds[n], alias, seeds[v]);
          run_case("nested", nested_bound, starts[s], bounds[n], alias, seeds[v]);
        }
  n = 0;
  printf("null bound %d\n", loaded_bound(0, &n, 0));
  printf("null jump %d\n", jump_bound(0, &n, 0));
  printf("null nested %d\n", nested_bound(0, &n, 0));
  for (v = 0; v < 4; ++v) {
    int out = 99;
    int exit = loaded_bound(&out, (int *)&read_only_bound, v);
    printf("readonly %d %d %d %d\n", v, exit, out, read_only_bound);
  }
  run_case("bound", loaded_bound, INT_MAX - 1, INT_MAX, 0, 99);
  run_case("bound", loaded_bound, INT_MAX, INT_MAX, 0, 99);
  run_case("bound", loaded_bound, INT_MIN, INT_MIN + 1, 0, 99);
  return 0;
}
