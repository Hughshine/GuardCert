#include <stdio.h>
#include <limits.h>

typedef int (*Kernel)(int *, int *, int *, int, int *);
static const int readonly_rows = 1;
static const int readonly_columns = 1;

int dual_unit(int *out, int *rows, int *columns, int start, int *exit_column) {
  int i, j = 99;
  for (i = start; i < *rows; ++i)
    for (j = 0; j < *columns; ++j) *out = 2;
  *exit_column = j;
  return i;
}
int dual_jump(int *out, int *rows, int *columns, int start, int *exit_column) {
  int i, j = 99;
  goto before_loop;
before_loop:
  for (i = start; i < *rows; ++i)
    for (j = 0; j < *columns; ++j) *out = 2;
  *exit_column = j;
  return i;
}
int dual_enclosing(int *out, int *rows, int *columns, int start, int *exit_column) {
  int i, j = 99, repeat;
  for (repeat = 0; repeat < 2; ++repeat)
    for (i = start; i < *rows; ++i)
      for (j = 0; j < *columns; ++j) *out = 2;
  *exit_column = j;
  return i;
}
int dual_unread(int *out, int *rows, int *maybe_columns, int start, int *exit_column) {
  int i, j = 99, *columns;
  if (*rows > 0) columns = maybe_columns;
  for (i = start; i < *rows; ++i)
    for (j = 0; j < *columns; ++j) *out = 2;
  *exit_column = j;
  return i;
}
int dual_sequential(int *out, int *rows, int *columns, int start, int *exit_column) {
  int i, j = 99;
  for (i = start; i < *rows; ++i)
    for (j = 0; j < *columns; ++j) *out = 2;
  *rows = 1;
  *columns = 1;
  for (i = 0; i < *rows; ++i)
    for (j = 0; j < *columns; ++j) *out = 2;
  *exit_column = j;
  return i;
}
void dual_forever(int *out, int *rows, int *columns) {
  int i, j;
  for (;;)
    for (i = 0; i < *rows; ++i)
      for (j = 0; j < *columns; ++j) *out = 2;
}
int refused_outer_volatile(int *out, volatile int *rows, int *columns) {
  int i, j = 99;
  for (i = 0; i < *rows; ++i)
    for (j = 0; j < *columns; ++j) *out = 2;
  return j;
}
int refused_inner_volatile(int *out, int *rows, volatile int *columns) {
  int i, j = 99;
  for (i = 0; i < *rows; ++i)
    for (j = 0; j < *columns; ++j) *out = 2;
  return j;
}
int refused_increment(int *out, int *rows, int *columns) {
  int i, j = 99;
  for (i = 0; i < *rows; ++i)
    for (j = 0; j < *columns; j += 2) *out = 2;
  return j;
}
int refused_store(int *out, int *rows, int *columns) {
  int i, j = 99;
  for (i = 0; i < *rows; ++i)
    for (j = 0; j < *columns; ++j) *out = 3;
  return j;
}
int refused_reset(int *out, int *rows, int *columns) {
  int i, j = 99;
  for (i = 0; i < *rows; ++i)
    for (j = 1; j < *columns; ++j) *out = 2;
  return j;
}

static void run_case(const char *tag, Kernel fn, int start, int n, int m, int layout, int seed) {
  int cells[4] = {n, m, seed, 777};
  int *rows = &cells[0];
  int *columns = layout >= 3 ? rows : &cells[1];
  int *out = layout == 1 || layout == 3 ? rows : layout == 2 ? columns : &cells[2];
  int j;
  int i = fn(out, rows, columns, start, &j);
  printf("%s %d %d %d %d %d %d %d %d %d %d %d\n", tag, start, n, m, layout, seed,
         i, j, cells[0], cells[1], cells[2], cells[3]);
}
int main(void) {
  int starts[4] = {-1, 0, 1, 3};
  int bounds[5] = {-1, 0, 1, 2, 4};
  int seeds[2] = {-9, 7};
  int s, n, m, layout, v, i, j, out;
  for (s = 0; s < 4; ++s)
    for (n = 0; n < 5; ++n)
      for (m = 0; m < 5; ++m)
        for (layout = 0; layout < 5; ++layout)
          for (v = 0; v < 2; ++v) {
            run_case("unit", dual_unit, starts[s], bounds[n], bounds[m], layout, seeds[v]);
            run_case("jump", dual_jump, starts[s], bounds[n], bounds[m], layout, seeds[v]);
            run_case("nested", dual_enclosing, starts[s], bounds[n], bounds[m], layout, seeds[v]);
          }
  for (n = -1; n <= 0; ++n) {
    i = dual_unit(0, &n, 0, 0, &j);
    printf("outerempty %d %d %d\n", n, i, j);
    i = dual_unread(0, &n, 0, 0, &j);
    printf("unread %d %d %d\n", n, i, j);
  }
  for (n = 1; n <= 4; ++n)
    for (m = -1; m <= 0; ++m) {
      i = dual_unit(0, &n, &m, 0, &j);
      printf("innerempty %d %d %d %d\n", n, m, i, j);
    }
  out = 7;
  i = dual_unit(&out, (int *)&readonly_rows, (int *)&readonly_columns, 0, &j);
  printf("readonly %d %d %d %d %d\n", i, j, out, readonly_rows, readonly_columns);
  out = 7;
  i = dual_unit(&out, (int *)&readonly_rows, (int *)&readonly_rows, 0, &j);
  printf("readonlyshared %d %d %d %d\n", i, j, out, readonly_rows);
  for (layout = 0; layout < 5; ++layout)
    for (n = 0; n <= 2; ++n)
      run_case("sequential", dual_sequential, 0, n, 1, layout, 7);
  n = INT_MIN;
  i = dual_unit(0, &n, 0, INT_MIN, &j);
  printf("extreme %d %d %d\n", n, i, j);
  n = INT_MAX;
  i = dual_unit(0, &n, 0, INT_MAX, &j);
  printf("extreme %d %d %d\n", n, i, j);
  n = INT_MAX; m = 0;
  i = dual_unit(0, &n, &m, INT_MAX-1, &j);
  printf("activeextreme %d %d %d %d\n", n, m, i, j);
  run_case("unit", dual_unit, 0, INT_MAX, 1, 1, 7);
  run_case("unit", dual_unit, 0, 1, INT_MAX, 2, 7);
  run_case("unit", dual_unit, 0, INT_MAX, INT_MAX, 3, 7);
  return 0;
}
