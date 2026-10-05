#include <stdio.h>
#include <limits.h>

int cells[4];
int wide_cells[6];
static const int readonly_two = 2;
typedef int (*Kernel)(int *, int *, int, int *);

int dual_matrix(int *rows, int *columns, int start, int *exit_column) {
  int i, j = 99;
  for (i = start; i < *rows; ++i)
    for (j = 0; j < *columns; ++j) cells[i*2+j] = i*10+j+1;
  *exit_column = j;
  return i;
}
int dual_matrix_jump(int *rows, int *columns, int start, int *exit_column) {
  int i, j = 99;
  goto work;
work:
  for (i = start; i < *rows; ++i)
    for (j = 0; j < *columns; ++j) cells[i*2+j] = i*10+j+1;
  *exit_column = j;
  return i;
}
int dual_matrix_enclosing(int *rows, int *columns, int start, int *exit_column) {
  int i, j = 99, repeat;
  for (repeat = 0; repeat < 2; ++repeat)
    for (i = start; i < *rows; ++i)
      for (j = 0; j < *columns; ++j) cells[i*2+j] = i*10+j+1;
  *exit_column = j;
  return i;
}
int dual_matrix_unread(int *rows, int *maybe_columns, int start, int *exit_column) {
  int i, j = 99, *columns;
  if (*rows > start) columns = maybe_columns;
  for (i = start; i < *rows; ++i)
    for (j = 0; j < *columns; ++j) cells[i*2+j] = i*10+j+1;
  *exit_column = j;
  return i;
}
int dual_matrix_sequential(int *rows, int *columns, int start, int *exit_column) {
  int i, j = 99;
  for (i = start; i < *rows; ++i)
    for (j = 0; j < *columns; ++j) cells[i*2+j] = i*10+j+1;
  *rows = 2;
  *columns = 2;
  for (i = 0; i < *rows; ++i)
    for (j = 0; j < *columns; ++j) cells[i*2+j] = i*10+j+1;
  *exit_column = j;
  return i;
}
void dual_matrix_forever(int *rows, int *columns) {
  int i, j;
  for (;;)
    for (i = 0; i < *rows; ++i)
      for (j = 0; j < *columns; ++j) cells[i*2+j] = i*10+j+1;
}
int refused_outer_volatile(volatile int *rows, int *columns) {
  int i, j;
  for (i = 0; i < *rows; ++i)
    for (j = 0; j < *columns; ++j) cells[i*2+j] = i*10+j+1;
  return j;
}
int refused_inner_volatile(int *rows, volatile int *columns) {
  int i, j;
  for (i = 0; i < *rows; ++i)
    for (j = 0; j < *columns; ++j) cells[i*2+j] = i*10+j+1;
  return j;
}
int refused_increment(int *rows, int *columns) {
  int i, j;
  for (i = 0; i < *rows; i += 2)
    for (j = 0; j < *columns; ++j) cells[i*2+j] = i*10+j+1;
  return j;
}
int refused_store(int *rows, int *columns) {
  int i, j;
  for (i = 0; i < *rows; ++i)
    for (j = 0; j < *columns; ++j) cells[i*2+j] = 42;
  return j;
}
int refused_reset(int *rows, int *columns) {
  int i, j;
  for (i = 0; i < *rows; ++i)
    for (j = 1; j < *columns; ++j) cells[i*2+j] = i*10+j+1;
  return j;
}
int refused_extent(int *rows, int *columns) {
  int i, j;
  for (i = 0; i < *rows; ++i)
    for (j = 0; j < *columns; ++j) wide_cells[i*2+j] = i*10+j+1;
  return j;
}

static void initialize(int seed) {
  int k;
  for (k = 0; k < 4; ++k) cells[k] = seed+k;
}
/* Exclude executions with an out-of-bounds store before calling a kernel.
   This bounded simulator is only fixture selection, outside the proof. */
static int permitted(int start, int n, int m, int row_alias, int column_alias, int seed, int repeats) {
  int data[4], i, j, k, repeat, budget = 80;
  for (k = 0; k < 4; ++k) data[k] = seed+k;
  if (row_alias >= 0) data[row_alias] = n;
  if (column_alias >= 0) data[column_alias] = m;
  for (repeat = 0; repeat < repeats; ++repeat) {
    i = start;
    while (i < (row_alias < 0 ? n : data[row_alias])) {
      if (budget-- <= 0 || i == INT_MAX) return 0;
      j = 0;
      while (j < (column_alias == -2 ? (row_alias < 0 ? n : data[row_alias]) :
                  column_alias == -1 ? m : data[column_alias])) {
        if (budget-- <= 0 || j == INT_MAX || i < 0 || i > 1 || j < 0 || j > 3 || i*2+j >= 4) return 0;
        data[i*2+j] = i*10+j+1;
        ++j;
      }
      ++i;
    }
  }
  return 1;
}
static void run_case(const char *tag, Kernel fn, int start, int n, int m, int ra, int ca, int seed) {
  int i, j, *rows, *columns, input_n = n, input_m = m;
  initialize(seed);
  rows = ra < 0 ? &n : &cells[ra];
  if (ra >= 0) *rows = n;
  columns = ca == -2 ? rows : ca == -1 ? &m : &cells[ca];
  if (ca >= 0) *columns = m;
  i = fn(rows, columns, start, &j);
  printf("%s %d %d %d %d %d %d %d %d %d %d %d %d %d %d\n", tag, start, input_n, input_m, ra, ca, seed,
         i, j, *rows, *columns, cells[0], cells[1], cells[2], cells[3]);
}
int main(void) {
  int starts[5] = {-1, 0, 1, 2, 3};
  int bounds[6] = {-1, 0, 1, 2, 3, 4};
  int seeds[2] = {-2, 7};
  int s, n, m, ra, ca, v, i, j;
  for (s = 0; s < 5; ++s)
    for (n = 0; n < 6; ++n)
      for (m = 0; m < 6; ++m)
        for (ra = -1; ra < 4; ++ra)
          for (ca = -2; ca < 4; ++ca)
            for (v = 0; v < 2; ++v) {
              if (permitted(starts[s], bounds[n], bounds[m], ra, ca, seeds[v], 1)) {
                run_case("matrix", dual_matrix, starts[s], bounds[n], bounds[m], ra, ca, seeds[v]);
                run_case("jump", dual_matrix_jump, starts[s], bounds[n], bounds[m], ra, ca, seeds[v]);
              }
              if (permitted(starts[s], bounds[n], bounds[m], ra, ca, seeds[v], 2))
                run_case("nested", dual_matrix_enclosing, starts[s], bounds[n], bounds[m], ra, ca, seeds[v]);
            }
  for (n = -1; n <= 0; ++n) {
    i = dual_matrix(&n, 0, 0, &j);
    printf("outerempty %d %d %d\n", n, i, j);
    i = dual_matrix_unread(&n, 0, 0, &j);
    printf("unread %d %d %d\n", n, i, j);
  }
  for (n = 1; n <= 4; ++n)
    for (m = -1; m <= 0; ++m) {
      initialize(7); i = dual_matrix(&n, &m, 0, &j);
      printf("innerempty %d %d %d %d %d %d %d %d\n", n, m, i, j, cells[0], cells[1], cells[2], cells[3]);
    }
  initialize(7); i = dual_matrix((int *)&readonly_two, (int *)&readonly_two, 0, &j);
  printf("readonlyshared %d %d %d %d %d %d %d\n", i, j, readonly_two, cells[0], cells[1], cells[2], cells[3]);
  for (n = 0; n <= 2; ++n)
    for (m = 0; m <= 2; ++m)
      for (ca = -2; ca <= -1; ++ca)
        run_case("sequential", dual_matrix_sequential, 0, n, m, -1, ca, 7);
  n = INT_MIN; i = dual_matrix(&n, 0, INT_MIN, &j);
  printf("extreme %d %d %d\n", n, i, j);
  n = INT_MAX; i = dual_matrix(&n, 0, INT_MAX, &j);
  printf("extreme %d %d %d\n", n, i, j);
  n = INT_MAX; m = 0; i = dual_matrix(&n, &m, INT_MAX-1, &j);
  printf("activeextreme %d %d %d %d\n", n, m, i, j);
  run_case("matrix", dual_matrix, 0, INT_MAX, 1, 0, -1, 7);
  run_case("matrix", dual_matrix, 0, 1, INT_MAX, -1, 0, 7);
  run_case("matrix", dual_matrix, 0, INT_MAX, INT_MAX, 0, -2, 7);
  return 0;
}
