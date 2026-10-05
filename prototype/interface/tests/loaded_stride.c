#include <stdio.h>
#include <limits.h>

int cells[12];
void show_stride(const char *tag, int start, int stride, int i, int j, int *rows) {
  int k;
  printf("%s %d %d %d %d %d", tag, start, stride, i, j, *rows);
  for (k = 0; k < 12; ++k) printf(" %d", cells[k]);
  printf("\n");
}
void loaded_stride(int start, int *rows, int columns, int stride) {
  int i = start, j = 99;
  for (; i < *rows; ++i)
    for (j = 0; j < columns; ++j) cells[i*stride+j] = i*1+j+(-1);
  show_stride("stride", start, stride, i, j, rows);
}
void loaded_stride_jump(int start, int *rows, int columns, int stride) {
  int i = start, j = 99;
  goto work;
work:
  for (; i < *rows; ++i)
    for (j = 0; j < columns; ++j) cells[i*stride+j] = i*1+j+(-1);
  show_stride("jump", start, stride, i, j, rows);
}
void loaded_stride_enclosing(int start, int *rows, int columns, int stride) {
  int i = start, j = 99, repeat;
  for (repeat = 0; repeat < 2; ++repeat) {
    i = start;
    for (; i < *rows; ++i)
      for (j = 0; j < columns; ++j) cells[i*stride+j] = i*1+j+(-1);
  }
  show_stride("nested", start, stride, i, j, rows);
}
void loaded_stride_unread(int *rows) {
  int i = 0, j = 99, columns, stride, reported = -77;
  if (*rows > 0) { columns = 3; stride = 4; reported = stride; }
  for (; i < *rows; ++i)
    for (j = 0; j < columns; ++j) cells[i*stride+j] = i*1+j+(-1);
  show_stride("unread", 0, reported, i, j, rows);
}
void loaded_stride_empty_inner(int *rows, int columns) {
  int i = 0, j = 99, stride, reported = -88;
  if (columns > 0) { stride = 4; reported = stride; }
  for (; i < *rows; ++i)
    for (j = 0; j < columns; ++j) cells[i*stride+j] = i*1+j+(-1);
  show_stride("innerempty", 0, reported, i, j, rows);
}
void loaded_stride_sequential(int *rows) {
  int i = 0, j = 99, columns = 3, stride = 3;
  for (; i < *rows; ++i)
    for (j = 0; j < columns; ++j) cells[i*stride+j] = i*1+j+(-1);
  show_stride("first", 0, stride, i, j, rows);
  *rows = 2; columns = 2; stride = 6; i = 0;
  for (; i < *rows; ++i)
    for (j = 0; j < columns; ++j) cells[i*stride+j] = i*1+j+(-1);
  show_stride("second", 0, stride, i, j, rows);
}
void loaded_stride_forever(int *rows, int columns, int stride) {
  int i = 0, j = 99;
  while (1) {
    for (; i < *rows; ++i)
      for (j = 0; j < columns; ++j) cells[i*stride+j] = i*1+j+(-1);
    i = 0;
  }
}
void refused_increment(int *rows, int columns, int stride) {
  int i = 0, j;
  for (; i < *rows; i += 2)
    for (j = 0; j < columns; ++j) cells[i*stride+j] = i*1+j+(-1);
}
void refused_volatile(volatile int *rows, int columns, int stride) {
  int i = 0, j;
  for (; i < *rows; ++i)
    for (j = 0; j < columns; ++j) cells[i*stride+j] = i*1+j+(-1);
}
void refused_mutating_stride(int *rows, int columns, int stride) {
  int i = 0, j;
  for (; i < *rows; ++i)
    for (j = 0; j < columns; ++j) { cells[i*stride+j] = i*1+j+(-1); stride = 4; }
}
void refused_extent(int *rows, int columns, int stride) {
  int large[13], i = 0, j;
  for (; i < *rows; ++i)
    for (j = 0; j < columns; ++j) large[i*stride+j] = i*1+j+(-1);
}
void initialize_cells(int seed) {
  int k;
  for (k = 0; k < 12; ++k) cells[k] = seed+k;
}
/* This harness admits only short, defined source executions. It computes
   addresses in a wider type before deciding whether to call the source. */
int legal_case(int start, int upper, int columns, int stride, int alias, int seed, int repeats) {
  int model[12], k, i, j, r, budget = 80;
  long long product, index;
  for (k = 0; k < 12; ++k) model[k] = seed+k;
  if (alias >= 0) model[alias] = upper;
  for (r = 0; r < repeats; ++r) {
    i = start;
    while (i < (alias < 0 ? upper : model[alias])) {
      if (budget-- <= 0 || i == INT_MAX) return 0;
      j = 0;
      while (j < columns) {
        if (j > 12) return 0;
        product = (long long)i*stride; index = product+j;
        if (product < INT_MIN || product > INT_MAX || index < 0 || index >= 12) return 0;
        model[(int)index] = i+j-1;
        ++j;
      }
      ++i;
    }
  }
  return 1;
}
void dispatch_case(int context, int start, int upper, int columns, int stride, int alias, int seed) {
  int rows = upper;
  initialize_cells(seed);
  if (alias >= 0) cells[alias] = upper;
  if (context == 0) loaded_stride(start, alias < 0 ? &rows : &cells[alias], columns, stride);
  if (context == 1) loaded_stride_jump(start, alias < 0 ? &rows : &cells[alias], columns, stride);
  if (context == 2) loaded_stride_enclosing(start, alias < 0 ? &rows : &cells[alias], columns, stride);
}
int main(void) {
  int upper, start, columns, stride, seed, alias, context, rows;
  for (upper = 0; upper <= 4; ++upper)
    for (start = 0; start <= 2; ++start)
      for (columns = 0; columns <= 4; ++columns)
        for (stride = -1; stride <= 13; ++stride)
          for (seed = -2; seed <= 5; seed += 7)
            for (alias = -1; alias < 12; ++alias)
              for (context = 0; context < 3; ++context)
                if (legal_case(start, upper, columns, stride, alias, seed, context == 2 ? 2 : 1))
                  dispatch_case(context, start, upper, columns, stride, alias, seed);
  for (context = 0; context < 3; ++context) {
    dispatch_case(context, 0, 8, 3, 4, 0, 9);
    dispatch_case(context, 0, INT_MAX, 3, 4, 0, 9);
    dispatch_case(context, INT_MIN, INT_MIN, INT_MAX, INT_MIN, -1, 9);
    dispatch_case(context, INT_MAX, INT_MAX, INT_MAX, INT_MAX, -1, 9);
    dispatch_case(context, 0, 3, -1, INT_MIN, -1, 9);
    dispatch_case(context, 0, 1, 5, 4, -1, 9);
    dispatch_case(context, 0, 1, 3, INT_MIN, -1, 9);
    dispatch_case(context, 0, 1, 3, INT_MAX, -1, 9);
    for (stride = 1; stride <= 12; ++stride)
      dispatch_case(context, 0, 12/stride, stride, stride, -1, 9);
  }
  for (upper = -3; upper <= 3; upper += 3) {
    rows = upper; initialize_cells(9); loaded_stride_unread(&rows);
  }
  for (upper = 0; upper <= 3; ++upper)
    for (columns = -1; columns <= 0; ++columns) {
      rows = upper; initialize_cells(9); loaded_stride_empty_inner(&rows, columns);
    }
  for (seed = -2; seed <= 2; ++seed) {
    rows = 3; initialize_cells(seed); loaded_stride_sequential(&rows);
  }
  return 0;
}
