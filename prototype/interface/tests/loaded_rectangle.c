#include <stdio.h>
#include <limits.h>

int cells[12];
void show_rectangle(const char *tag, int start, int i, int j, int *rows) {
  int k;
  printf("%s %d %d %d %d", tag, start, i, j, *rows);
  for (k = 0; k < 12; ++k) printf(" %d", cells[k]);
  printf("\n");
}
void loaded_rectangle(int start, int *rows, int columns) {
  int i = start, j = 99;
  for (; i < *rows; ++i)
    for (j = 0; j < columns; ++j) cells[i*4+j] = i*1+j+(-1);
  show_rectangle("rectangle", start, i, j, rows);
}
void loaded_rectangle_jump(int start, int *rows, int columns) {
  int i = start, j = 99;
  goto work;
work:
  for (; i < *rows; ++i)
    for (j = 0; j < columns; ++j) cells[i*4+j] = i*1+j+(-1);
  show_rectangle("jump", start, i, j, rows);
}
void loaded_rectangle_enclosing(int start, int *rows, int columns) {
  int i = start, j = 99, repeat;
  for (repeat = 0; repeat < 2; ++repeat) {
    i = start;
    for (; i < *rows; ++i)
      for (j = 0; j < columns; ++j) cells[i*4+j] = i*1+j+(-1);
  }
  show_rectangle("nested", start, i, j, rows);
}
void loaded_rectangle_unread(int *rows) {
  int i = 0, j = 99, columns;
  if (*rows > 0) columns = 3;
  for (; i < *rows; ++i)
    for (j = 0; j < columns; ++j) cells[i*4+j] = i*1+j+(-1);
  show_rectangle("unread", 0, i, j, rows);
}
void loaded_rectangle_sequential(int *rows) {
  int i = 0, j = 99, columns = 4;
  for (; i < *rows; ++i)
    for (j = 0; j < columns; ++j) cells[i*4+j] = i*1+j+(-1);
  show_rectangle("first", 0, i, j, rows);
  *rows = 2; columns = 3; i = 0;
  for (; i < *rows; ++i)
    for (j = 0; j < columns; ++j) cells[i*4+j] = i*1+j+(-1);
  show_rectangle("second", 0, i, j, rows);
}
void loaded_rectangle_forever(int *rows, int columns) {
  int i = 0, j = 99;
  while (1) {
    for (; i < *rows; ++i)
      for (j = 0; j < columns; ++j) cells[i*4+j] = i*1+j+(-1);
    i = 0;
  }
}
void refused_increment(int *rows, int columns) {
  int i = 0, j;
  for (; i < *rows; i += 2)
    for (j = 0; j < columns; ++j) cells[i*4+j] = i*1+j+(-1);
}
void refused_volatile(volatile int *rows, int columns) {
  int i = 0, j;
  for (; i < *rows; ++i)
    for (j = 0; j < columns; ++j) cells[i*4+j] = i*1+j+(-1);
}
void refused_layout(int *rows, int columns) {
  int i = 0, j;
  for (; i < *rows; ++i)
    for (j = 0; j < columns; ++j) cells[i*0+j] = i*1+j+(-1);
}
void refused_check_size(int *rows, int columns) {
  int large[256], i = 0, j;
  for (; i < *rows; ++i)
    for (j = 0; j < columns; ++j) large[i*1+j] = i*1+j+(-1);
}
void initialize_cells(int seed) {
  int k;
  for (k = 0; k < 12; ++k) cells[k] = seed+k;
}
/* Select only defined, short source executions. The independent Python
   model selects the same cases and checks every resulting cell and exit. */
int legal_case(int start, int upper, int columns, int alias, int seed, int repeats) {
  int model[12], k, i, j, r, index, budget = 20;
  for (k = 0; k < 12; ++k) model[k] = seed+k;
  if (alias >= 0) model[alias] = upper;
  for (r = 0; r < repeats; ++r) {
    i = start;
    while (i < (alias < 0 ? upper : model[alias])) {
      if (budget-- <= 0 || i == INT_MAX) return 0;
      j = 0;
      while (j < columns) {
        if (j > 12 || i < 0 || i > 3) return 0;
        index = i*4+j;
        if (index < 0 || index >= 12) return 0;
        model[index] = i+j-1;
        ++j;
      }
      ++i;
    }
  }
  return 1;
}
void dispatch_case(int context, int start, int upper, int columns, int alias, int seed) {
  int rows = upper;
  initialize_cells(seed);
  if (alias >= 0) cells[alias] = upper;
  if (context == 0) loaded_rectangle(start, alias < 0 ? &rows : &cells[alias], columns);
  if (context == 1) loaded_rectangle_jump(start, alias < 0 ? &rows : &cells[alias], columns);
  if (context == 2) loaded_rectangle_enclosing(start, alias < 0 ? &rows : &cells[alias], columns);
}
int main(void) {
  int upper, start, columns, seed, alias, context, rows;
  for (upper = 0; upper <= 3; ++upper)
    for (start = 0; start <= 3; ++start)
      for (columns = 0; columns <= 4; ++columns)
        for (seed = -2; seed <= 5; seed += 7)
          for (alias = -1; alias < 12; ++alias)
            for (context = 0; context < 3; ++context)
              if (legal_case(start, upper, columns, alias, seed, context == 2 ? 2 : 1))
                dispatch_case(context, start, upper, columns, alias, seed);
  for (context = 0; context < 3; ++context) {
    dispatch_case(context, 0, 8, 3, 0, 9);
    dispatch_case(context, 0, INT_MAX, 3, 0, 9);
    dispatch_case(context, INT_MIN, INT_MIN, INT_MAX, -1, 9);
    dispatch_case(context, INT_MAX, INT_MAX, INT_MAX, -1, 9);
    dispatch_case(context, 0, 3, -1, -1, 9);
    dispatch_case(context, 0, 1, 5, -1, 9);
  }
  for (upper = -3; upper <= 3; upper += 3) {
    rows = upper; initialize_cells(9); loaded_rectangle_unread(&rows);
  }
  for (seed = -2; seed <= 2; ++seed) {
    rows = 3; initialize_cells(seed); loaded_rectangle_sequential(&rows);
  }
  return 0;
}
