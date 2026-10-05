#include <stdio.h>
#include <limits.h>

int cells[4];
void show_matrix(const char *tag, int start, int i, int j, int *rows) {
  printf("%s %d %d %d %d %d %d %d %d\n", tag, start, i, j, *rows, cells[0], cells[1], cells[2], cells[3]);
}
void loaded_matrix(int start, int *rows, int columns) {
  int i = start, j = 99;
  for (; i < *rows; ++i) {
    for (j = 0; j < columns; ++j) cells[i*2+j] = i*10+j+1;
  }
  show_matrix("matrix", start, i, j, rows);
}
void loaded_matrix_jump(int start, int *rows, int columns) {
  int i = start, j = 99;
  goto work;
work:
  for (; i < *rows; ++i) {
    for (j = 0; j < columns; ++j) cells[i*2+j] = i*10+j+1;
  }
  show_matrix("jump", start, i, j, rows);
}
void loaded_matrix_enclosing(int start, int *rows, int columns) {
  int i = start, j = 99, repeat;
  for (repeat = 0; repeat < 2; ++repeat) {
    i = start;
    for (; i < *rows; ++i) {
      for (j = 0; j < columns; ++j) cells[i*2+j] = i*10+j+1;
    }
  }
  show_matrix("nested", start, i, j, rows);
}
void loaded_matrix_unread(int *rows) {
  int i = 0, j = 99, columns;
  if (*rows > 0) columns = 2;
  for (; i < *rows; ++i) {
    for (j = 0; j < columns; ++j) cells[i*2+j] = i*10+j+1;
  }
  show_matrix("unread", 0, i, j, rows);
}
void loaded_matrix_sequential(int *rows) {
  int i = 0, j = 99, columns = 2;
  for (; i < *rows; ++i) {
    for (j = 0; j < columns; ++j) cells[i*2+j] = i*10+j+1;
  }
  show_matrix("first", 0, i, j, rows);
  *rows = 1;
  i = 0;
  for (; i < *rows; ++i) {
    for (j = 0; j < columns; ++j) cells[i*2+j] = i*10+j+1;
  }
  show_matrix("second", 0, i, j, rows);
}
void loaded_matrix_forever(int *rows, int columns) {
  int i = 0, j = 99;
  while (1) {
    for (; i < *rows; ++i) {
      for (j = 0; j < columns; ++j) cells[i*2+j] = i*10+j+1;
    }
    i = 0;
  }
}
void refused_value(int *rows, int columns) {
  int i = 0, j;
  for (; i < *rows; ++i)
    for (j = 0; j < columns; ++j) cells[i*2+j] = 99;
}
void refused_increment(int *rows, int columns) {
  int i = 0, j;
  for (; i < *rows; i += 2)
    for (j = 0; j < columns; ++j) cells[i*2+j] = i*10+j+1;
}
void refused_volatile(volatile int *rows, int columns) {
  int i = 0, j;
  for (; i < *rows; ++i)
    for (j = 0; j < columns; ++j) cells[i*2+j] = i*10+j+1;
}
void initialize_cells(int seed) {
  int k;
  for (k = 0; k < 4; ++k) cells[k] = seed+k;
}
int main(void) {
  int upper, start, columns, seed, alias, context, rows;
  for (upper = 0; upper <= 2; ++upper) {
    for (start = 0; start <= upper; ++start) {
      for (columns = -1; columns <= 2; ++columns) {
        for (seed = -1; seed <= 1; ++seed) {
          for (alias = -1; alias <= 1; ++alias) {
            for (context = 0; context < 3; ++context) {
              initialize_cells(seed); rows = upper;
              if (alias >= 0) cells[alias] = upper;
              if (context == 0) loaded_matrix(start, alias < 0 ? &rows : &cells[alias], columns);
              if (context == 1) loaded_matrix_jump(start, alias < 0 ? &rows : &cells[alias], columns);
              if (context == 2) loaded_matrix_enclosing(start, alias < 0 ? &rows : &cells[alias], columns);
            }
          }
        }
      }
    }
  }
  for (alias = 2; alias <= 3; ++alias) {
    initialize_cells(9); cells[alias] = 0; loaded_matrix(0, &cells[alias], 2);
    initialize_cells(9); cells[alias] = 0; loaded_matrix_jump(0, &cells[alias], 2);
    initialize_cells(9); cells[alias] = 0; loaded_matrix_enclosing(0, &cells[alias], 2);
  }
  rows = INT_MIN; initialize_cells(9); loaded_matrix(INT_MIN, &rows, INT_MAX);
  rows = INT_MAX; initialize_cells(9); loaded_matrix(INT_MAX, &rows, INT_MAX);
  rows = INT_MIN; initialize_cells(9); loaded_matrix_jump(INT_MIN, &rows, INT_MAX);
  rows = INT_MAX; initialize_cells(9); loaded_matrix_jump(INT_MAX, &rows, INT_MAX);
  rows = INT_MIN; initialize_cells(9); loaded_matrix_enclosing(INT_MIN, &rows, INT_MAX);
  rows = INT_MAX; initialize_cells(9); loaded_matrix_enclosing(INT_MAX, &rows, INT_MAX);
  rows = -3; initialize_cells(9); loaded_matrix_unread(&rows);
  rows = 0; initialize_cells(9); loaded_matrix_unread(&rows);
  rows = 2; initialize_cells(9); loaded_matrix_unread(&rows);
  for (seed = -2; seed <= 2; ++seed) {
    rows = 2; initialize_cells(seed); loaded_matrix_sequential(&rows);
  }
  return 0;
}
