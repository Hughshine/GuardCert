#include <stdio.h>

int cells[12];

static void snapshot(const char *stage, int i, int j, int *rows, int *columns) {
  int k;
  printf("%s %d %d %d %d", stage, i, j, *rows, *columns);
  for (k = 0; k < 12; ++k) printf(" %d", cells[k]);
  printf("\n");
}

void common_multicache(unsigned *out, unsigned *parameter, int n,
                       int *rows, int *columns, int next_rows, int next_columns) {
  int i, j = 99, second_n = n + 1;
  for (i = 0; i < n; ++i) *out = *parameter + (unsigned)i + 1U;
  printf("payload1 %u %u %d\n", *out, *parameter, i);
  for (i = 0; i < *rows; ++i)
    for (j = 0; j < *columns; ++j) cells[i*4+j] = i*10+j+1;
  snapshot("matrix1", i, j, rows, columns);
  *parameter = 23U;
  *rows = next_rows;
  *columns = next_columns;
  for (i = 0; i < second_n; ++i) *out = *parameter + (unsigned)i + 1U;
  printf("payload2 %u %u %d\n", *out, *parameter, i);
  for (i = 0; i < *rows; ++i)
    for (j = 0; j < *columns; ++j) cells[i*4+j] = i*7+j+2;
  snapshot("matrix2", i, j, rows, columns);
}

struct Case { int rows, columns, row_index, column_index, next_rows, next_columns; };
static const struct Case cases[] = {
  {1,1,-1,-1,2,3}, {2,3,-1,-1,3,4}, {3,4,-1,-1,1,2},
  {2,2,-1,-2,3,3}, {2,3,0,-1,3,2}, {2,3,-1,0,2,4},
  {3,3,0,-2,3,3}, {2,3,11,-1,2,2}, {2,3,-1,7,3,3},
  {0,3,-1,-1,2,3}, {2,0,-1,-1,0,4}, {-1,2,-1,-1,2,0},
  {4,0,-1,-1,2,3}, {2,1,1,-1,2,3}, {2,1,-1,1,2,2}
};

int main(void) {
  int t, n, alias, k;
  for (t = 0; t < (int)(sizeof(cases)/sizeof(cases[0])); ++t)
    for (n = 0; n <= 3; ++n)
      for (alias = 0; alias <= 1; ++alias) {
        struct Case c = cases[t];
        int outer = c.rows, inner = c.columns;
        int *rows = c.row_index < 0 ? &outer : cells+c.row_index;
        int *columns = c.column_index == -2 ? rows :
                       c.column_index < 0 ? &inner : cells+c.column_index;
        unsigned words[2] = {0xffffffffU, 7U};
        for (k = 0; k < 12; ++k) cells[k] = 7+k;
        if (c.row_index >= 0) *rows = c.rows;
        if (c.column_index >= 0) *columns = c.columns;
        printf("input %d %d %d\n", t, n, alias);
        common_multicache(words, alias ? words : words+1, n, rows, columns,
                          c.next_rows, c.next_columns);
        printf("result %u %u %d %d\n", words[0], words[1], *rows, *columns);
      }
  return 0;
}
