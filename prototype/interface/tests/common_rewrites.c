#include <stdio.h>

typedef unsigned (*Kernel)(unsigned *, unsigned *, int *, int *, int, int, int, unsigned);

unsigned common_rewrites(unsigned *out, unsigned *parameter, int *bound_out, int *bound,
                         int n, int rows, int columns, unsigned count) {
  int a[16], b[4], i, j = 99, k;
  int ei, ej, ui, uj, ri, rj, mi, mj;
  unsigned result = 9U, payload;
  for (k = 0; k < 16; ++k) a[k] = -99;
  for (k = 0; k < 4; ++k) b[k] = -99;
  for (i = 0; i < n; ++i) *out = *parameter + (unsigned)i + 1U;
  payload = *out;
  for (i = 0; i < rows; ++i) {
    for (j = 0; j < columns; ++j) a[i * 4 + j] = i * 7 + j + 1;
  }
  ei = i; ej = j;
  for (i = 0; i < rows; ++i) {
    for (j = 0; j < columns; ++j) a[i * 4 + j] += i * 7 + j + 1;
  }
  ui = i; uj = j;
  for (i = 0; i < rows; ++i) {
    for (j = 0; j < columns; ++j) a[i * 4 + j] = a[i * 4] + (i * 7 + j + 1);
  }
  ri = i; rj = j;
  for (i = 0; i < rows; ++i) {
    for (j = 0; j < columns; ++j) b[i * 2 + j] = i * 10 + j + 1;
  }
  mi = i; mj = j;
  if (n % 2) {
    *out = 11U;
    *parameter = 0U;
  } else {
    *out = 11U;
    *parameter = 22U;
  }
  if (count) if (*parameter) result = result + 1U;
  for (i = 0; i < *bound; ++i) *bound_out = i + 1;
  printf("payload %u\n", payload);
  printf("exits %d %d %d %d %d %d %d %d %d\n", ei, ej, ui, uj, ri, rj, mi, mj, i);
  printf("array");
  for (k = 0; k < 16; ++k) printf(" %d", a[k]);
  for (k = 0; k < 4; ++k) printf(" %d", b[k]);
  printf("\n");
  return result;
}

int main(void) {
  int n, rows, columns, alias, bound_alias, upper;
  for (n = 0; n <= 3; ++n)
    for (rows = 1; rows <= 2; ++rows)
      for (columns = 0; columns <= 2; ++columns)
        for (alias = 0; alias < 2; ++alias)
          for (bound_alias = 0; bound_alias < 2; ++bound_alias)
            for (upper = 0; upper <= 5; ++upper) {
              unsigned words[2] = {0xffffffffU, 7U};
              int bounds[2] = {bound_alias ? upper : 99, upper};
              unsigned result;
              printf("input %d %d %d %d %d %d\n", n, rows, columns, alias, bound_alias, upper);
              result = common_rewrites(&words[0], alias ? &words[0] : &words[1],
                                       &bounds[0], bound_alias ? &bounds[0] : &bounds[1],
                                       n, rows, columns, (unsigned)(upper % 2));
              printf("result %u %u %u %d %d\n", result, words[0], words[1], bounds[0], bounds[1]);
            }
  return 0;
}
