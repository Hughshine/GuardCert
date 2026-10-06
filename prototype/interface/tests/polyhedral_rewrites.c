#include <stdio.h>

/* Two distinct replacements share private resources while public state and
   surrounding control remain observable. */
void polyhedral_pair(int n, int m) {
  int a[120], b[120], i = 0, j = 99, k, cookie = 17;
  for (k = 0; k < 120; ++k) { a[k] = -999; b[k] = -777; }
  goto before;
  cookie = -1;
before:
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) {
      a[i * 10 + j] = i * 37 + j + 7;
      b[i * 10 + j] = a[i * 10 + j] + (i * 11 + j + 19);
    }
  }
  cookie += i + j;
  i = 0; j = 77;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) {
      a[i * 10 + j] = a[i * 10 + j] + (i * 23 + j + 3);
      b[i * 10 + j] = a[i * 10 + j];
    }
  }
  printf("pair %d %d %d", cookie, i, j);
  for (k = 0; k < 120; ++k) printf(" %d %d", a[k], b[k]);
  putchar('\n');
}

/* This function is only called with n <= 0. The source never observes m;
   the generated guard must refuse before attempting that observation. */
void polyhedral_unread(int n) {
  int a[120], i = 0, j = 99, m;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) a[i * 10 + j] = i * 37 + j + 7;
  }
  printf("unread %d %d\n", i, j);
}

int main(void) {
  int n, m;
  for (n = 0; n <= 12; ++n)
    for (m = 0; m <= 10; ++m) polyhedral_pair(n, m);
  polyhedral_pair(-1, 10);
  polyhedral_pair(3, -1);
  /* The source is defined despite bounds outside the modeled layout, because
     these calls perform no array accesses. They must execute the fallback. */
  polyhedral_pair(13, 0);
  polyhedral_pair(0, 11);
  polyhedral_unread(0);
  polyhedral_unread(-1);
  return 0;
}
