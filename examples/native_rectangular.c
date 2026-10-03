#include <stdio.h>
#include <limits.h>

int global_rectangle[120];

void emit(char *tag, int *a, int extent, int i, int j) {
  int k;
  printf("%s %d %d", tag, i, j);
  for (k = 0; k < extent; ++k) printf(" %d", a[k]);
  printf("\n");
}

void rectangle_dynamic(int i, int n, int m) {
  int a[120], j = 99, k;
  for (k = 0; k < 120; ++k) a[k] = -999;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) a[i * 10 + j] = i * 37 + j + 7;
  }
  emit("dynamic", a, 120, i, j);
}

void rectangle_other_layout(int i, int n, int m) {
  int a[105], j = 99, k;
  for (k = 0; k < 105; ++k) a[k] = -999;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) a[i * 7 + j] = i * -11 + j + -3;
  }
  emit("other", a, 105, i, j);
}

void rectangle_goto(int n, int m) {
  int a[120], i = 0, j = 99, k;
  for (k = 0; k < 120; ++k) a[k] = -999;
  goto work;
work:
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) a[i * 10 + j] = i * 37 + j + 7;
  }
  emit("goto", a, 120, i, j);
}

void rectangle_global(int n, int m) {
  int i = 0, j = 99, k;
  for (k = 0; k < 120; ++k) global_rectangle[k] = -999;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) global_rectangle[i * 10 + j] = i * 37 + j + 7;
  }
  emit("global", global_rectangle, 120, i, j);
}

void rectangle_enclosing_loop(int n, int m) {
  int a[120], i = 0, j = 99, k, repeat;
  for (k = 0; k < 120; ++k) a[k] = -999;
  for (repeat = 0; repeat < 2; ++repeat) {
    for (i = 0; i < n; ++i) {
      for (j = 0; j < m; ++j) a[i * 10 + j] = i * 37 + j + 7;
    }
  }
  emit("enclosing", a, 120, i, j);
}

int rectangle_unread_bound(int i, int n) {
  int a[120], j = 99, m;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) a[i * 10 + j] = i * 37 + j + 7;
  }
  return j;
}

void rectangle_dependent(int n, int m) {
  int a[120], i = 0, j = 99, k;
  for (k = 0; k < 120; ++k) a[k] = -999;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) a[i * 10 + j] = a[0] + i * 37 + j + 7;
  }
  emit("dependent", a, 120, i, j);
}

void rectangle_volatile(int n, int m) {
  volatile int a[120];
  int i = 0, j = 99, k;
  for (k = 0; k < 120; ++k) a[k] = -999;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) a[i * 10 + j] = i * 37 + j + 7;
  }
  printf("volatile %d %d", i, j);
  for (k = 0; k < 120; ++k) printf(" %d", a[k]);
  printf("\n");
}

void rectangle_invalid_layout(int n, int m) {
  int a[120], i = 0, j = 99, k;
  for (k = 0; k < 120; ++k) a[k] = -999;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) a[i * 0 + j] = i * 37 + j + 7;
  }
  emit("invalid", a, 120, i, j);
}

void rectangle_update_dynamic(int i, int n, int m) {
  int a[120], j = 99, k;
  for (k = 0; k < 120; ++k) a[k] = -999;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) a[i * 10 + j] = a[i * 10 + j] + (i * 37 + j + 7);
  }
  emit("update_dynamic", a, 120, i, j);
}

void rectangle_update_other_layout(int i, int n, int m) {
  int a[105], j = 99, k;
  for (k = 0; k < 105; ++k) a[k] = -999;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) a[i * 7 + j] = a[i * 7 + j] + (i * -11 + j + -3);
  }
  emit("update_other", a, 105, i, j);
}

void rectangle_update_goto(int n, int m) {
  int a[120], i = 0, j = 99, k;
  for (k = 0; k < 120; ++k) a[k] = -999;
  goto work;
work:
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) a[i * 10 + j] = a[i * 10 + j] + (i * 37 + j + 7);
  }
  emit("update_goto", a, 120, i, j);
}

void rectangle_update_global(int n, int m) {
  int i = 0, j = 99, k;
  for (k = 0; k < 120; ++k) global_rectangle[k] = -999;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) global_rectangle[i * 10 + j] = global_rectangle[i * 10 + j] + (i * 37 + j + 7);
  }
  emit("update_global", global_rectangle, 120, i, j);
}

void rectangle_update_enclosing_loop(int n, int m) {
  int a[120], i = 0, j = 99, k, repeat;
  for (k = 0; k < 120; ++k) a[k] = -999;
  for (repeat = 0; repeat < 2; ++repeat) {
    for (i = 0; i < n; ++i) {
      for (j = 0; j < m; ++j) a[i * 10 + j] = a[i * 10 + j] + (i * 37 + j + 7);
    }
  }
  emit("update_enclosing", a, 120, i, j);
}

int rectangle_update_unread_bound(int i, int n) {
  int a[120], j = 99, m;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) a[i * 10 + j] = a[i * 10 + j] + (i * 37 + j + 7);
  }
  return j;
}

void rectangle_update_compound(int i, int n, int m) {
  int a[120], j = 99, k;
  for (k = 0; k < 120; ++k) a[k] = -999;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) a[i * 10 + j] += (i * 37 + j + 7);
  }
  emit("update_compound", a, 120, i, j);
}

void rectangle_update_neighbor(int n, int m) {
  int a[120], i = 0, j = 99, k;
  for (k = 0; k < 120; ++k) a[k] = -999;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) a[i * 10 + j] = a[0] + (i * 37 + j + 7);
  }
  emit("update_neighbor", a, 120, i, j);
}

int main(void) {
  int n, m, i;
  for (n = 1; n <= 12; ++n)
    for (m = 1; m <= 10; ++m) rectangle_dynamic(0, n, m);
  for (n = 1; n <= 15; ++n)
    for (m = 1; m <= 7; ++m) rectangle_other_layout(0, n, m);
  rectangle_dynamic(0, 2, 11);
  rectangle_dynamic(1, 4, 5);
  rectangle_dynamic(0, 13, 0);
  rectangle_dynamic(0, 3, -1);
  rectangle_dynamic(0, 0, INT_MAX);
  rectangle_dynamic(INT_MAX, INT_MAX, INT_MIN);
  rectangle_dynamic(INT_MIN, INT_MIN, INT_MAX);
  for (i = 0; i < 2; ++i) {
    n = i ? 2 : 5; m = i ? 11 : 4;
    rectangle_goto(n, m); rectangle_global(n, m); rectangle_enclosing_loop(n, m);
  }
  printf("unread %d %d %d\n", rectangle_unread_bound(0, 0),
    rectangle_unread_bound(1, 0), rectangle_unread_bound(INT_MAX, INT_MAX));
  rectangle_dependent(3, 4); rectangle_volatile(3, 4); rectangle_invalid_layout(3, 4);
  for (n = 1; n <= 12; ++n)
    for (m = 1; m <= 10; ++m) {
      rectangle_update_dynamic(0, n, m);
      rectangle_update_compound(0, n, m);
    }
  for (n = 1; n <= 15; ++n)
    for (m = 1; m <= 7; ++m) rectangle_update_other_layout(0, n, m);
  rectangle_update_dynamic(0, 2, 11);
  rectangle_update_dynamic(1, 4, 5);
  rectangle_update_dynamic(0, 13, 0);
  rectangle_update_dynamic(0, 3, -1);
  rectangle_update_dynamic(0, 0, INT_MAX);
  rectangle_update_dynamic(INT_MAX, INT_MAX, INT_MIN);
  rectangle_update_dynamic(INT_MIN, INT_MIN, INT_MAX);
  for (i = 0; i < 2; ++i) {
    n = i ? 2 : 5; m = i ? 11 : 4;
    rectangle_update_goto(n, m); rectangle_update_global(n, m); rectangle_update_enclosing_loop(n, m);
  }
  printf("update_unread %d %d %d\n", rectangle_update_unread_bound(0, 0),
    rectangle_update_unread_bound(1, 0), rectangle_update_unread_bound(INT_MAX, INT_MAX));
  rectangle_update_neighbor(3, 4);
  return 0;
}
