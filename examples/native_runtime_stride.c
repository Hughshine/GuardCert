#include <stdio.h>
#include <limits.h>

int stride_global_array[16];

void stride_emit(char *tag, int *a, int i, int j) {
  int k;
  printf("%s %d %d", tag, i, j);
  for (k = 0; k < 16; ++k) printf(" %d", a[k]);
  printf("\n");
}

void stride_dynamic(int i, int n, int m, int stride) {
  int a[16], j = 99, k;
  for (k = 0; k < 16; ++k) a[k] = -999;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) a[i * stride + j] = i * 7 + j + 1;
  }
  stride_emit("dynamic", a, i, j);
}

void stride_global(int n, int m, int stride) {
  int i = 0, j = 99, k;
  for (k = 0; k < 16; ++k) stride_global_array[k] = -999;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) stride_global_array[i * stride + j] = i * 7 + j + 1;
  }
  stride_emit("global", stride_global_array, i, j);
}

void stride_goto(int n, int m, int stride) {
  int a[16], i = 0, j = 99, k;
  for (k = 0; k < 16; ++k) a[k] = -999;
  goto work;
work:
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) a[i * stride + j] = i * 7 + j + 1;
  }
  stride_emit("goto", a, i, j);
}

void stride_enclosing(int n, int m, int stride) {
  int a[16], i = 0, j = 99, k, repeat;
  for (k = 0; k < 16; ++k) a[k] = -999;
  for (repeat = 0; repeat < 2; ++repeat) {
    for (i = 0; i < n; ++i) {
      for (j = 0; j < m; ++j) a[i * stride + j] = i * 7 + j + 1;
    }
  }
  stride_emit("enclosing", a, i, j);
}

void stride_two_regions(int n, int m, int stride) {
  int a[16], i = 0, j = 99, k;
  for (k = 0; k < 16; ++k) a[k] = -999;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) a[i * stride + j] = i * 7 + j + 1;
  }
  stride_emit("first", a, i, j);
  /* A second rewrite observes the new entry stride, not the first guard. */
  stride = 1; i = 0;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) a[i * stride + j] = i * 7 + j + 1;
  }
  stride_emit("second", a, i, j);
}

int stride_unread_all(int i, int n) {
  int a[16], j = 99, m, stride;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) a[i * stride + j] = i * 7 + j + 1;
  }
  return j;
}

int stride_unread_stride(int n, int m) {
  int a[16], i = 0, j = 99, stride;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) a[i * stride + j] = i * 7 + j + 1;
  }
  return i * 100 + j;
}

/* The surrounding program can diverge; the selected fragment is finite. */
void stride_forever(int n, int m, int stride) {
  int a[16], i, j;
  while (1) {
    i = 0;
    for (; i < n; ++i) {
      for (j = 0; j < m; ++j) a[i * stride + j] = i * 7 + j + 1;
    }
  }
}

/* These fail the complete body/type certificate. */
void stride_dependent(int n, int m, int stride) {
  int a[16], i = 0, j;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) a[i * stride + j] = a[0] + i * 7 + j + 1;
  }
}
void stride_changed(int n, int m, int stride) {
  int a[16], i = 0, j;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) {
      a[i * stride + j] = i * 7 + j + 1;
      stride = stride + 1;
    }
  }
}
void stride_volatile(int n, int m, int stride) {
  volatile int a[16];
  int i = 0, j;
  for (; i < n; ++i) {
    for (j = 0; j < m; ++j) a[i * stride + j] = i * 7 + j + 1;
  }
}

int main(void) {
  int n, m, stride;
  for (stride = 0; stride <= 16; ++stride) {
    for (n = 0; n <= 4; ++n) {
      for (m = 0; m <= 4; ++m) {
        if (n == 0 || m == 0 || (n - 1) * stride + m - 1 < 16)
          stride_dynamic(0, n, m, stride);
      }
    }
  }
  stride_dynamic(1, 3, 2, 4);
  stride_dynamic(0, 1, 3, -7);
  stride_dynamic(0, 1, 3, INT_MAX);
  stride_dynamic(0, -3, 3, INT_MAX);
  stride_dynamic(0, 3, -2, INT_MAX);
  stride_global(3, 2, 4);
  stride_goto(3, 2, 4);
  stride_enclosing(3, 2, 4);
  stride_two_regions(3, 2, 4);
  printf("unread_all %d %d %d\n", stride_unread_all(0, 0),
    stride_unread_all(1, 0), stride_unread_all(0, -3));
  printf("unread_stride %d %d %d\n", stride_unread_stride(3, 0),
    stride_unread_stride(3, -2), stride_unread_stride(0, 3));
  return 0;
}
