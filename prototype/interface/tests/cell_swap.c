#include <stdio.h>

void pair(unsigned *p, unsigned *q) {
  *p = 11u;
  *q = 29u;
}

void loop_pair(unsigned *p, unsigned *q, unsigned n) {
  unsigned i;
  for (i = 0u; i < n; ++i) {
    *p = 11u;
    *q = 29u;
  }
}

/* Compile and inspect an infinite surrounding loop; do not run it. */
void forever_pair(unsigned *p, unsigned *q) {
  for (;;) {
    *p = 11u;
    *q = 29u;
  }
}

int main(void) {
  unsigned checksum = 0u, failures = 0u;
  unsigned i, j, k, n;
  for (i = 0u; i < 4u; ++i) {
    for (j = 0u; j < 4u; ++j) {
      unsigned cells[4] = {3u, 5u, 7u, 9u};
      unsigned expected[4] = {3u, 5u, 7u, 9u};
      expected[i] = 11u;
      expected[j] = 29u;
      pair(&cells[i], &cells[j]);
      for (k = 0u; k < 4u; ++k) {
        failures += cells[k] != expected[k];
        checksum += cells[k];
      }
    }
  }
  {
    unsigned left = 3u, right = 5u;
    pair(&left, &right);
    failures += left != 11u || right != 29u;
    checksum += left + right;
  }
  loop_pair((unsigned *)0, (unsigned *)0, 0u);
  for (n = 1u; n <= 4u; ++n) {
    for (i = 0u; i < 4u; ++i) {
      for (j = 0u; j < 4u; ++j) {
        unsigned cells[4] = {3u, 5u, 7u, 9u};
        unsigned expected[4] = {3u, 5u, 7u, 9u};
        expected[i] = 11u;
        expected[j] = 29u;
        loop_pair(&cells[i], &cells[j], n);
        for (k = 0u; k < 4u; ++k) {
          failures += cells[k] != expected[k];
          checksum += cells[k];
        }
      }
    }
  }
  printf("%u %u\n", checksum, failures);
  return failures != 0u;
}
