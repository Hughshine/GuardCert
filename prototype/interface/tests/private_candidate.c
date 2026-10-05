#include <stdio.h>

int direct(int seed) {
  int result;
  result = 5;
  return result + seed;
}

int loop(int n) {
  int i, result, sum = 0;
  for (i = 0; i < n; ++i) {
    result = 5;
    sum += result;
  }
  return sum;
}

int jump(int seed) {
  int result;
  goto inside;
inside:
  result = 5;
  return result + seed;
}

void forever(void) {
  int result;
  for (;;) {
    result = 5;
  }
}

int main(void) {
  int seed, n, failures = 0, checksum = 0;
  for (seed = -17; seed <= 17; ++seed) {
    int a = direct(seed), b = jump(seed);
    failures += (a != seed + 5) + (b != seed + 5);
    checksum += a + b;
  }
  for (n = -2; n <= 10; ++n) {
    int value = loop(n);
    failures += value != (n > 0 ? 5 * n : 0);
    checksum += value;
  }
  printf("%d %d\n", checksum, failures);
  return failures != 0;
}
