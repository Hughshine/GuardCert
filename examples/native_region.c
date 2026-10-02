#include <stdio.h>
#include <stdint.h>

unsigned int guarded_region(unsigned int x) {
  int result;
  { result = (x + 1U < x); x = 7U; }
  return result + x;
}

unsigned int guarded_region_in_loop(unsigned int x) {
  int result = 0;
  unsigned int i;
  for (i = 0; i < 3; ++i) {
    { result = (x + 1U < x); x = 7U; }
  }
  return result + x;
}

unsigned int guarded_region_with_goto(unsigned int x) {
  int result;
  goto work;
work:
  { result = (x + 1U < x); x = 7U; }
  return result + x;
}

unsigned int same_temporary_excluded(unsigned int x) {
  { x = (x + 1U < x); x = 7U; }
  return x;
}

int main(void) {
  unsigned int inputs[] = {0U, 6U, 7U, 8U, 2147483648U, 4294967295U};
  unsigned int i;
  for (i = 0; i < sizeof(inputs) / sizeof(inputs[0]); ++i) {
    unsigned int x = inputs[i];
    printf("region %u %u %u %u %u\n", x, guarded_region(x),
      guarded_region_in_loop(x), guarded_region_with_goto(x), same_temporary_excluded(x));
  }
  return 0;
}
