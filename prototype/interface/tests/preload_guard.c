#include <stdio.h>

unsigned gate(unsigned count, unsigned *bound, unsigned seed) {
  unsigned result = seed;
  if (count) if (*bound) result = seed + 1u;
  return result;
}

int main(void) {
  unsigned counts[4] = {0u, 1u, 2u, 4294967295u};
  unsigned bounds[4] = {0u, 1u, 7u, 4294967295u};
  unsigned seeds[4] = {0u, 11u, 4294967294u, 4294967295u};
  unsigned total = 0u, failures = 0u;
  unsigned i, j, k;
  for (k = 0u; k < 4u; k++) {
    unsigned observed = gate(0u, (unsigned *)0, seeds[k]);
    if (observed != seeds[k]) failures++;
    total += observed;
  }
  for (i = 0u; i < 4u; i++)
    for (j = 0u; j < 4u; j++)
      for (k = 0u; k < 4u; k++) {
        unsigned observed = gate(counts[i], &bounds[j], seeds[k]);
        unsigned expected = seeds[k] + ((counts[i] && bounds[j]) ? 1u : 0u);
        if (observed != expected) failures++;
        total += observed;
      }
  printf("%u %u\n", total, failures);
  return failures ? 1 : 0;
}
