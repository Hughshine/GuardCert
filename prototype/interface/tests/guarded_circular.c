#include <stdio.h>
#include <limits.h>

typedef unsigned (*Kernel)(unsigned *, unsigned *, unsigned);
static const unsigned readonly_bound = 5U;

unsigned circular(unsigned *out, unsigned *bound, unsigned start) {
  unsigned i;
  for (i = start; i != *bound; ++i) *out = i + 2U;
  return i;
}
unsigned circular_jump(unsigned *out, unsigned *bound, unsigned start) {
  unsigned i;
  goto before_loop;
before_loop:
  for (i = start; i != *bound; ++i) *out = i + 2U;
  return i;
}
unsigned circular_nested(unsigned *out, unsigned *bound, unsigned start) {
  unsigned i;
  int repeat;
  for (repeat = 0; repeat < 2; ++repeat)
    for (i = start; i != *bound; ++i) *out = i + 2U;
  return i;
}
void circular_forever(unsigned *word) {
  unsigned i;
  for (i = 0; i != *word; ++i) *word = i + 2U;
}
unsigned circular_volatile(unsigned *out, volatile unsigned *bound, unsigned start) {
  unsigned i;
  for (i = start; i != *bound; ++i) *out = i + 2U;
  return i;
}
unsigned circular_stride(unsigned *out, unsigned *bound, unsigned start) {
  unsigned i;
  for (i = start; i != *bound; i += 2U) *out = i + 2U;
  return i;
}
unsigned circular_different(unsigned *out, unsigned *bound, unsigned start) {
  unsigned i;
  for (i = start; i != *bound; ++i) *out = i + 1U;
  return i;
}
unsigned circular_mixed(unsigned *out, unsigned *bound, unsigned start, unsigned *payload, unsigned *parameter) {
  int j, count = 3;
  unsigned i, first;
  for (j = 0; j < count; ++j) *payload = *parameter + (unsigned)j + 1U;
  for (i = start; i != *bound; ++i) *out = i + 2U;
  first = i;
  *parameter = 23U;
  *bound = first + 3U;
  count = 2;
  for (j = 0; j < count; ++j) *payload = *parameter + (unsigned)j + 1U;
  for (i = first; i != *bound; ++i) *out = i + 2U;
  return i;
}

static void run_case(const char *tag, Kernel fn, unsigned start, unsigned distance, unsigned seed) {
  unsigned upper = start + distance;
  unsigned cells[4] = {111U, seed, upper, 333U};
  unsigned exit = fn(&cells[1], &cells[2], start);
  printf("%s %u %u %u %u %u %u %u\n", tag, start, distance, seed, exit,
         cells[0], cells[1], cells[2]);
}
int main(void) {
  unsigned starts[] = {0U, 1U, 7U, UINT_MAX-3U, UINT_MAX-1U, UINT_MAX};
  unsigned seeds[] = {0U, 77U, UINT_MAX};
  unsigned s, d, v, word;
  for (s = 0; s < 6; ++s)
    for (d = 0; d < 9; ++d)
      for (v = 0; v < 3; ++v) {
        run_case("loop", circular, starts[s], d, seeds[v]);
        run_case("jump", circular_jump, starts[s], d, seeds[v]);
        run_case("nested", circular_nested, starts[s], d, seeds[v]);
      }
  for (s = 0; s < 6; ++s) {
    word = starts[s];
    printf("alias-empty %u %u\n", circular(&word, &word, starts[s]), word);
    printf("null-empty %u\n", circular(0, &word, starts[s]));
  }
  for (s = 0; s < 6; ++s) {
    unsigned start = readonly_bound - s;
    unsigned out = 99U;
    unsigned exit = circular(&out, (unsigned *)&readonly_bound, start);
    printf("readonly %u %u %u %u\n", start, exit, out, readonly_bound);
  }
  for (s = 0; s < 6; ++s)
    for (d = 0; d < 6; ++d) {
      unsigned upper = starts[s] + d;
      unsigned cells[2] = {77U, upper};
      unsigned parameter = 9U, payload = UINT_MAX;
      unsigned exit = circular_mixed(&cells[0], &cells[1], starts[s], &payload, &parameter);
      printf("mixed %u %u %u %u %u %u %u\n", starts[s], d, exit, cells[0], cells[1], payload, parameter);
    }
  return 0;
}
