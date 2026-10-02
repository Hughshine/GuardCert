extern int printf(const char *, ...);

/* Volatile inputs keep the executable demonstration dynamic. */
volatile unsigned inputs[] = {0u, 1u, 254u, 255u, 4294967294u, 4294967295u};

unsigned probe(unsigned x)
{
    if (x + 1u < x) return 11u;
    else return 22u;
}

unsigned in_loop(unsigned x)
{
    unsigned result = 100u;
    unsigned i;
    for (i = 0u; i < 2u; ++i) {
        if (x + 1u < x) result += 11u;
        else result += 22u;
    }
    return result;
}

unsigned label_barrier(unsigned x)
{
    if (x == 123u) goto injected;
    if (x + 1u < x) {
injected:
        return 11u;
    } else return 22u;
}

int main(void)
{
    unsigned i;
    for (i = 0u; i < 6u; ++i) {
        unsigned x = inputs[i];
        unsigned a = probe(x);
        unsigned b = in_loop(x);
        unsigned c = label_barrier(x);
        unsigned expected = x == 4294967295u ? 11u : 22u;
        printf("x=%u probe=%u loop=%u label=%u\n", x, a, b, c);
        if (a != expected || b != 100u + 2u * expected || c != expected) return 1;
    }
    /* Entering the labeled branch must bypass the region's guard. */
    if (label_barrier(123u) != 11u) return 2;
    printf("external-goto=11\n");
    return 0;
}
