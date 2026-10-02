# Untrusted point orders through the complete compiler

`ScheduledRegionCompiler.compile_scheduled_regions_correct` quantifies over
every proposed `list nat`. If compilation succeeds, the generated assembly
refines the complete source C program under CompCert's existing assumptions.
The proposal is ordinary optimizer input; the proof does not assume it is a
permutation, that a scheduling algorithm is correct, or that it provides a
proof term. A companion theorem preserves safety-enforcing specifications.

This instance shares the exact 2x2 source template, full AST checks, temporary
frame checks, and short-circuit dimension condition of the
[native loop interchange](native-matrix-interchange.md). It extends the
candidate side: every checked point order is lowered to an unrolled Clight
region. For example, the externally proposed order `[3, 1, 2, 0]` has this
equivalent C view, with left-to-right short-circuit checking:

```c
if (i == 0 && n == 2 && m == 2) {
  a[3] = 12;
  a[1] = 2;
  a[2] = 11;
  a[0] = 1;
  j = 2;
  i = 2;
} else { /* original loop */ }
```

The order checker must first accept the proposal. It refuses missing,
additional, or duplicated source operations and any crossing without the
language's independence evidence. Successful checking preserves multiplicity;
in this source, each point occurs once and names a different four-byte cell.
The language instance supplies actual `Mem.store` commutation, not a
statement about an abstract store model detached from CompCert memory.

`ClightIndexedStores.indexed_store_code_encode` translates a finite execution
to actual Clight assignments. It works for arbitrary immutable integer
payload maps on the four supported cells. `checked_matrix_schedule_bounds`
derives the pointer-range premise from acceptance, rather than trusting the
proposal. `matrix_scheduled_target_encode` restores both loop iterators and
preserves every other temporary. `ClightScheduledMatrix` combines source
decoding, checked memory reordering, candidate encoding, and the shared
condition compiler into a `region_contract`. The existing complete-program
host and CompCert passes then consume that contract.

The actual Clight lowering uses [shared fallback control](shared-fallback.md):
each refusal leaves a constant switch and reaches one copy of the original
loop. Acceptance runs the candidate and leaves a surrounding one-shot loop.
It introduces neither private temporaries nor labels. The normal-exit,
temporary, memory, and complete-program contracts remain the same.

The optional extracted compiler reads the proposal at compile time:

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make native-schedules
GUARDCERT_POINT_ORDER=3,1,2,0 build/compcert-scheduled/ccomp \
  -conf build/compcert-scheduled/compcert.ini \
  -stdlib build/compcert-scheduled/runtime -dclight -S \
  -o /tmp/scheduled.s examples/native_matrix_interchange.c
```

An unset environment variable proposes `[0,2,1,3]`. An empty value proposes an
empty list and is refused. The driver parses at most 64 natural identifiers,
each at most 1024, to bound construction of unary naturals; these parser
limits are outside the semantic theorem. The Rocq theorem covers every
well-typed natural list. Refused proposals allow the existing zero-trip or
redundant-assignment selectors to proceed; they never generate an unchecked
point schedule. A compiler refusing a proposal and a runtime guard refusing
the dimension premise are distinct cases.

`scripts/native_scheduled_matrix.py` compiles all 24 permutations and seven
invalid proposals. It checks the actual Clight store order in five source
contexts, exact iterator restoration, original-loop fallback, nine input
rectangles, global/local arrays, surrounding goto and loops, and an unread
uninitialized inner bound. Linked executions match GCC and independent
expected values. Four malformed or excessive parser inputs must fail.
Reports are `build/scheduled-matrix-proof-report.json` and
`build/native-scheduled-matrix/report.json`.

The generic checker handles arbitrary finite instruction lists; this native
source bridge handles one fixed four-point domain. It does not infer conditions
from an arbitrary rewrite, validate dynamic affine domains or tiling, analyze
dependencies of an arbitrary body, call PolOpt, or establish a speedup. The
contribution of this instance is an exercised interface for untrusted
scheduling input, verified code generation, safe runtime versioning, and
complete-program composition.
