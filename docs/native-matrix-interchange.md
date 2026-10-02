# Native guarded matrix loop interchange

This instance connects an actual Clight loop schedule change to
`AdaptiveRegionCompiler.compile_progress_regions_correct`, whose source and
target are the complete CompCert C and assembly semantics. It uses CompCert
memory directly. It does not import CInstr or invoke PolOpt.

The first accepted template is deliberately small:

```c
for (; i < n; ++i) {
  for (j = 0; j < m; ++j) {
    a[i * 2 + j] = i * 10 + j + 1;
  }
}
```

The array has exactly four ordinary signed 32-bit elements. The generated
condition checks `i == 0`, then `n == 2`, then `m == 2`. Its accepting branch is:

```c
j = 0;
for (; j < m; ++j) {
  i = 0;
  for (; i < n; ++i) {
    a[i * 2 + j] = i * 10 + j + 1;
  }
}
```

Every refusal executes the original region. Candidate recognition checks the
complete outer loop AST, both flattened body lists, the complete array
assignment AST, and five identifier inequalities. Flattening removes only
empty statements and sequence associations, with a proof about actual source
executions. Changing the assignment value or introducing a memory-dependent
right-hand side fails this instance's certificate check.

The important entry requirement is conditional. The original outer loop reads
`i` and `n`; when they equal 0 and 2, its successful execution must enter the
body and read `m`. The guard therefore reads `m` only after both outer checks
accept. An outer zero-trip execution need not initialize `m`. This entry
property is proved from the source execution in
`ClightMatrixRegion.matrix_source_guard_domain`; it is not an assumption about
all function parameters.

The proof separates three reusable interfaces. `ClightLoopExecution` decodes
and reconstructs actual frontend loop executions from normal-exit and
temporary-frame properties. `CompCertStoreSchedule` instantiates
`AbstractSchedule` with actual `Mem.store`, byte-disjoint independence, and
equality of complete CompCert memories. `ClightMatrixGuard` supplies a
positive property dimension and a certified short-circuit check to the shared
condition compiler.

For this template, source execution yields the store order `[0, 1, 2, 3]` and
candidate execution uses `[0, 2, 1, 3]`. A single certified swap of the middle
two byte-disjoint stores constructs the new execution with the same complete
final memory. The compiler now uses the [executable schedule checker](schedule-checker.md)
to certify that order, rather than supplying a hand-built swap proof. Both loop
iterators end at 2. Every other temporary has the same
value, including the loop bounds. The surrounding program resumes from the
same exit state. Source stores supply the memory permissions, and the
commutation proof transports them to the new order.

`ClightMatrixSelector.select_matrix_interchange_sound` packages these facts as
a `region_contract`. The compiler checks this selector before its zero-trip
and redundant-assignment selectors. The existing whole-program host handles
source progress, arbitrary surrounding continuations, calls and observable
events outside the region, and the remaining CompCert compilation passes.
The whole-program theorem has exactly the original CompCert theorem's global
assumptions. The direct store commutation proof uses CompCert's inherited
proof-irrelevance assumption when equating memory records.

Native validation is provided by:

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make check-integration
```

`scripts/native_matrix_interchange.py` checks the extracted compiler's Clight
dump for the generated condition and both loop orders, compares the linked
program with GCC, and checks independent expected memory values and iterator
exits. The fixtures include local/global arrays, surrounding `goto` and loop
contexts, acceptance and fallback, an unread uninitialized inner bound, and
refusal of unsupported values, dependencies, and volatile stores. Its report
is `build/native-matrix-interchange/report.json`.

This is an execution and integration prototype. It does not validate general
affine schedules, arbitrary dimensions, tiling, reductions, parallel code,
array-pointer aliasing, or optimizer-generated candidates. It also makes no
performance claim: a guarded 2x2 interchange can cost more than the source.
The current conditional-tree lowering repeats the fallback region on separate
refusal edges; control-flow sharing and guard-cost selection remain work to do.
The next generalization should retain the same property/check/host interfaces
while replacing the fixed template and four-store certificate with an affine
domain and order certificate.
