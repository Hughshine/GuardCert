# Nonrectangular C source regions

The CompCert-memory adapter recognizes a counted outer loop whose inner upper
bound is `i + M`. The actual source is a nonrectangular affine region:

```c
for (; i < N; ++i) {
  K = i + M;
  for (j = 0; j < K; ++j) {
    a[i * stride + j] = i * coefficient + j + bias;
    b[i * stride + j] = a[i * stride + j];
  }
}
```

The original C fragment is checked against the complete normalized Clight AST.
Recognition proposals do not carry a correctness assumption. The shared host
injects the runtime decision and keeps the source as its fallback.

The accepted source operations are the named-array operations: affine writes,
updates from the same cell, row-prefix updates, cross-array affine updates and
direct integer copies. Arrays can be local or global objects. The current
source recognizer still requires one common extent and stride. It does not
recognize arbitrary affine C loop bounds, pointer slices or different strides.

## Runtime presumption and encoding

The presumption is `i == 0`, `0 < N <= extent / stride`, `0 < M <= stride`,
`N + M - 1 <= stride`, and distinct actual blocks for different registered
array objects. The width condition bounds every successful iteration to the
selected array row; this also keeps source loop bounds and indices in range.

The emitted width test is `N <= stride - M + 1`. It is lowered by the existing
verified signed affine expression compiler, after the positive range checks.
Its intermediate intervals are `-M` in `[-stride,-1]`, `stride-M` in
`[0,stride-1]` and the final right-hand side in `[1,stride]`. An encoding failure
rejects the transformation. Neither the test nor the source-to-IR theorem
requires evaluating `N+M` as an unchecked machine expression.

Actual array-pointer inequality tests follow the range and width tests. Their
definedness comes from the source execution's first successful point and the
preservation of memory permissions by stores. A base inequality for objects
is not a proof of non-overlap for arbitrary pointer slices.

## Execution and whole-program connection

`GuardMemoryVariableCounterExit.v` generalizes counted-loop decoding to a
settlement that depends on the current outer iteration.
`GuardMemoryRaggedClight.v` proves that the real source executes `i+M` inner
iterations for each `i`; `GuardMemoryNamedRaggedSource.v` connects these
iterations to the actual-memory Loop IR with the original arrays registered.

The source and proposed Loop programs are extracted independently. Both are
restricted by the runtime presumption. The mapped domain checker proves exact
integer domain equivalence and validates actual read/write dependencies.
Accepted coordinate maps have proved point correspondences. An unsafe
statement order, a missing point, an extra point or an incorrect map rejects
its proposal.

The candidate backend executes the validated IR with the same physical array
registry. It restores `i=N`, `K=N-1+M` and `j=K`. This restoration is proved
against the source execution and surrounding temporary-variable frame; the
bounds are computed as `(N-1)+M`.

`check_memory_ragged_mapped_region_sound` provides the projected fragment
contract. `GuardMemoryUnifiedCompiler.compile_memory_unified_regions_correct`
composes the shared region replacement with CompCert's front and back ends,
producing a backward simulation from the actual Csem program to assembly.
The source fallback and containing functions remain covered by that theorem.

## Reproduction

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make native-memory-ragged
```

`examples/native_memory_ragged.c` includes local and global arrays, an enclosing
loop, all named source operation forms, direct copies of extreme integers,
public `i/j/K` uses and calls whose width presumption fails. The test script
compares complete output with both GCC and an independent execution model. It
also checks the generated Clight to distinguish accepted transformations from
successful fallback executions.

The fresh audit compiles 81 memory modules and the seven lowering modules. It
retains the existing 7 instruction assumptions, 12 validator assumptions and
42 assumptions for the CompCert/validator union. The 12 nonrectangular native
configurations each match all 1,385 output lines. Identity, interchange,
fission, shift and skew are accepted on all seven source functions. Incorrect
domains, incorrect skew maps, missing statements, reversed dependent writes,
resource exhaustion and invalid oracle certificates fall back. The original
16 multiarray configurations each still match all 4,022 output lines.

This source extension is a bounded affine family. The generic Loop extractor
handles a wider affine grammar than this C recognizer. General source
recognition and tiling of nonrectangular regions remain separate obligations;
no successful affine proposal should be reported as evidence that those
obligations have been discharged.
