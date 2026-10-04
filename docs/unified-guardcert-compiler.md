The unified compiler applies guarded loop transformations and conditional scalar rewrites in the same complete C program. Its entry point is `AffineNestUnifiedCompiler.compile_guardcert`; `compile_guardcert_correct` proves a backward simulation from CompCert C semantics to assembly semantics.

The intended reader is a compiler researcher using the existing GuardCert services. The pipeline normalizes C to Clight, checks each proposed loop region, installs the accepted regions, applies scalar rewrites, and runs the CompCert backend. The single-pointer and multiple-pointer deep affine services receive the first opportunities to transform a source region. When they return no candidate, the existing rectangular memory service checks the region. Each service proves the same projected region contract, including memory, public temporaries, and the source fallback.

The deep affine service accepts checked source syntax, parameter intervals, private names, and candidate syntax with reindexing or tiling evidence. The rectangular service accepts independently checked mapped, scheduled, and tiled candidates. Both producers remain untrusted. The scalar stage currently includes the unsigned wrap-condition rule, signed multiplication/division cancellation under a checked word-range condition, and the existing memory expression rules.

For example, the signed rule transforms `(x*2)/2` into a guarded choice. It evaluates `2*x` in a wider integer type, returns `x` when the signed 32-bit range check succeeds, and otherwise executes the original expression. The unsigned rule simplifies `if (x+1U<x)` when a runtime bound excludes wraparound. The compiler retains the original branch when that bound fails.

Build and run with the repository Rocq toolchain:

```sh
make affine-nest-prototype-proof
make guardcert-compiler
make native-guardcert
```

The resulting executable is `build/compcert-guardcert/ccomp`. It uses the normal CompCert driver options. `GUARDCERT_AFFINE_MODE` selects the deep affine candidate policy; `GUARDCERT_AFFINE_PROFILE=inferred` derives checked bounds and address windows from the source. `GUARDCERT_LOOP_CANDIDATE` names the candidate file for the rectangular memory service. These settings propose data; they cannot bypass either checker.

The proof audit compiles 96 prototype modules. In the same Rocq environment, the unified whole-program theorem has exactly the original whole-program theorem's 42 global assumptions. The audit reports no new global axioms. The extraction stamp records the entry point, executable digest, 707 proof-source digests, and eight native-source digests.

`native_guardcert.py` constructs one C program containing the five deep affine kernels, six signed multi-pointer rectangular kernels, and both scalar examples. Six candidate configurations each execute 988 calls, giving 5,928 actual assembly calls. Every run compares all array cells and public loop controls with independent word-level models and a GCC reference. The configurations cover disabled loop candidates, identity, interchange, tiling, an incorrect deep tiling witness, and an oracle resource limit.

`native_guardcert_paths.py` separately instruments the actual generated Clight. It observes the emitted guards, pointer comparisons, parameter tests, and selected branches. These observations establish test-path coverage; the unmodified assembly runs and Rocq theorems provide separate evidence. Shared storage with disjoint accessed cells can use the rectangular fast path; overlapping accessed cells use the source fallback.

The deep affine service handles multiple stable pointers by scanning the actual source domain with private control variables. It compares every cross-pointer pair of actual source accesses. Source execution supplies the permissions needed to prove these comparisons safe. Acceptance establishes non-aliasing on the actual source footprint, which is enough for the candidate validator. The scanner preserves memory and public temporaries; rejection executes the original source.

The [external candidate interface](external-affine-candidates.md) exports checked source requests and imports concrete Loop IR candidates. The same source-domain guard and candidate checker consume their results. Request matching, parsing and candidate generation remain untrusted.

The source and candidate must satisfy the checked syntax and range interfaces. Scanning has quadratic cost in source points and access sites. The deep service also restores public control values by replaying pure source control after the transformed memory computation. That replay has a cost proportional to source control iterations, so these results establish behavior preservation without claiming a speedup.
