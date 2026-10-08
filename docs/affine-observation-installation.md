# Alternative header-observation conditions in the actual compiler

Date: 2026-10-08. This successor tests the guard-library and proof-provenance
clarifications in `topdown/research-positioning@c4b1395` against an actual
loaded-affine client. It reuses the minimal kernel, Clight installation host,
polyhedral validators, candidate lowering and public-exit restoration.

The supported source family includes marked regions of this form:

```c
#pragma scop
rq = *q; rp = *p;
for (; i < *N; ++i) {
    K = i + *M;              /* also supports 2*i + *M */
    for (j = 0; j < K; ++j)
        p[32 + 64*i + j] = p[32 + 64*i + j] + alpha;
}
#pragma endscop
/* public iterators, loaded words and memory remain available here */
```

If a write overlaps N or M, separation cannot justify caching that header.
For this checked RMW body, `alpha == 0` independently establishes preservation
of its defined Mint32 word observations. Other inputs still use the original
separation scan. Both conditions establish the same actual-row obligation;
data dependencies and candidate ranges remain separate checks.

## Shared guarantee and its scope

`affine_snapshot_row_observation_preservation` in
`ClightAffineSnapshotRowObservation.v` quantifies reached original row
executions. Its prerequisites include a bounded row coordinate, stable
temporary agreement, and current memory matching the entry's recorded header
observations. Its conclusion says those observations still match after the
actual row body. It does not require all memories or raw loads to be equal.

The previous separation result quantified arbitrary point memories and raw
`location_load` equality. The existing RMW capability instead preserves already
defined Mint32/Vint loads. They were not interchangeable theorem fields.
`affine_snapshot_separated_row_preservation` and
`affine_snapshot_zero_rmw_row_preservation` now derive the concrete obligation
used by the whole-loop transport from their respective capabilities. This is
a domain/language adaptation above the kernel.

The RMW source checker chooses a scalar from the checked region context and
checks the entire original row body with `check_zero_rmw_control`. It does not
accept a proposer-supplied semantic predicate. The capability allows structured
control and temporary assignments that do not change this scalar; actual word
stores must have the checked redundant-RMW shape. It preserves defined Mint32
words, not arbitrary bytes, other chunks, pointer fragments, or complete memory.

## Invocation, execution and refusal

| Clause | This client |
| --- | --- |
| Inputs | Checked original source package, automatically selected RMW scalar, two private header caches, existing preparation descriptors, scan plan and actual candidate proposal |
| Requires | Original-source/capture domain and the fresh typed resources checked by the factory; the scalar test additionally requires accepted numeric preparation |
| Order | Original conditional capture; header/range and first-or-second reached-body preparation; scalar-zero test; zero path or old separation scan; data alias and candidate ranges; dispatch |
| Scalar-read license | Accepted preparation provides a full typed view including the context scalar. The scalar test is not moved before this gate |
| Accepted | Ready geometry, row observation preservation, data non-alias and actual candidate ranges |
| Refused | Original repeated-load source executes. A refused sufficient condition does not establish its logical negation |
| Effects | Decision checks are readonly; capture, scan cursors and shared result use checked private temporaries. Memory and public temporaries are framed at the guard exit |
| Producer | Static source/resource checkers produce syntax and freshness; runtime checks plus source-licensed receipts/transport produce dynamic facts |
| Semantic starting point | A given original execution is consumed by the finite-region correctness proof; runtime code does not execute the source before checking |

This implementation uses the existing readonly branching combinator for the
two sufficient conditions. Its compact plan uses an `alpha == 0` test around
the old scan plan, so extracted compilation need not expand the complete scan
tree. It does not add a combinator for arbitrary alternatives that change
private state before refusal, nor a callable runtime C library.

## Concrete proof chain and responsibility

| Bridge | Endpoint | Responsibility and direction |
| --- | --- | --- |
| Separation or zero-RMW to row guarantee | `affine_snapshot_separated_row_preservation`, `affine_snapshot_zero_rmw_row_preservation` | Domain obligation, using concrete row decoding and language memory/control laws |
| Actual guard acceptance to geometry/row/data/range facts | `affine_rmw_snapshot_candidate_condition` | Language safe readonly execution plus domain sufficient-condition producers |
| Given original loaded execution to cached execution | `affine_row_snapshot_checked_cached_execution` | Language transport consumes the row invariant; exact final memory and temporary exits are preserved |
| Cached Clight to source Loop | `memory_zero_width_pointer_region_source_under_ranges` | Existing one-way domain execution decoder; not parsing or a standalone bidirectional equivalence |
| Source Loop to actual candidate Loop | Existing zero-width mapped/tiling checker soundness | Existing C_opt, rechecking the returned actual candidate under the wider assumed source model |
| Candidate Loop to lowered Clight/public exits | `affine_zero_pointer_candidate_execution` | Existing concrete backend and restoration proof |
| Actual guarded region and retained prefix/suffix | `check_affine_rmw_snapshot_planned_source_sound` | Checked factory discharges source, resources, candidate and finite-region obligations |
| Whole C program to assembly | `compile_selected_rmw_snapshot_planned_regions_correct` | Existing selected-region language host and CompCert backend, yielding backward simulation |

The fixed registry tries the checked RMW builder before the zero-width and
older builders. Static RMW ineligibility allows the older route to run. The
ordinary native proposer, actual Pluto scheduling/tiling and PolCert prepared
code generation are reused. The source user supplies marked C and strategy
options, not completion proofs, modeling callbacks or a handwritten target.

## Running the supported path

On this restored workspace, compile a supported marked input with the bound
binary as follows; `schedule` selects scheduling instead of tiling:

```sh
GUARDCERT_TENSOR_MODE=pipeline GUARDCERT_POLYHEDRAL_MODE=tile \
GUARDCERT_AFFINE_ROW_CAP=4 GUARDCERT_AFFINE_COLUMN_CAP=8 \
GUARDCERT_AFFINE_GEOMETRY_CAP=4 GUARDCERT_AFFINE_EXTENT=8192 \
GUARDCERT_PLUTO="$PWD/build/polyhedral-pipeline/pluto-source/tool/pluto" \
build/affine-observation/compiler-v1/ccomp -fall \
  -stdlib build/affine-observation/compiler-v1/runtime -S input.c -o input.s
```

The proof/native helpers below validate existing checkpoints when their report
is present. They retain successful sources/objects and refuse to overwrite a
new compiler or experiment directory. A clean workspace first needs the parent
proof/dependency setup recorded by the earlier installation stages.

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_affine_observation.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_affine_observation.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_affine_observation_regression.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_affine_observation_comparison.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_affine_observation_cost.py
```

## Evidence and remaining work

Eleven new modules total 1,115 source lines and compile and audit 29 endpoints: two closed, at most the
existing 42 globals, and no additional global axioms. The 1,992 bindings cover
the reachable source/object closure and preserved compile attempts. The proof
checkpoint is `build/affine-observation/proof-v1/report.json`, SHA-256
`299c4146d50b7e44ac2b648376e425b33b90dc093e02814ca10ad76d58c1b3d0`.
All 23 compile attempts are preserved: eleven successful and twelve rejected.
The extracted selected compiler builds successfully; its SHA-256 is
`aa02cd8ffbc4d28e1285742e3863f44b56746f386fc7280c979b4d4366a5714b`.

Six configurations (tile, schedule, unannotated, disabled, scheduler failure
and checker-resource refusal) each compare 408 complete calls against an
independent word model and GCC reference, and separately execute emitted Clight.
Total: 2,448 Asm / 2,448 Clight calls. All 19,200 array cells, header values,
public iterators/temporaries and the continuation match. Each normal mode
installs the two marked functions and observes 126 candidate selections, 146
runtime fallbacks and 136 unmarked calls. Nonzero-alpha writes overlapping N/M
refuse; empty outer loops skip an unavailable M; all-empty body preparation
still refuses before its body-only scalar test.

On exactly the same RMW C sources and 408 inputs, the old frozen compiler
observes 122 candidate selections per normal mode, versus 126 for the new
compiler, with no lost acceptance. The four gains are the two marked functions
with N or M at the first actual write and alpha zero. Acceptance numbers from
the earlier copy-source suite are not used as this comparison's baseline.

The same successor binary passes word 400/400, recursive-affine 480/480,
private-loaded 270/270 and zero-width 672/672 Asm/Clight regressions. Recursive
cases include actual rank-three code generation and multiple marked regions.

| Bound checkpoint | SHA-256 |
| --- | --- |
| `build/affine-observation/native-v1/report.json` | `50a79fd6913dee283b82ab1b345b60f15e0ebd35e94490de03af3772abb9bb0e` |
| `build/affine-observation/regression-v1/report.json` | `d1069f12134c29ae5e4499b81b9fcd1ce118e5902eef0ea162b8c802e7cfb648` |
| `build/affine-observation/comparison-v1/report.json` | `381331cdd0acac74140f06b68a5ab74346a93ee8f56bee65a8a1aa9ec194ba8b` |
| `build/affine-observation/cost-v2/report.json` | `723815112d0efdd6d6f5493b02cf5425b98f0c556b4b59515285c6d8fa22d77f` |

## Complete-call cost

The cost harness measures the unchanged triangle kernel instructions from the
bound native assembly. It renames only the old `main` symbol before linking a
common driver; object `.text` equality is checked. The driver resets N/M before
each call and observes the continuation afterward. Storage initialization and
printing are outside the timer. Source baselines use the same successor compiler
with transformation disabled; previous guards use the frozen old compiler on
the same RMW source. Timing uses process CPU time with seven randomized process
batches per variant, input and mode. Row/column caps are 4/8, extent 8192.

All 336 batches of 65,536 calls compare the complete final memory and public
outputs against an independent repeated-execution word model. The table reports
ratios of median complete-call times; these include check and selected candidate
or fallback, rather than isolated guard cost.

| Input | New/old tile | New/source tile | New/old schedule | New/source schedule |
| --- | ---: | ---: | ---: | ---: |
| Separated, alpha zero | 0.845 | 3.063 | 0.917 | 2.077 |
| N overlap, alpha zero | 2.346 | 3.441 | 1.288 | 1.891 |
| M overlap, alpha zero | 1.841 | 3.155 | 1.174 | 1.969 |
| N overlap, alpha one, fallback | 1.021 | 1.516 | 0.934 | 1.400 |
| Separated, alpha one | 1.013 | 3.761 | 0.991 | 2.444 |
| Body empty, fallback | 1.064 | 1.293 | 0.961 | 1.723 |
| Cap refusal | 0.981 | 1.036 | 0.903 | 1.004 |
| First child empty, later active | 0.876 | 3.686 | 0.842 | 1.845 |

Skipping stability scans reduces the separated-zero median by 15.48%/8.26%
in tile/schedule mode relative to the old guarded path. Newly accepted overlap
inputs cost more than their previous fallback. All sixteen new medians exceed
the source baseline; these tiny kernels establish no profitability result or
representative-workload conclusion. Generated code size, scan work, complete
time and acceptance remain distinct measurements.

The first cost harness completed all 336 output comparisons, then failed while
building its table: a cap-refusal input was absent from the native path matrix.
Its source and all outputs remain in `cost-v1`. The corrected `cost-v2` uses the
already path-observed cap-refusal input and binds the failed run too.

The source family remains rank two with nonnegative bounded child widths and
first-or-second reached-body licensing. All-empty body input bypass, clipped
negative-width exits, general recursive loaded affine sources, broader scalar
and chunk capabilities, compact condition derivation and the complete OLO
comparison remain work for the active goal. This stage measures one service's
complete cost; broader compact-condition and benchmark work remain active. It
does not establish profitability or cross-language contract reuse.
