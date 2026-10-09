# Header-only empty affine rewrites in the selected compiler

Date: 2026-10-08. This successor exercises the proof-responsibility and premise
provenance clarified in `topdown/research-positioning@c4b1395`. It adds an
ordinary conditional rewrite to the existing selected CompCert compiler. The
kernel, installation host and polyhedral validators are unchanged.

The [signed-header successor](affine-empty-signed-installation.md) now adds
bounded negative-parameter acceptance through a condition-certificate client.
The generic encoder already supports signed intervals; the nonnegative limit
below describes this historical client profile.

The [shared-fallback successor](affine-empty-plan-installation.md) now removes
the repeated original loops while preserving every tested acceptance/refusal
path. This document retains the expanded compiler checkpoint and its evidence.

The source family has an original loaded root and an affine loaded child:

```c
int i = start, j = 77, K = 91;
#pragma scop
for (; i < *N; ++i) {
    K = i - *M;                /* also 2*i-M, i+M and 2*i+M */
    for (j = 0; j < K; ++j)
        p[32 + 64*i + j] = q[4096 + 64*i + j] + a;
}
#pragma endscop
/* i, j, K and memory remain observable here */
```

For `start=0, N=3, M=4`, the child bounds are `-4,-3,-2`. The source performs
no body access and exits with `i=3, j=0, K=-2`. Reusing the old nonnegative-child
restore would set `j=-2`, which is incorrect. The new restore explicitly sets
it to zero. If `N<=0`, the source leaves `j` and `K` unchanged and never reads
M; that path has a separate skip certificate.

## Conditions and effects

The positive-root condition uses only the header context. It checks the
existing entry/parameter profile and a safely encoded affine endpoint test:

```text
N > 0
Int.min_signed <= width(0)   <= 0
Int.min_signed <= width(N-1) <= 0
```

The affine extrema theorem derives the same signed range and nonpositivity at
every reached row. The language execution theorem constructs actual original
Clight execution with no leaf evaluation. Body-only words, body pointers,
allocation permissions and non-alias are absent from these prerequisites.

| Clause | Concrete contract |
| --- | --- |
| Inputs | Checked original AST/profile, fresh typed root/child caches, header-only decision tree |
| Invocation producer | Existing conditional capture plus the original source execution produce the loaded-word receipts; the first reached setup produces header words |
| Outer acceptance | Row is zero and cached signed N is nonpositive; skip preserves all original public temporaries and memory |
| Positive-root acceptance | Header profile and encoded endpoint test imply every reached child is empty; restore produces the exact public exit |
| Refusal | Run the original repeated-load AST; refusal does not imply that some child is nonempty |
| Effects | Original-licensed root/conditional-child loads, private cache writes, readonly condition evaluation, then public loop-exit assignments; no leaf access on acceptance |
| Memory/events | Accepted source and rewrite have exactly the original memory and empty trace; captures/checks do not change memory |
| Context | A projected region contract preserves all live temporaries; the existing selected host/backend compose it to Csem-to-Asm backward simulation |

The original finite execution is a proof premise, not a runtime pre-execution.
The source user supplies marked C and ordinary configuration. The checked
factory produces the semantic and placement/resource evidence; it accepts no
source-user completion or equivalence callback.

## Concrete proof chain and ownership

| Responsibility | Endpoint |
| --- | --- |
| Domain: endpoint implication | `affine_empty_width_math_sound` |
| Language/domain: safe Boolean encoding | `compile_affine_empty_width_exact`, `compile_affine_empty_width_sound` |
| Language: actual zero-leaf execution | `affine_empty_loop_execution`, `affine_empty_restore_execution` |
| Domain/site producer: original loaded headers and exact exits | `affine_empty_snapshot_child_value`, `affine_empty_snapshot_source_complete`, `affine_empty_snapshot_source_exit` |
| Language: empty outer and conditional choice | `affine_outer_empty_source_exit`, `affine_empty_snapshot_guarded_execution` |
| Site producer: capture, scope and original fallback | `affine_empty_snapshot_captured_execution`, `affine_empty_snapshot_prefix_contract`, `check_affine_empty_snapshot_source_sound` |
| Language: whole-program installation/backend | `compile_selected_empty_snapshot_regions_correct` |
| Framework | Existing local certificate/guarded-choice composition; no new kernel interface or axiom |

This rewrite does not reorder an active leaf and needs no `C_opt` polyhedral
candidate certificate. Its local replacement proof is the actual empty-source
execution and public-exit correspondence. The same compiler continues to use
the original Pluto/PolCert candidate route for the existing optimization
families; their candidate and dependence certificates remain independent.

The registry first tries all existing certified builders. The empty builder
runs only after their **static** refusal. Thus the new normal configuration
preserves previously installed candidates. It does not yet add a runtime empty
choice inside a previously returned guarded candidate: a later runtime
refusal of that candidate still uses its original fallback. Static registry
choice and runtime guard choice are different composition tasks.

## Checked evidence and remaining limits

Ten new frozen modules contain 1,000 lines. The reachable audit binds 29
endpoints, five closed, 2,076 files and at most the 42 inherited globals, with
no additional axiom. All 53 source-build attempts are retained: ten successful
and 43 rejected attempts. Successful sources/objects are not edited.

The extracted compiler runs two source matrices (`i+M`/`2*i+M` and
`i-M`/`2*i-M`) in six configurations: tile, schedule, unannotated, disabled,
scheduler failure and oracle-resource refusal. All 2,280 Asm and 2,280
independent Clight diagnostic calls match the word model, every one of 12,000
array cells per call, public iterators and a continuation. Each normal matrix
has three installed marked functions and one unmarked function. Two matrices
include a marked function with an uninitialized body-only local; all its tested
source executions avoid that read.

| Normal configuration, per 190-input matrix | `i+M` / `2*i+M` | `i-M` / `2*i-M` |
| --- | ---: | ---: |
| Actual fast / fallback / unmarked | 33 / 107 / 50 | 87 / 53 / 50 |
| Fast calls with NULL body pointers | 9 | 27 |
| Fast calls with an undefined body-only word | 11 | 32 |
| Fast calls with header/data overlap | 9 | 27 |
| Fast calls with unavailable M on an empty outer | 6 | 6 |

Scheduler and oracle refusal do not prevent this independent rewrite. The
disabled native policy refuses the profile, and unannotated regions remain
unselected. Native phase attempts are not evidence of a polyhedral candidate
installed on an empty path.

The same compiler passes five existing families: word 400/400,
recursive-affine 480/480, private-loaded 270/270, zero-width 672/672 and
RMW 816/816 Asm/Clight calls. Each normal RMW configuration retains its
126 fast and 146 fallback selections. These checks preserve the established
candidate path; they do not identify the families' source semantic domains.

Three failed harness runs are retained and bound by the successful report:
one requested a nonexistent scheduler helper, one assumed a single ordinary
`for` fallback where the printer emitted duplicated strict loops, and one
replaced identical unannotated bodies ambiguously. The compiler's full-output
checks passed before the latter two diagnostic-construction failures; these
are not compiler-miscompilation witnesses.

The current parameter guard has a **nonnegative** parameter profile. Hence
negative child widths are accepted for `i-M` with nonnegative M, while
negative M in positive-root `i+M` safely falls back. General signed parameter encoding
remains required. The new readonly tree is materialized: the measured marked
triangle has 32 original fallback occurrences in its Clight AST. Existing
private-Boolean/check-plan lowering should remove that duplication in a
successor. This stage claims neither compact code nor profitability.

The full goal remains active: signed header parameters, compact lowering,
runtime composition with existing candidates, general recursive loaded affine
domains, broader scalar/chunk services, complete-call cost and the combined
OLO/BT case still require work.

## Reproduction and immutable checkpoints

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_affine_empty.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_affine_empty.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_affine_empty_regression.py
```

The extraction recipe is `scripts/build_affine_empty_compiler.py`; it refuses
to overwrite an existing compiler checkpoint. The proof report is
`build/affine-empty/proof-v1/report.json`
(`ecee9787f1ff5acafd2ee7f45fc29f220256356ae4c5d8acfa613391c88f5c41`).
The compiler is `build/affine-empty/compiler-v1/ccomp`
(`87817ea32bb5f3223a1595a56043ebffc1a48b24ea1fa5702798985c7f1a884a`).
The native report is `build/affine-empty/native-v4/report.json`
(`42c9cba7c12787cc987c0e8367e9fa6427fee4d38af21199021f9328d1900c6d`).
The same-binary regression report is
`build/affine-empty/regression-v1/report.json`
(`690be97a820705dd72c5e68c71af71e0a0e09f29fcec5ba242dd8b2f03a3d648`).
