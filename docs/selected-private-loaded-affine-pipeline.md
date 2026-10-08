# Actual loaded-root affine optimization under the selected CompCert host

2026-10-08. Narrative reference `12419c1` still matches main after fetching all
remote heads. This stage connects the existing two-dimensional private-loaded
source proof to real Pluto scheduling/tiling and prepared codegen. It tests the
narrative's separation of domain guarantees from language installation.

## What a source user provides

The user supplies C, region annotations and ordinary policy options:

```c
int i=start, j=77, k=91, rp, rq;
#pragma scop
rq=*q; rp=*p;
for (; i<*bound; ++i) {
  k=i+m;
  for (j=0; j<k; ++j)
    p[32+64*i+j]=q[4096+64*i+j]+a;
}
#pragma endscop
/* Public iterator observations and subsequent memory effects continue here. */
```

The retained pointer reads are part of this supported source family. They are
not invented unconditional reads of a later header. `m` is an existing scalar
parameter; this example does not support replacing it with a conditionally read
`*M`. A second example uses `2*i+1` as the child bound. The tested policy has row
cap 4, child cap 8, geometry cap 4 and extent 8192. These are configurable
profiles, not bounds of the generic framework.

The source user does not write a target Loop or provide a semantic callback.
The ordinary adapter sends the checked original nonrectangular Loop, context,
pointers and proposed validator ranges to the existing signed pipeline. Its
axis pairs record two source caps and configure rank; they do not replace the
source with a rectangle. Actual Pluto produces OpenScop transitions and PolCert
prepared codegen produces the candidate. The adapter translates the returned
mapped/tiling data into the existing private-loaded proposal type.

## Who proves what

| Responsibility | Reused proof or new connection |
| --- | --- |
| Kernel local composition | Existing kernel; no new semantic rule or proposition compiler |
| Domain `C_opt` | Existing affine-inner source/model correspondence and mapped/tiling candidate checker, applied to the actual returned Loop |
| Domain `C_derive` | Existing width/range, footprint separation and loaded-bound stability sufficient conditions |
| Language `C_guard` and state transport | Existing original-header snapshot insertion, actual check plan, private/public frames and candidate iterator restoration |
| Domain region guarantee | `check_affine_private_loaded_source_sound`, reused after frontend normalization |
| Language installation/backend | Existing selected certified-region compiler theorem; the new Csem-to-Asm endpoint is a one-line instantiation |
| Concrete site | Existing annotation, actual-source progress/scope checks and the generated fresh signed32 private pool |

`ClightLoadedAffineRegionBuilders.v` registers this factory after the existing
word and recursive-affine builders. Static `None` permits the next builder to
try the source. Runtime refusal remains inside the returned certified statement
and executes the original loaded-header source. These three source models are
not identified or combined by builder composition.

Three legacy objects had stale dependencies. They were rebuilt in an isolated
`GuardLoadedAffine` namespace, changing imports only. Existing successful source,
objects and reports remain untouched. The new two-module connection totals
63 lines including imports and audit queries. Its four audited endpoints use
at most the inherited 42 globals, with 1,810 bindings and no new axiom. These
counts do not measure author time or establish a burden-reduction claim.

## Execution evidence and limits

The new binary passes **810 unmodified assembly calls and 810 independently
executed emitted-Clight calls** across six configurations: real tiling, real
scheduling, unmarked input, disabled optimization, scheduler failure and
Fourier-Motzkin resource refusal. Each configuration compares all 19,200 array
cells, public controls, retained observations, the final loaded bound and
continuation effects with an independent word model and GCC reference.

Each normal mode installs two marked functions and excludes an unmarked
comparator. It records 16 candidate selections and 74 runtime refusals across
90 marked calls. The other 45 calls invoke the unmarked function. Both real
source models pass affine/tiling validation and codegen; final installation
also requires the original private-loaded factory's whole-candidate checks.
The generic Loop diagnostic is separate from this factory acceptance.

Changing `*bound` through a store and overlapping input/output accesses execute
the source fallback. Empty roots, nonzero starts, oversized profiles, first-empty
children and wrapping RHS word arithmetic remain in the matrix. The inherited
envelope condition requires equal pointer roots: disjoint offset footprints
under `p==q` accept, but distinct allocations conservatively refuse. This is an
acceptance limitation, not evidence that different allocations alias.

The same binary passes **400 assembly/400 Clight** word regressions and
**480 assembly/480 Clight** recursive-affine regressions. The latter retain real
rank-two/rank-three codegen, negative starts, two marked regions in one function
and public continuations. No new runtime cost or profitability study is added.

Two failed harness expectations are archived: an inherited installation-count
list and an incorrectly expected distinct-allocation acceptance. Native outputs
matched the reference in both attempts; the second also completed all 135
Clight full-output comparisons before its assertion failed. The initial legacy
object mismatch and duplicate-loadpath attempt are retained separately.

## Checkpoints and next acceptance

- Proof: `build/selected-loaded-affine/proof-v1/report.json`.
- Isolated legacy rebuild: `build/selected-loaded-affine/compat-v2/report.json`.
- Compiler: `build/selected-loaded-affine/compiler-v1/ccomp`.
- Loaded-affine execution: `build/selected-loaded-affine/native-v3/report.json`.
- Same-binary regressions: `build/selected-loaded-affine/regression-v1/report.json`.
- Retained attempts: `build/selected-loaded-affine/attempts-v1/report.json`.
- Manuscript successor: `build/paper/selected-loaded-affine-v1/report.json`.

On the prepared toolchain, reproduce in this order:

```sh
python3 scripts/prepare_loaded_affine_compat.py
python3 scripts/compile_selected_loaded_affine_sources.py --attempt isolated-namespace
python3 scripts/audit_selected_loaded_affine.py
python3 scripts/build_selected_loaded_affine_compiler.py
python3 scripts/native_selected_loaded_affine.py
python3 scripts/native_selected_loaded_affine_regression.py
```

Existing proof/compiler checkpoints are preserved rather than rebuilt in place.
Use a successor work directory for a new compiler or native matrix.

Next prove conditional child-header observation for actual `i<*N; K=i+*M`,
including empty-root skipping and stability when header locations can alias
writes. Keep header-read permission separate from later leaf/RHS permission.
Then address general recursive domains, first-empty-child acceptance, broader
alias sufficient conditions, scalar/chunk sources and the OLO source/cost
comparison. Connecting this narrower family does not complete that goal.
