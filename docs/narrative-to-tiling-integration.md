# Narrative Clarification and the Actual Generated Candidate

This note is for an optimizer implementer using GuardCert's CompCert instance.
It records how the current integration follows
[`paper-narrative.md`](topdown/paper-narrative.md), rather than changing the
language-independent kernel to accommodate a particular loop transformation.
On 2026-10-07, the remote narrative reference was
`12419c1e1e3da450bf378742a2fb4e204e51e060`; its narrative text already matched
main. The implementation target remains the complete sequential guarded
polyhedral compiler, with OLO as a functional and usability reference.

## Responsibility Boundaries

| Owner | Evidence supplied or service proved | Current realization |
| --- | --- | --- |
| Generic kernel | Compose a guard certificate and a conditional preservation certificate into local guarded correctness. | Existing `GuardInterface` and materialized preservation services. |
| Language host | Real check/control semantics, private resources, public frames, legal installation, progress, and connection to the backend. | Existing Clight expression/selected-region hosts and CompCert compilation theorems. |
| Domain instance | Source/model correspondence, sufficient assumptions, safe condition encoding, validated transformation, and actual candidate execution. | Tensor source and guard libraries, instantiated affine/tiling validators, prepared codegen, and the generated-candidate bridge. |
| Untrusted producer | Select a region, propose a schedule, tile sizes, and witness data. | Explicit region markers, Pluto phases, and native data producers. |

The last row provides no semantic evidence by itself. The language and domain
instances check the proposed data. The generic kernel does not inspect C syntax,
OpenScop matrices, tile sizes, or addresses.

## The Candidate Interface Gap

The older `TensorRegionTiled rows columns` interface builds a fixed target Loop
from two tile sizes. It is useful as a regression fixture, but it cannot establish
that the compiler installs the Loop returned by real prepared codegen.

`ClightTensorGeneratedCandidates.v` instead accepts either an actual Loop plus
affine reindex data, or an actual Loop plus point-space tiling witnesses. The
proposer supplies no execution proof or semantic callback. The factory compiles
that Loop and checks its correspondence with the conditionally valid source.
Changing witness data cannot bypass the checker.

Two proof directions are required. The prepared pipeline's backward theorem
relates a completed generated execution to the source model. Separately, the
forward source/candidate checker establishes that a completed source execution
has an execution of this actual candidate. The latter supports Clight progress
and installation; the backward theorem alone is insufficient.

An actual C probe exposed a representation gap. Prepared codegen emits
`min/max/floordiv` loop bounds, while `ExtractorFrontend` accepts pure affine
loop bounds and guards. The raw generated Loop therefore failed extraction,
even after successful phase validation. The producer now proposes an automatic
bound adaptation: keep the generated loop skeleton and instruction arguments,
use affine enclosing bounds, and encode original membership as affine guards.
For example, with positive `d`, `q < floor(e/d)` is encoded as
`d*(q+1) <= e`. Unsupported bound forms refuse.

This adaptation is untrusted. The final checker verifies the adapted candidate
against the assumed source, including its complete point domain and effects;
it does not trust the proposed enclosing bounds or membership identities.
The pipeline saves both `raw-generated.loop` and `generated.loop`. No separate
raw-to-adapted equivalence theorem is claimed. The prepared-codegen backward
theorems concern the raw output, while the installed candidate's certificate
comes from checking the adapted output. This boundary should remain explicit
when describing the connected proof chain.

The new bridge reuses `tensor_checked_candidate_execution` and the existing
public-counter restoration theorem. Its literal-bound adapter reuses the
existing guard encoding certificate, private-state transport and materialized
host. The selected compiler then uses the existing region-table installation
theorem and verified CompCert backend. The minimal kernel remains unchanged.

## Acceptance and Remaining Work

The tiling path is selected C region, source Loop extraction, OpenScop,
actual scheduling and tiling phases, checked affine import, checked tiling
transition, prepared codegen, proposed bound adaptation, checking and lowering of the actual
candidate, original-source fallback, selected Clight host, and assembly.

Direct compilation of the new definitions and the whole-program endpoint is a
proof check, not native acceptance evidence. Native acceptance must separately
bind phase outputs, witness data, generated Loop, installed Clight dispatch,
public exits, and full-program observations. A phase receipt alone does not
establish that the factory accepted or installed its candidate.

The independent proof audit queries 13 endpoints over 442 dependencies. The
whole-program endpoint keeps the existing 42-global baseline, with no additional
global axiom. Its report is
`build/polyhedral-tiling/proof/report.json`, SHA-256
`17408069e310f282eff66c1ab06eb1dffcc770d249f473fecfa99f585af9f8a2`.
The complete native matrix passed nine configurations: 648 unmodified assembly
calls and 288 separate generated-Clight dispatch observations. It covers row
and column layouts, tile sizes `(2,3,2)`, `(4,2,3)` and `(64,64,64)`, repeated
marked regions, excluded unmarked regions, runtime guard refusal, unsupported
source bodies, disabled optimization, scheduler failure, truncated output and
invalid scattering. Every call compares all 6,144 array words, public counters
and context effects against an independent machine-word source model and GCC
source execution. The Clight observations also check each installed branch.
They are separate instrumentation evidence, not assembly path probes.

The report is `build/polyhedral-tiling/native/report.json`, SHA-256
`7c35aeb104297c1d81f1cd639aa17a574a82425783bf293ee4140c61ef93c80b`.
It binds the compiler, proof report, native producers, actual phase outputs,
raw and adapted candidates, C and Clight inputs, assembly and observations.
No speedup or reduced checking cost is established.

The complete compiler entry is
`ClightSelectedTensorGeneratedCompiler.compile_selected_tensor_generated_regions`.
With the pinned toolchain and the previously built scheduler:

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/polyhedral_tiling.mk proof
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/polyhedral_tiling.mk compiler
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/polyhedral_tiling.mk native
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/polyhedral_tiling.mk validate
```

The scheduler recipe and its unreplayed fresh-build boundary remain as recorded
in [the affine pipeline stage](connected-polyhedral-pipeline.md). Use the new
`polyhedral-tiling` artifact directory; the older reports remain frozen.

The demanding part remains the domain and language boundary: safe condition
evaluation from source-definedness, machine/model correspondence, loaded-bound
stability, and candidate progress and effects visible to the continuation.
The generic local composition theorem does not discharge those obligations.
Host contract clauses remain an open factoring question, to be tested against
real hosts as described in [`context-lifting.md`](topdown/context-lifting.md).

After actual tiling acceptance, the plan continues with combined loaded headers
and dynamic address layouts, compact sufficient entry conditions where
available, and separate measurements of guard work, accepted inputs, generated
code size and performance. The existing bounded source family is not a claim
of complete OLO coverage.
