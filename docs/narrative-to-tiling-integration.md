# Narrative Clarification and the Actual Generated Candidate

This note is for an optimizer implementer using GuardCert's CompCert instance.
It records how the current integration follows
[`paper-narrative.md`](topdown/paper-narrative.md), rather than changing the
language-independent kernel to accommodate a particular loop transformation.
On 2026-10-07, the remote narrative reference was
`12419c1e1e3da450bf378742a2fb4e204e51e060`; its narrative text already matched
main. The implementation target remains the complete sequential guarded
polyhedral compiler, with OLO as a functional and usability reference.

The [loaded-word cost and condition checkpoint](loaded-word-condition-cost.md)
now separates usability from correctness on that same installed family. The
720 paired batches expose a dense complete-call regression of 17.69/20.43 times
source; the independent Clight work count does not identify all of its causes.
A new checked zero-RMW effect law and its existing `readonly_condition`
encoding permit header aliases without changing the kernel. The condition-only checkpoint did not establish installation. The
[zero-capable successor](zero-loaded-word-installation.md) now proves source-point
licensing, capture/helper/check-exit and canonical execution, produces the local
contract and reuses the selected host. Its new Csem-to-Asm compiler and same-C
native matrix preserve the existing assumptions. A fresh paired comparison
shows expanded alias acceptance and zero scan work, but no complete-call
speedup; candidate lowering and profitability take priority in cost work.
The active plan also retains compact nonzero-RMW footprint conditions,
candidate-lowering costs and conservative profitability policies.

The [tight-bound successor](tight-loaded-word-candidates.md) addresses one
concrete candidate cost: the old affine adapter enumerated the full source
extent inside each tile. Its untrusted replacement proposes tile-local point
ranges and simpler guards; the same final checker and compiler theorem supply
the certificate. Seven native configurations and a fresh cost/instruction
comparison pass. Unit tiles are a recorded negative case: raw codegen removes
tile dimensions and final installation refuses their unchanged witness. Dense
zero complete cost falls to about 2.97 times source, still a slowdown. This
reuses the existing responsibility boundary; it neither changes the kernel nor
closes general-domain, nonzero-condition, full OLO/BT or profitability work.

The [unit-coordinate/positive-offset successor](unit-tile-and-positive-offset.md)
now proposes singleton coordinates for partially unit tiles and mapped reindex
for the all-unit raw result. All eight diagnostic probes pass final domain
checking and show installed dispatches; those probes do not call the region.
The fresh full matrix passes 2,352 Asm and 1,792 separate Clight calls over
both layouts and all masks.
Separately, the same compiler passes 1,215 Asm calls and 540 Clight dispatch
checks on actual loaded `+1` bounds, wrapping, empty paths and alias contexts.
New arithmetic/receipt services interpret the cached profile as a mathematical
no-overflow bound without changing source read licensing or installing a new
runtime encoder. The next domain gate connects real statement sequences,
multiple arrays and true cross-iteration dependencies in this same pipeline.
The latest fetch still resolves to `12419c1`; both narrative documents match main.

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

## Loaded Bounds and Dynamic Addresses: Next Acceptance Gate

A fresh fetch on 2026-10-07 still resolves the narrative branch to
`12419c1e1e3da450bf378742a2fb4e204e51e060`. Both the narrative and
`context-lifting.md` match main. The clarification determines the following
proof dependencies for the next source family, without changing the kernel.

The source combines `i < grid[0]+1`, `j < grid[1]+1`, a literal component
bound, and the runtime address `a[((i*ld)+j)*5+k]`. The header storage may alias
the data storage. Consequently, source-definedness, captured header words,
mathematical no-wrap assumptions, and header stability are separate facts.

| Certificate link | Current evidence for this source family | Obligation to close next |
| --- | --- | --- |
| `C_derive` | The driver composes actual conditional capture, count gates, helper initialization and scanning. The [checked family factory](loaded-word-family-factory.md) derives its static resources and canonical package from AST data. | Extend source/model capabilities and reduce condition work on the installed family. |
| `C_guard` | Scan acceptance derives canonical execution; the full guard's accepting tree and execution reach the actual complete-check exit. The same loaded/runtime-Horner C validates actual accepting/refusing dispatch. | Prove compact condition replacements against this complete-check boundary. |
| `C_opt` | The actual affine/tiled candidate checker proves final-memory/public-exit correspondence at that exit. Real scheduler/tiling/prepared-codegen output is bound to the factory and checked on the same C. | Broaden domains and candidate transformations toward the full objective. |
| `C_host` | Check/choice laws implement full-check dispatch. The factory/host check actual private allocation, source control and frontend administrative equivalences. | Measure author obligations and keep these checks automatic. |
| Installation (language host and site) | Selected base/frontend/padded-leaf Csem-to-Asm endpoints and same-C native installation pass, including unmarked/repeated sites and continuation effects. | Quantify complete-execution costs and apply the host boundary to future families. |

The four certificate links describe local proof ownership and reuse; installation
is a further language/IR step. They are not new records that an end user must
prove for every marked region. The optimizer's data-only
checker must produce the supported family's static syntax, scope, typing and
freshness evidence. The language library owns arithmetic execution, permission
transport, private-state frames and installation laws; the domain instance
wires its loaded-bound shape and model to those laws.

The loaded-driver audit queries 22 endpoints over 524 dependencies, with no
globals added to the existing CompCert/PolCert baseline. Its actual-memory
fixtures instantiate capture and full stability scanning with undefined
incoming caches/helper, and prove canonical/original execution from the scan
exit. Their wrapping address ignores row and column; the generic full
guard/generated-candidate theorem is not yet a native runtime-Horner case or a
loaded-family compiler installation.

The succeeding factory/padded-frontend pipeline adds 420 unmodified assembly
calls and 168 separate instrumented Clight dispatch calls on the same loaded
headers and runtime-Horner RMW source. Actual tiling candidates are installed;
changing-header aliases, profile/layout refusal, empty-root unavailable reads,
marked/unmarked regions, repeated sites and continuation exits pass. The
[family report](loaded-word-family-factory.md) binds three independent proof
checkpoints and the later native report. This closes that integration slice;
compact conditions, acceptance and paired complete-execution costs remain work.

The safe scan must obtain each address permission from a reached original
source execution. Acceptance at a point proves preservation of both captured
raw observations before advancing that original prefix. A refusal stops later
checks. Assuming that the entire cached source is already executable would
reverse this dependency and would not establish guard safety. Likewise, a
captured `raw+1` machine word does not itself prove the mathematical no-wrap
condition needed by the polyhedral model.

Acceptance of this milestone requires the same loaded/dynamic C input to run
through capture, full stability checking, cached-source/model transport, the
real scheduler and code generator, final candidate checking, original-source
fallback, selected installation and assembly. Native cases must cover accepted
inputs, alias and profile refusal, empty paths that skip unavailable reads,
marked/unmarked regions, repeated sites and continuation-visible exits. Separate
loaded-bound and dynamic-layout examples do not establish this combination.

Once that declared slice is proved, guard improvements must independently
establish safety, acceptance soundness and entry-state transport while reusing
candidate and host certificates. Code size, per-point work, acceptance, full
execution cost and per-instance manual work remain separate measurements. No
new proof, native or cost result is claimed by this plan refinement.
