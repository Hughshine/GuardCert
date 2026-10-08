# Narrative alignment and the next implementation contract

Date: 2026-10-07. Reviewed narrative revision:
`12419c1e1e3da450bf378742a2fb4e204e51e060`.

The fetched [paper narrative](paper-narrative.md) and
[context-lifting discussion](context-lifting.md) match main. This review checks
their responsibility boundaries against the current code and fixes the next
acceptance criteria. It adds no proof endpoint, guard implementation, compiler
capability, or experimental result.

## What the current interfaces establish

| Responsibility | Current code boundary | What an implementation must supply |
| --- | --- | --- |
| Semantic kernel | `guardify_refinement` / `guardify_preservation` in [GuardInterface.v](../../prototype/interface/GuardInterface.v), and `guarded_rewrite_equivalent` in [GuardedRewrite.v](../../prototype/interface/GuardedRewrite.v) | Abstract host laws and certificates; the kernel composes them into local correctness. |
| Language installation | `projected_region_contract` in [ClightPrivateRegion.v](../../theories/ClightPrivateRegion.v) and the simulation in [ClightPrivateRegionProof.v](../../theories/ClightPrivateRegionProof.v) | Actual target execution, live-temp agreement, memory relation, source progress, scope and fresh private resources. |
| Open-region installation | `open_region_protocol` / `open_region_contract` in [ClightOpenRegionContract.v](../../theories/ClightOpenRegionContract.v) | A step protocol that can keep matching source steps without an exit. |
| Optimizer/domain | [Multi-array source decoding](../../adapters/compcert-memory/GuardMemoryMultiTensorSourceRegion.v), [source/candidate execution](../../prototype/interface/ClightMultiTensorSourceCandidates.v), and the domain candidate checkers | Source/model correspondence, sufficient assumptions, condition derivation and candidate correctness. |
| Concrete site | Selected frontend/host checks, including [the installed loaded-word compiler](../../prototype/interface/ClightSelectedZeroLoadedWordFrontendCompiler.v) | Region identity, legal placement, source recognition, supported progress and private-resource evidence. |

`context_certificate.lift_refinement` and `rewrite_context.rewrite_lift` are
host-supplied theorems. The generic records do not prove contextual closure for
an arbitrary language or a weak local observation relation. The concrete
Clight proof separately requires `SUPPORTED_SOUND`, `SELECT_SOUND`,
`PROGRAM_SCOPE`, and `POOL_FRESH`.

There are two users of these interfaces. A language or transformation author
provides the reusable proofs above. A source-program user of an implemented
family supplies marked C and phase/tile options; the family factory and host
checkers must produce its evidence. Unproved source/model or guard-safety
obligations must not be turned into callbacks requested from that source user.

## What the host comparison supports

The exact-temp `region_contract`, projected-temp `projected_region_contract`,
and `open_region_exit` share a normal `Sskip` boundary, a CompCert memory
relation, and a temporary-state relation. The projected and open exits already
reuse `temp_agree`; [ClightTempFrame.v](../../theories/ClightTempFrame.v) provides
reflexivity, transitivity and weakening of that relation.

Their progress obligations differ. The projected contract consumes a silent,
normally completed source execution and produces target small steps. Its
installation also consumes a separate
[source progress protocol](../../theories/ClightRegionProgress.v). The open
contract instead supplies a step simulation with a decreasing index for
zero-step matching. Equality of completed exits cannot replace that protocol.
The shared realization in
[ClightSharedRegion.v](../../theories/ClightSharedRegion.v) changes the control
implementation of choice; it proves execution and then reuses a region
contract. It is not a new universal context relation.

This identifies reusable state/memory clauses and essential progress
differences. It does not justify a new freely composable contract algebra.
There is no demonstrated current transformation blocked specifically by the
existing exit relation in this review, and no measured reduction in author
work from further factoring. Keep that design question open; do not change the
kernel to rename existing obligations. The current selected compiler uses
`program_temps` as a conservative live set, not a new minimal liveness analysis.

## The next hard connection: a static guard from source-licensed observations

The [multi-array permission checkpoint](../multi-array-source-permissions.md)
establishes entry pointer/parameter observations and valid aligned addresses
from actual canonical source execution. Its reference alias tree is indexed
by runtime counts and parameters. It is a specification witness; it does not
yet constitute code emitted by an ahead-of-time compiler.

The next producer must have this staging shape:

```text
static source description + static resource/phase options
    -> option (guard AST + checked metadata)

one fixed guard AST + an actual runtime entry
    -> refusal, or accepted facts at the actual guard exit
```

The guard AST must be independent of unknown runtime counts, scalar values,
locations and footprint lists. Those belong in the correctness theorem and
are read by emitted code through licensed operations. A scanner may use
private cursors/caches/flags while preserving public state and memory.

Acceptance for this producer requires all of the following:

1. **Source-licensed safety.** Check evaluation is defined from original-source
   observations and actual access permissions. It does not assume the
   non-aliasing or stability proposition the guard is intended to establish.
   Empty paths and refusal avoid unlicensed future observations.
2. **Runtime coverage and sufficiency.** Accepted checks cover the actual
   source obligations and imply the separation/stability used by the existing
   candidate theorem. Equal logical cells that encode intentional dependencies
   must not be confused with distinct cells that require separation.
3. **Actual exit transport.** Private-state changes preserve the source's
   public entry on refusal and establish the candidate's required entry on
   acceptance. Entry facts alone do not establish facts at a changed exit.
4. **Data-produced evidence.** Source-family checkers produce static
   shape/scope/freshness evidence and local certificates. The installed API
   must not ask its caller to assume source execution, `NonAlias`, or an
   arbitrary simulation.

Language libraries own defined evaluation, pointer primitives, permission and
frame laws, private control, and installation. The tensor domain owns the
coverage argument, the sufficient condition and the source/model connection.
The kernel consumes the resulting local certificates without learning tensor
semantics.

There is an additional dependency for loaded headers. At each actually reached
point, obtain read/write permission, check preservation by both stores, and
only then advance to the next original source test. A changed header can
change the later reached domain. Therefore, the complete canonical-source
footprint theorem cannot license an original loaded-source scan before that
prefix/stability proof has established the cached-source correspondence.
Permissions transport backward through stores; loaded integer values do not.

The first scanner may target the supported canonical two-array family. That is
an intermediate library milestone. Integration acceptance still requires the
same extended loaded/Horner C program, actual polyhedral phases and generated
candidate, original fallback, selected host, Csem-to-Asm endpoint, and native
accept/refuse/context evidence. The existing installed single-body pipeline
does not install the new multi-array certificates automatically.

## Evaluation and repeated rewrites

After this agreed slice is installed, improve sufficient conditions while
reusing candidate and host proofs when their contracts still apply. Record
generated code size, runtime check work, useful accepted inputs, whole-call
cost and instance-author work separately. A cursor loop addresses code growth;
it does not by itself remove pairwise or per-point runtime work. Scans remain
an intermediate implementation, not the final OLO usability claim.

Finite repeated application uses a certificate for each successive program.
After a rewrite changes code or a boundary, the next rule must establish its
placement and assumptions against that changed program. Transitivity does not
make stale site evidence reusable without proof.

The active goal retains the complete compiler and OLO coverage criteria. This
review changes the presentation and acceptance checklist, not that objective.
