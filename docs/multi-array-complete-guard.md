# Source-licensed complete conditions for the canonical two-array family

Date: 2026-10-08. This succeeds the frozen
[scan-exit checkpoint](multi-array-scan-exit.md).

The canonical two-array path now emits a complete setup condition before its
address-pair scan. Acceptance produces the numeric, layout, coordinate-box and
parameter-range facts required by the actual candidate theorem. Failure of
either the setup condition or the alias scan executes the original source AST.
The resulting local execution theorem has no dynamic setup or separation
premise supplied by its caller.

This is a complete local guard for the supported temporary-bound family, not
its whole-program installation. Loaded-header preservation, typed private
resources, a frame for arbitrary program live temporaries, progress and the
family's Csem-to-Asm factory remain open.

## Reuse the existing encoders

The new path reuses `tensor_source_layout_guard`, `tensor_complete_tree`, the
checked tensor volume encoder and `compile_tensor_box_guard`. Its static tree
depends on source metadata and a proposed arithmetic profile, not runtime
counts, addresses or footprint lists.

[ClightMultiTensorSourceGuard.v](../prototype/interface/ClightMultiTensorSourceGuard.v)
licenses the existing layout tree from actual assignment-list source execution.
The source supplies the outer iterator word. An accepted zero-start test
licenses checking the first bound. Each accepted positive bound licenses the
next source level. Only after all bound checks accept does an actually reached
leaf supply the used scalar and dimension words. Each assignment's reads remain
in its own intermediate memory. Layout acceptance or cross-array separation
does not license these observations.

The module proves exact check execution and acceptance implying initial-counter,
positive/ranged-bound and layout facts. Its `readonly_condition` certificate
uses the existing framework API. A metadata-only purity lemma avoids requiring
a single-operation source package merely to prove the shared layout tree pure.

[ClightMultiTensorCompleteGuard.v](../prototype/interface/ClightMultiTensorCompleteGuard.v)
collects coordinate terms from every checked write and read in the body.
The existing profile and box compiler lowers those terms with verified machine
arithmetic. Its certificates prove check safety, availability and acceptance
soundness. Accepted checks produce actual count/scalar bindings, signed scalar
values, observed dimensions, backend-guard acceptance, coverage of all body
accesses and the candidate checker's parameter ranges.

The profile is a static sufficient-condition proposal. Its compiler may refuse
an expression whose intermediate arithmetic is not proved safe. This is not
general Presburger projection, arbitrary assumption inference or a native
overflow-flag interface.

## Execute both rejection paths and the candidate

[ClightMultiTensorCompleteCandidates.v](../prototype/interface/ClightMultiTensorCompleteCandidates.v)
constructs the following statement:

```text
if generated_setup_tree:
    pair_guard;
    if private_alias_flag:
        checked_generated_candidate;
        restore_public_iterators;
    else:
        original_source_AST;
else:
    original_source_AST;
```

`multi_tensor_demo_full_versioned_execution` starts from actual original-source
execution and static compilation/checker evidence. It runs the complete setup
tree. Acceptance derives the earlier pair-scan theorem's explicit setup facts;
that theorem runs the scan and candidate from the actual scan exit. Setup
refusal uses the original AST directly, while alias refusal uses its established
transport through the private scan. The final memory matches the source, with
agreement on requested live temporaries within the fixed public ports.

The theorem does not assume positive counts, zero start, scalar/dimension
availability, layout acceptance, coordinate-box acceptance, validator ranges
or `NonAlias` at entry. These are now conclusions of accepted checks. It still
requires a static signed cap, successful static condition compilation, actual
candidate-check success and normally completed source execution. The latter is
the proof domain for local preservation, not an assertion supplied by a C user.

## Concrete producer and condition semantics

[ClightMultiTensorCompleteExample.v](../prototype/interface/ClightMultiTensorCompleteExample.v)
successfully compiles a static profile for cap 32 and the actual four accesses
of the two-store source. Concrete decision-execution proofs cover coordinate
acceptance, excessive columns/components, profile refusal and an empty outer
bound with absent child/scalar/pointer bindings. A large-coefficient probe is
refused statically because its intermediate arithmetic is not certified safe.

`multi_tensor_demo_setup_condition` uses the existing
`readonly_condition_entails` combinator to expose the mathematical setup
property. Its premise includes initial/ranged counters, observed layout and
coverage of all actual body accesses; it is more than a flag-equality claim.
Safety and availability come from the condition encoder, and semantic
sufficiency comes from the domain derivation theorem.

`check_multi_tensor_demo_full_versioned` consumes candidate data, runs the
existing generated-candidate checker and wraps accepted Clight code with the
compiled complete guard. Its execution theorem preserves source final memory
and the requested public exit. It returns a local statement, not a selected
program/compiler result. Candidate construction remains a separate producer;
this wrapper does not connect another scheduler or codegen phase.

## Responsibilities and next integration

The kernel and host contracts are unchanged. Language libraries provide source
observation/definedness, checked arithmetic, choice execution and frames. The
domain provides the assignment-list coverage, profile proposal, setup
derivation and candidate connection. Existing framework condition entailment
composes the encoder with the semantic premise without inspecting tensor code.

The fixed example's live-state theorem covers a subset of its source public
ports. A whole-program host may request additional context temporaries through
`program_temps`; their frame must be derived from the guard's actual write set
and freshness. The factory must also check typed private resources, source
shape/selection and the supported progress protocol. This cannot be replaced
by asking source-program users to supply a simulation or separation callback.

For loaded bounds, both stores must preserve captured headers at each actual
source point before advancing the next original test. An unproved cached
rectangle still cannot license future checks. Entry permissions do not move a
later initialized integer value backward. After these connections, install the
same family through actual polyhedral phases/codegen and the selected host,
then validate native acceptance/refusal, annotations, repeated sites and
observable continuations.

The alias scan remains quadratic and continues after alias refusal. Setup
refusal now skips it entirely. Compact conditions, useful acceptance, guard
work, code size and full-call profitability remain separate OLO obligations.

## Validation boundary

The four successor modules compile with CompCert 3.18 and Rocq/Stdlib 9.2.
The independent helper is `scripts/audit_multi_tensor_complete_guard.py`;
`scripts/compile_multi_tensor_complete_guard_sources.py` builds only missing
successor objects and preserves historical inputs.

The audit queries 26 endpoints: eight closed, with at most fourteen existing
globals per endpoint. All remain within the old 42-global compiler baseline;
there is no new global axiom. The report binds 129 files and validates the
frozen scan-exit prerequisite closure.

Report: `build/multi-tensor-complete-guard/proof/report.json`.
SHA-256: `00543a521a20ab40eea285e7a59844c33ed94fce92dfceb6bcc0198e122fd9e5`.

This checkpoint adds no compiler theorem, C/assembly matrix or measured cost.
