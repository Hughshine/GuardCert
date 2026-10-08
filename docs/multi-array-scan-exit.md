# Canonical two-array execution from the actual scan exit

Date: 2026-10-08. This succeeds the frozen
[runtime pair-scan checkpoint](multi-array-runtime-pair-scan.md).

The canonical two-array pair scan now connects to both actual branches of the
versioned Clight statement. Acceptance supplies source-footprint separation at
the scan exit, where the checked candidate executes and restores public
iterators. Refusal executes the original source AST from that same exit. Both
branches preserve the original final memory and requested public exit values.

This closes the scan-exit connection for the positive, temporary-bound source
family. The theorem still assumes numeric, layout, box and parameter-profile
setup. Producing those facts with a complete safe guard, extending loaded-header
preservation and installing this family into C-to-assembly compilation remain
required work.

## Why entry facts need transport

The scan initializes its private flag and two cursor vectors. The temporary
environment at its exit therefore differs from the original source entry.
Conditional candidate correctness at the old entry alone does not justify
executing the candidate from that exit.

[GuardMemoryMultiTensorGuardExit.v](../adapters/compcert-memory/GuardMemoryMultiTensorGuardExit.v)
provides four reusable transport lemmas. Agreement on dimension registers
preserves dimension observation and acceptance of the existing tensor backend
guard. Agreement on used pointer registers preserves the locator restricted to
the actual source footprint and transports its separation property. The proof
uses pointwise restricted-locator agreement; it does not require equality of
the complete raw registry or add an extensionality axiom.

[ClightMultiTensorPairScanExit.v](../prototype/interface/ClightMultiTensorPairScanExit.v)
checks the actual source statement's scope and iterator writes. The existing
structured execution transport theorem then constructs execution of that
original statement from scan-exit temporaries, with the same final memory and
related public exit. The module also transports the concrete family's bound,
scalar, root-counter, dimension and layout-guard setup, and its separation
premise. Pointer membership comes from checked source-footprint coverage.

## The actual versioned statement

[ClightMultiTensorPairScanCandidates.v](../prototype/interface/ClightMultiTensorPairScanCandidates.v)
defines the following static statement:

```text
pair_guard;                         // initializes flag and compares addresses
if private_flag:
    checked_generated_candidate;
    restore_public_iterators;
else:
    original_source_AST;
```

`multi_tensor_demo_pair_candidate_at_exit` combines the transported source
execution, setup and separation with the existing generated-candidate checker
theorem. It constructs execution of the actual emitted Clight code followed by
iterator restoration, starting from the actual scan exit. The final memory is
the original source's final memory. Requested live temporaries must lie within
the scan's preserved public ports.

`multi_tensor_demo_pair_versioned_execution` constructs execution of the whole
statement above. It consumes actual original-source execution and a successful
candidate-check result, runs the source-licensed scan, and selects the branch
using its actual flag. Acceptance establishes separation rather than asking
the caller to provide it. Refusal uses transported execution of the original
AST. Neither branch assumes that all entry array words contain integers.

The theorem handles alias acceptance/refusal after its explicit setup
conditions hold. It is not yet a full guard that tests those setup conditions
and falls back when any of them fail. It covers silent, normally completed,
positive canonical nests; it does not provide empty-path handling, a source
progress protocol or a whole-program region contract for this new family.

## Responsibility boundaries from the narrative

The fetched narrative revision remains `12419c1`; its text matches main. This
connection follows its kernel/language/domain cutoff without changing the
kernel or introducing a new host contract.

| Layer | Responsibility exercised here | Remaining responsibility |
| --- | --- | --- |
| Framework kernel | Existing certificate composition interface remains available and unchanged. | Consume a completed local certificate; no tensor-specific condition inference. |
| Language/IR libraries and host | Dimension/locator frames, concrete choice execution, original-AST transport and public exit relations. | Typed private resources, supported progress, placement and whole-program installation for this family. |
| Domain/transformation | Actual two-array source scope/footprint, source-derived scan permission and separation, checked candidate and restore connection. | Safe production of the explicit setup conditions, loaded-source correspondence and factory-produced region guarantees. |

These are library theorems for transformation authors. Source-program users
should ultimately supply annotated C and phase/tile options. Missing setup or
source/model proofs must be produced by the implemented family, not exposed as
semantic callbacks to those users.

## Next integration obligations

Produce numeric, layout, coordinate-box and parameter-profile evidence from
the actual source's licensed observations. Combine those checks with the pair
scan and transport their accepted facts through the same actual exit. Static
source/scope/freshness evidence must come from a typed data factory.

For loaded bounds, establish each reached point's permissions and prove both
stores preserve every captured header before advancing the next original test.
Only an established cached-source correspondence may license a scan of its
complete rectangle. The second store can read a value initialized by the first;
entry permission does not justify moving that read or its arithmetic backward.

Then connect the same family to actual polyhedral phases/codegen, the factory,
selected Clight host and Csem-to-Asm theorem. Acceptance, alias/profile refusal,
conditional empty paths, marked/unmarked regions, repeated sites and observable
continuations require evidence from that installed path. The earlier installed
single-RMW compiler is a separate established family.

The scan still compares all point pairs, including after its flag becomes
false. Its quadratic runtime work, compact-condition replacement, useful
acceptance domain and full-call cost remain separate OLO usability obligations.

## Validation boundary

The three successor modules compile with CompCert 3.18 and Rocq/Stdlib 9.2.
`scripts/audit_multi_tensor_scan_exit.py` queries all eleven declared endpoints
and binds the new sources/objects to the validated runtime-scan prerequisite.
Its missing-object builder is
`scripts/compile_multi_tensor_scan_exit_sources.py`. Historical proof inputs
remain frozen and are not recompiled.

The independent audit passes: eleven endpoints, six closed, with at most
fourteen existing globals per endpoint. Those globals remain within the old
42-global compiler baseline; no new global axiom is introduced. The candidate
endpoints retain the existing domain checker's assumptions. The audit binds
97 files and validates the frozen prerequisite closure.

Report: `build/multi-tensor-scan-exit/proof/report.json`.
SHA-256: `55b70d67d9e48bfd00722a6d7f99c1dd3fc14a69c89a672ff8552995c43962dc`.

No compiler theorem, C/assembly execution matrix or measured cost is added by
this checkpoint.
