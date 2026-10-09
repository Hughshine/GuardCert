# Runtime Empty Alternatives Reusing Existing Candidate Certificates

Date: 2026-10-08. Reviewed narrative reference:
`origin/topdown/research-positioning@c4b1395668786f20cdb75fb2db020dd651bb4684`.
A fresh fetch and remote-head query found no later narrative commit; the main
copy of [paper-narrative.md](topdown/paper-narrative.md) is identical.

This successor connects the installed [signed empty condition
client](affine-empty-signed-installation.md) to sites that already have a
polyhedral candidate. It reuses that candidate's certificate and the existing
selected CompCert installation. The source grammar and bounded header profiles
are unchanged. Source users still provide marked C and policy options.

## Generated Control and Its Proof

For a checked site with an existing target, the new target has this shape:

```text
original read prefix;
conditional header capture;
empty-check plan -> private Boolean;
if Boolean:
    outer empty ? skip : exact empty-loop public restoration;
    original quiet suffix;
else:
    previous entire certified target;
```

The previous target occurs once. Its own guard, generated candidate and source
fallback remain inside that target. The new accepting branch contains no loop
fallback. A rejected wrapper construction keeps the previous target exactly.
If the old registry returns no target, the compiler uses the preceding signed
standalone empty builder and its nonnegative backup.

The refused branch can repeat the previous target's source read prefix and
capture. This needs proof: public prefix outputs may already have been
assigned, and private caches/result may differ from their initial values.
`source_prefix_output_transport` requires agreement only on the read prefix's
pointer inputs, allowing duplicate output temporaries. Under the checked
disjointness of prefix outputs and pointer inputs, `source_prefix_replay` proves
that a completed prefix can execute again with exactly the same state. The
reads and replay do not change memory.

`projected_dispatch_prelude` separates two producer obligations. Acceptance
supplies actual fast-branch execution with the original final memory and public
exit. Refusal supplies a source replay entry related to the checked entry by
`temp_agree live`, together with the original source execution from that entry.
`projected_runtime_dispatch_contract` then consumes the previous target's
`projected_region_contract`. It stitches actual prelude/branch steps to the old
target's small-step execution; it does not demand a new big-step certificate or
inspect the old AST. Source progress, labels, placement and private resources
remain installation obligations.

The concrete `affine_empty_runtime_prelude` produces these obligations from
original Clight execution. It derives conditional capture receipts, applies the
unchanged empty condition client, executes the check plan and transports the
private result. Its refused entry reuses exact prefix replay. Its accepted
branch transports the real quiet suffix, including suffix memory writes.
Source execution is the proof starting point; generated code does not execute
the source loop before checking.

## Responsibility and Premise Provenance

| Responsibility | Evidence supplied in this stage |
| --- | --- |
| Generic kernel | Existing local certificate composition; no kernel edit |
| Domain condition author | Existing signed producer proves safe invocation and acceptance implying the same empty-loop facts |
| Clight language library | Pointer-input transport, exact source-prefix replay, private-result dispatch and small-step composition with an opaque old target |
| Concrete source client | `affine_empty_runtime_prelude` derives actual capture/check entries and original public exits; acceptance retains the suffix |
| Checked site factory | Actual source description, prefix disjointness, typed caches/result, capture resources, static condition lowering and branch freshness |
| Previous optimizer | Its existing source/model/candidate and public-exit certificate, consumed unchanged through the previous projected contract |
| Language installation | Existing selected host, site/progress checks and backend; `compile_selected_empty_runtime_regions_correct` yields Csem-to-Asm backward simulation |

The narrative's concrete-to-model distinction still applies. On the old
candidate branch, original Clight to captured/stable source to source Loop to
candidate Loop to lowered Clight/public restoration retains the existing
directions and premises. The empty branch instead uses an actual empty-source
execution/exit certificate; it does not obtain its correctness from polyhedral
validation or a new model decoder.

Static syntax/resource checks, dynamic capture/condition/state transport, and
the given original execution are separate premise sources. No source-user
completion, equivalence, observation or model-correspondence callback is added.
This service belongs above the semantic kernel in the Clight instance. It is
not a general Boolean-OR rule for checks with unrelated invocation domains.

## Checked Evidence

Six new frozen modules total 529 lines, including imports and audit queries.
Fifteen endpoints, two closed, bind 2,028 reachable inputs with at most the same
42 inherited globals and no new axiom. Eighteen archived proof-source attempts
contain six successes and twelve rejections. The selected compiler was
extracted and built with the pinned CompCert 3.18/Rocq 9.2 toolchain.

The two historical empty matrices retain all paths over 2,280 assembly and
2,280 independently executed emitted-Clight calls. Each compares 12,000 array
cells, public exits and continuation effects.

The RMW matrix runs the same 408 inputs in six configurations, totaling 2,448
assembly and 2,448 Clight calls. Every call compares 19,200 cells and public
continuation results. Diagnostics distinguish the new empty branch, the old
candidate and the actual original-loop fallback. Per normal configuration:

| Path | Signed predecessor | Runtime alternative |
| --- | ---: | ---: |
| Empty shortcut | 0 | 58 |
| Existing candidate | 126 | 126 |
| Original fallback | 146 | 88 |
| Unmarked comparator | 136 | 136 |

All old fast paths are retained. When the empty condition refuses, old candidate
choices match every historical input. The 58 additions comprise 44 actual
outer-empty and 14 positive-outer/all-child-empty executions; four have NULL M.
Twenty-four have a header/data or shared-header alias (categories overlap).
Normal ASTs contain two root capture occurrences, one empty choice, one old
candidate choice and one original fallback per marked function. Capture
occurrences are not additional rewrite sites.

Scheduler and resource refusal still install the independent empty rewrite:
58 empty selections and 214 original fallbacks, with no candidate selection.
Unmarked and disabled configurations install neither branch. Actual optimizer
phase artifacts retain source models, OpenScop, transformed/generated loops and
successful affine/tiling/whole-candidate checks for the normal configurations.

Same-binary regressions pass word 400/400, recursive affine 480/480,
private-loaded 270/270 and zero-width 672/672 assembly/Clight calls. The zero-width
matrix retains its 60 candidate choices and adds 56 empty choices per normal
configuration, reducing fallback from 164 to 108. Its nonempty candidate paths
remain unchanged. The regression report also references the already completed
816/816 normal RMW calls from the six-configuration report; these are not an
additional execution batch.

| Checkpoint | SHA-256 |
| --- | --- |
| `build/affine-empty-runtime/proof-v1/report.json` | `f05d39c3050cd0a2aaa3419a63c1255c6ce3002ba5c02fe51ef624103f6b49aa` |
| `build/affine-empty-runtime/compiler-v1/ccomp` | `7f6e461b5a9ce8d8ecebc9905867b9d9454caaff60ff976d733c00ad02741964` |
| `build/affine-empty-runtime/native-v1/report.json` | `d67c00d3d232f0d1717ee6d51c4f4432e7f04b6b51723a1fa2ebb94fa7dbb003` |
| `build/affine-empty-runtime/native-rmw-v1/report.json` | `b35bc8b3c2e409fe91c70111a3648e4121c8491dc054dd8b19b9ca38bc728ec9` |
| `build/affine-empty-runtime/regression-v1/report.json` | `31f6bc18cface8762f2dbfc71988083a7331f75e051ac496618eaa155c5323b6` |

## Remaining Scope

Refusal can repeat source reads and capture, adding work to a nonempty invocation.
This stage measures correctness and paths, not runtime cost or profitability.
It does not infer a globally minimal sufficient condition. Mixed negative/active
children, general recursive loaded-affine domains, broader scalar/chunk services,
dynamic layouts, full OLO/NAS BT coverage and complete-call cost remain active.
The finite region host and existing conservative candidate assumptions retain
their previous boundaries. The full goal is not complete.
