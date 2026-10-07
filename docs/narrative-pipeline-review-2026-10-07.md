# Annotated polyhedral compilation: narrative review and integration plan

Reviewed on 2026-10-07 against `origin/topdown/research-positioning` at
`12419c1e1e3da450bf378742a2fb4e204e51e060`. The new commits are `1c63ccb`
and `12419c1`; main's narrative and top-down README now retain their wording.
This review changes the next integration milestone in the active goal.

## Decision and current evidence

The next milestone is an annotated C region optimized through a real
polyhedral scheduling and code-generation pipeline. Default selection uses
`#pragma scop` / `#pragma endscop`. An annotation requests an attempt and
supplies no validity, no-wrap, alias, stability or execution evidence.
Automatic discovery can remain an explicit experimental mode.

The current native compiler proposes a candidate Loop AST, extracts source and
candidate, validates correspondence and dependences, lowers the accepted
candidate, then installs its guard and original fallback. These are real
verified services. They do not establish that the native driver calls the
external scheduler or PolCert's prepared code generator. Built-in candidate
policies and external Loop candidates remain regression fixtures and a useful
framework API, rather than acceptance evidence for this new milestone.

The source checks for this review are:

| Boundary | Current implementation | Consequence for integration |
| --- | --- | --- |
| In-function pragmas | `vendor/CompCert/cparser/Elab.ml`, `elab_definition`, ignores local pragmas | Capture region selection before elaboration; retain it through normalization. |
| Region discovery | `GuardMemoryCompiler.memory_program_candidates` visits all statements | Restrict the default optimization offer to selected regions. |
| Installation identity | `select_memory_tiled_table` and the current host use structural AST lookup | Filtering discovery alone is insufficient: an identical unmarked loop must remain untouched. Carry site identity into installation. |
| External scheduling | `adapters/compcert-memory/GuardMemoryPolyhedral.v`, `GuardMemoryIRs`, returns errors/`None` for scheduler/phase export | Add a separate connected instance; preserve the frozen instance and its reports. |
| Optimizer proof | `theories/PolCertOptimizer.v`, `optimize_version`, calls `Core.Opt_prepared`; `PolCertOptimizerRegion.v` exposes a region bridge | The adapter exists, but the native C driver does not invoke it. |
| Real pipeline | Vendored `driver/PolOpt.v`: extraction, strengthening, checked affine phase, checked tiling phase, `PrepareCore.prepared_codegen` | Reuse these stages where their representation and execution contracts match. |
| Current candidate lowering | Existing affine/tensor lowerers check a supported Loop syntax and resource profile | Generated Loop code needs an actual supported lowering and execution bridge; a backward optimizer endpoint alone does not supply candidate progress. |

These are source observations, not a new proof audit or native integration run.
The five in-progress word-column proof files remain uncommitted work; no new
audited column/outer theorem or compiler is claimed by this review.

## Implementation order

1. Implement explicit selection in an isolated frontend path. Inspect the
   actual parser and normalized ASTs, reject unsupported marker structures
   conservatively, and preserve location identity during installation. Test an
   annotated and structurally identical unannotated loop in the same function,
   multiple marked sites, and no markers. Do not use a name prefix or a pragma
   as a semantic certificate.
2. Instantiate the real pipeline for a first already supported source family.
   Start with the prepared optimizer and existing Pluto phase interfaces.
   Record source Loop/model, exported OpenScop, affine midpoint, tiled result,
   witnesses, validation outcomes and generated Loop. Resolve instruction,
   parameter, access-coordinate and lowering compatibility at each boundary.
   User options may choose phases and tile sizes; no hand-written target loop
   should be needed for this demonstrated path.
3. Connect that generated candidate to the existing source-derived safe guard,
   original-source fallback, public-exit restoration, private resources and
   language host. Supply any necessary candidate progress or actual
   source/generated-code correspondence. Run actual marked C to assembly and
   bind it to the connected compiler's whole-program correctness endpoint.
4. Once this slice closes, improve guard derivation and measure check work,
   code size, useful acceptance and paired complete-call cost. Continue the
   loaded-bound/dynamic-layout expansion when it is a dependency of the
   connected example; it is not a prerequisite to connecting every first
   supported annotated source family.

The earlier proof-first decision still orders proof closure before guard-cost
improvements. It does not place all source-family extensions before scheduler
integration. The previous plan's unconditional next step of completing every
inner/outer word scan is superseded by this integration order. Retain those
proofs and finish immediate dependencies when the selected example needs them.

## Responsibilities and difficult boundaries

The generic kernel remains responsible for local guard/candidate certificate
composition. It neither parses pragmas nor chooses schedules.

The language/IR instance owns safe concrete check execution, private state,
legal placement and reusable whole-program installation laws. Selection must
remain site-specific, with labels, exits and progress checked independently of
the marker. A prototype parser pass is part of the native frontend boundary;
it does not itself prove Csem-to-Asm preservation or selected-only installation.

The optimizer/domain implementation owns conditional extraction, sufficient
assumptions, actual source/model correspondence, checked phase transitions and
generated-candidate execution. The user of a supported family supplies marked
source and options, rather than hand-filling semantic callbacks or constructing
the target Loop. New language/domain families still require their own proofs.

The hard work crosses these boundaries: source-definedness must license the
guard without assuming the stability it is checking; accepted observations must
justify the model; the generated Loop and concrete check exit must agree on
parameters and memory; candidate progress and public exits must satisfy the
installation contract. Scheduler output is untrusted, and its failure or an
unsupported representation must preserve the original region.

## Milestone acceptance

Completion requires all of the following evidence from the same connected path:

- A marked C region transformed using an actual scheduler/codegen result, with
  retained intermediate representations and validator outcomes.
- A comparable unmarked region excluded, including an identical AST at a
  different site; multiple marked regions handled independently.
- Static refusal and runtime-guard refusal retain the actual source region.
- Actual generated-candidate execution, public-exit and host proofs connected
  to a Csem-to-Asm correctness endpoint and native C run.
- Plan, manuscript and evidence map identify the exact supported family and
  any source adaptations, unfinished transitions or usability gaps.

A parser experiment, an optimizer module compiling, or another direct candidate
fixture is partial evidence. The active full implementation goal remains open.
