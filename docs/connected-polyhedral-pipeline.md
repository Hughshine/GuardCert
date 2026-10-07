# Connected affine scheduling and prepared code generation

This successor implements the first real pipeline slice requested by narrative
`12419c1`. The user supplies annotated C and phase options. The pipeline exports
its canonical source model, runs Pluto, checks the returned affine schedule,
and invokes PolCert's proved prepared code generator. The resulting Loop is
rechecked, lowered and installed through the existing selected-region compiler.
The main compiler's Csem-to-Asm theorem already quantifies over an arbitrary
data-only candidate proposer; this route instantiates that proposer.

The additional layout phase automatically produces a nonidentity schedule for
the supported column-order tensor. It changes a polyhedral scattering matrix;
it never constructs a target Loop. Pluto alone retains the original order on
these examples. The layout permutation is GuardCert's heuristic, not a result
selected by Pluto. Broader transformations, tiling through this new path,
loaded-header/dynamic-layout integration and cost evaluation remain unfinished.

## User path

For example, mark the original column-order update:

```c
#pragma scop
for (; i < n; ++i)
  for (j = 0; j < columns; ++j)
    for (k = 0; k < 5; ++k)
      a[((j * ld) + i) * 5 + k] += alpha;
#pragma endscop
```

The frontend offers that occurrence to the domain factory. The checked source
description establishes a canonical logical tensor model under the emitted
numeric/address condition. Its logical access coordinates are `(j,i,k)`.
The layout heuristic sees this order in the affine WRITE matrix and proposes
`(j,i,k)` as the schedule. The validator checks the proposed model against the
source; prepared codegen produces the corresponding Loop. The native bridge
proposes adjacent-swap witness data from its actual instruction arguments.
The existing mapped-domain checker verifies those data and the generated Loop,
including the forward execution required by the installation contract.

On acceptance, the generated traversal visits `j`, then `i`, then `k` and
restores the original public loop exits. The original AST remains the runtime
fallback. Private preparation records the literal third bound and supplies the
same parameters to the guard and candidate. The annotation supplies none of
these proofs. A same-shaped unmarked loop beside the marked occurrence remains
outside installation, and two marked occurrences receive separate attempts.

With the already pinned Rocq/CompCert toolchain and the separately supplied
Pluto source archive:

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/polyhedral_pipeline.mk proof
python3 scripts/build_pipeline_pluto.py --archive /path/to/pluto-fixed-source.tar.xz
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/polyhedral_pipeline.mk compiler
```

Compile using only Pluto's affine phase:

```sh
GUARDCERT_PLUTO="$PWD/build/polyhedral-pipeline/pluto-source/tool/pluto" \
GUARDCERT_POLYHEDRAL_MODE=affine \
GUARDCERT_PIPELINE_DUMP="$PWD/build/my-pipeline-dumps" \
build/polyhedral-pipeline/compiler/ccomp \
  -conf build/polyhedral-pipeline/compiler/compcert.ini \
  -stdlib build/polyhedral-pipeline/compiler/runtime -S input.c
```

Use the access-matrix layout phase after Pluto by setting
`GUARDCERT_PLUTO="$PWD/scripts/polyhedral_layout_scheduler.py"` and
`GUARDCERT_LAYOUT_PLUTO="$PWD/build/polyhedral-pipeline/pluto-source/tool/pluto"`.
`GUARDCERT_POLYHEDRAL_MODE=identity` retains the scheduler's identity baseline;
the layout wrapper is a separate phase and should not be used for that baseline.
Use a fresh dump directory for each compilation so receipts cannot be confused
with an earlier run. No target Loop or semantic callback is an input.

## Representations and actual calls

| Step | Implementation | Evidence or refusal |
| --- | --- | --- |
| Selection and source recognition | `GuardScopFrontend` and the existing literal tensor factory | Fresh marker identities and full normalized AST checks; unsupported bodies remain original. |
| Canonical source model | `GuardPreparedTensorCandidate.propose`, `memory_scalar_rectangle` | Source Loop constructed from checked instruction data; the final factory establishes its conditional relation to the original C. |
| Loop extraction | `MemoryPrepared.Extractor.extractor` | PolCert's actual extractor; `source.loop` and its exported model are retained. |
| OpenScop export | `GuardMemoryPreparedPipeline.export_memory_model` | Domain/schedule matrices and instruction/access substitutions; `before.scop`. |
| Scheduling | Native `run` invokes Pluto `--readscop --dumpscop` | Command, process log, before/mid/after models and diagnostic C are retained. Scheduler C is not the installed candidate. |
| Optional layout phase | `polyhedral_layout_scheduler.py` | Original Pluto output, proposed scattering matrix and JSON receipt. |
| Import and affine validation | `from_openscop_like_source`, `GuardMemoryValidator.validate` | Source instructions, accesses and domains are retained; only schedule data are imported. |
| Verified candidate generation | `MemoryPrepared.PrepareCore.prepared_codegen` | Actual generated `Loop`; `generated.loop` and pipeline receipt. |
| Reindex, progress, lowering and guard installation | Existing checked scalar/tensor factory and selected Clight host | Rechecks the generated candidate; actual Clight dispatch and assembly execution. |
| Backend | `compile_selected_tensor_literal_regions` | Existing successful-output Csem-to-Asm correctness endpoint. |

`pipeline-result.txt` reports successful affine validation and codegen. A
`receipt.txt` additionally records that native reindex data were proposed. Those
receipts alone do not prove installation. The native audit also checks actual
Clight dispatch sites, observations and full-program output. Scheduler failure,
malformed transport, rejected import, failed validation, codegen alarm or an
unsupported generated representation returns no candidate and keeps the source.

## Proof responsibilities

The minimal language-independent kernel is unchanged. It consumes the local
condition/preservation certificates; it knows neither pragmas nor matrices.

The Clight host owns concrete checks, private resources, public-state and exit
restoration, source progress, occurrence-specific placement and whole-program
installation. `compile_selected_tensor_literal_regions_correct` supplies the
whole-program endpoint for arbitrary data proposers. The native Cabs metadata
pass remains at the parser/elaborator boundary; the mechanized theorem starts
with Csyntax, rather than claiming a new verified Cabs transformation.

The domain owns source/model correspondence, sufficient conditions, schedule
validation and actual candidate execution. Two new endpoints establish that
successful checked scheduling and prepared codegen map a completed generated
Loop execution back to the source model and then to the source Loop:
`checked_memory_prepared_phase_correct` and
`checked_memory_prepared_loop_correct`. These are backward correspondence
theorems; they do not establish progress by themselves. The final existing
mapped-domain source/candidate factory supplies the forward execution and
progress required to install the generated candidate. The new bridge does not
replace that obligation with an assumed optimizer callback.

In the narrative's certificate chain, candidate validation supplies `C_opt`;
the existing tensor producer supplies source/model and entry obligations for
`C_derive`; checked condition lowering supplies `C_guard`; and the selected
Clight host supplies `C_host`. These describe logical boundaries rather than
four records a user must fill for each marked instance. A new source family or
language host still needs its corresponding producer/host proofs.

## Compatibility decisions

The frozen memory `POLIRS` export/scheduler hooks still refuse. This new route
passes the scheduler explicitly and uses compatible actual components:
`ExtractorCorrect`, the affine validator and `PrepareCodegen`. It does not
literally call the old `PolOpt.Opt_prepared`, whose frozen objects were compiled
against an earlier Prelude in this workspace. It also omits strengthening and
the checked tiling phase. Neither missing phase is reported as integrated.

Three OpenScop issues were resolved in the new transport. Access matrices must
compose `pi_access_transformation` to reach the domain's dimensions. Expanded
affine body expressions need compact printing for OSL's bounded string reader.
Sparse CompCert array identifiers are renumbered densely for Pluto's array-name
indexing. Returned bodies, accesses and array tables are never trusted by the
verified schedule importer.

Pluto's signed-int matrix reader cannot encode the `2147483648` bias of a
signed32 minimum-bound guard. The scheduling source is therefore the parametric
canonical rectangle without the host's machine-word profile guard. The final
certified factory applies that profile to both source and generated models;
the scheduler's word arithmetic supplies no proof. This is not a wider runtime
acceptance claim.

The external scheduler is built from the pinned archive SHA-256
`5d04579f13add5ba6838fd8a8e617eec63d46186a8756e2946abbf471e6e3eb0`.
The host uses LLVM/Clang 14. A PET API compatibility patch and an isolated
bundled-ISL link are required: LLVM 14 exports its own incompatible `isl_*`
symbols. Keep the whole-archive linker argument grouped so libtool cannot
reorder it. GLPK is not requested, and documentation is not built. The
fingerprint records the completed manual build; the helper contains a fresh
build recipe, but that recipe has not yet been replayed from a new empty tree.
This scheduler is untrusted and does not enlarge the semantic axiom boundary.

## Validation and remaining scope

The independent bridge audit queries two endpoints over 88 dependencies. It
adds no global axioms; each endpoint has at most twelve existing baseline
globals. The minimal kernel is closed and the frozen selected-compiler parent
report is validated before and after. Parent compiler assumptions remain its
existing 42-global set; this stage does not report two closed new endpoints.

The first native matrix uses six functions and twelve inputs in nine
configurations: 648 unmodified assembly calls and 288 separate generated-Clight
dispatch observations. It checks all 6,144 words, public counters, first-region
exits and context markers against an independent signed32 model and GCC source
execution. Cases include marked/unmarked duplicates, repeated marked regions,
static body refusal, runtime profile refusal, empty null-pointer execution,
goto/memory contexts, scheduler failure, truncated output and an invalid
scattering equality. The latter two exercise transport/import refusal.

The supplementary layout matrix uses the same frozen compiler and proof with
an additional untrusted affine phase. The column-order source receives a
generated nonidentity `(j,i,k)` traversal; the row-order source stays `(i,j,k)`.
It adds 144 unmodified assembly calls and 144 separate generated-Clight
dispatch observations. These are functional/semantic checks, not assembly path
probes or performance measurements. The two matrices therefore add 792 assembly
calls and 432 Clight observations through the connected path.

The supported integration slice is sequential three-axis literal-bound Horner
RMW with a compact sufficient numeric/address profile. Its scope does not
include arbitrary skewed schedules, general tiling, new loaded-bound model
extraction, arbitrary instruction bodies or universal assumption inference.
Next, connect the checked tiling transition and its actual generated-code
point/reindex/progress witness; preserve this affine path as a regression.
Then extend loaded-header/dynamic-layout modeling and measure guard work,
acceptance, code size and paired complete-call cost.

Reports are `build/polyhedral-pipeline/proof/report.json`,
`build/polyhedral-pipeline/pluto-build.json`,
`build/polyhedral-pipeline/native/report.json`, and
`build/polyhedral-layout/native/report.json`. Validate the stage with:

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/polyhedral_pipeline.mk validate
```

Bound report SHA-256 values:

| Report | SHA-256 |
| --- | --- |
| Bridge proof | `137ba84b5621dce408c16c6e652c1d0be3c4ae0e8d1ea2773b33a94686cd2048` |
| External scheduler build | `e367d9bdfe18b264537bddf746b1a2f828750bdbb02246bc26bff3d7a4c17743` |
| Pipeline native matrix | `aa9a92b956161499e538e9d417d0fe2aaa8317e0392620094a51612fcc6f462e` |
| Layout native matrix | `2dc0c2db9d8cd819427a585fa51b9f83022ee4364d6320e904beae9608954149` |
