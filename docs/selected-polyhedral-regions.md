# Explicit SCoP Selection and Occurrence-Sensitive Installation

This stage implements the selection part of narrative `12419c1`. A native
frontend preserves paired `#pragma scop` / `#pragma endscop` requests through
normalization, and a new proved Clight host restricts both discovery and
installation to those regions. The existing literal-bound tensor checker,
condition producer, candidate policies and backend are reused. Real external
scheduling and prepared code generation remain the next integration task.

## User interface

Mark the source span to offer to this loop pass:

```c
#pragma scop
for (; i < n; ++i)
  for (j = 0; j < columns; ++j)
    for (k = 0; k < 5; ++k)
      a[((i * ld) + j) * 5 + k] += alpha;
#pragma endscop
```

The marker requests an attempt. It establishes no safety, SCoP validity,
no-wrap, alias, stability or progress property. The checked factory still
validates the actual normalized AST, source description, resources, condition
and candidate certificate. Unsupported rewrites preserve the original region;
a false runtime guard executes its original source AST.

Build and verify the isolated selected compiler with the pinned toolchain:

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/selected_regions.mk compiler
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/selected_regions.mk native
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/selected_regions.mk frontend
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/selected_regions.mk validate
```

Its driver calls
`ClightSelectedTensorLiteralCompiler.compile_selected_tensor_literal_regions`.
Default selection in this entry is marker-only; an input without markers is
not offered to this loop pass. Frozen earlier compiler routes retain their
historical discovery behavior for regression evidence. This stage is not a
change to those binaries or their reports.

Current candidate modes are the inherited `GUARDCERT_TENSOR_MODE` policies:
`identity`, `interchange`, and `tile-2-3`, plus disabled and invalid regression
proposals. These still construct Loop candidates directly. They exercise the
selection and installation path, and do not count as a scheduler/codegen result.

## Parser metadata and its boundary

`prototype/annotated-polyhedral/native/GuardScopFrontend.ml` runs on the actual
Cabs parser output before elaboration would discard local pragmas. It pairs
markers within one block and wraps a supported span in a fresh ordinary label.
The manifest records opening/closing source locations and statement count.
Freshness avoids all existing label and goto names in the translation unit.
Selection uses exactly the manifest's interned labels, never a name prefix.
Labels survive elaboration, Csyntax, SimplExpr and SimplLocals.

Declaration-free spans may contain multiple statements. Declarations inside
existing nested blocks keep their scope. Declarations directly in the selected
span conservatively refuse selection: adding a new block around them could
shorten their scope. Unmatched, nested, cross-block and empty marker structures
also refuse selection for their whole function. The original function is then
returned unchanged to the usual elaborator; another well-marked function can
still be selected. Properly paired regions in one function remain separate
selection boundaries, and unsupported rewrite syntax at one does not assert
validity of the others.

This is native frontend metadata handling, not a mechanized Cabs-to-Cabs
preservation theorem. As with CompCert's parser/elaborator boundary, the
whole-program endpoint starts at the resulting Csyntax program. The frontend
tests establish actual parsing, retained labels, conservative refusal and
ordinary execution for the declared cases. They do not replace that semantic
boundary or supply an optimization premise.

## Why occurrence identity matters

The old table maps source ASTs to certified replacements. Filtering its inputs
would not by itself restrict installation: an equal AST at another site would
match the same table. The new `selected_transform_statement` therefore carries
an active selection bit through the tree. It becomes active only under an
explicit chosen label; unmarked siblings remain inactive even when their ASTs
are identical. Label boundaries themselves remain in the source and target.

`unselected_subtrees_unchanged` proves identity on any subtree with no chosen
label when entered inactive, independently of the selector. Five closed syntax
fixtures cover identical marked/unmarked occurrences, two marked occurrences,
an unlisted label, restricted discovery and an empty/refused table. These
fixtures do not replace the host's semantic premises.

`ClightSelectedRegionProof.SelectedRegionProof.transform_program_correct2`
proves forward simulation for the selected traversal when the selector supplies
the existing projected-region contract and the source progress checker is
sound. It retains temp scope, fresh private resources, memory equivalence,
control/label matching and open surrounding execution. Its structural/memory
simulation follows the frozen `ClightPrivateRegionProof` in a separate module;
that source and its objects are unchanged. This introduces a language service,
not a generic kernel capability or an optimizer-specific semantic callback.
Factoring the shared simulation remains a possible host-library improvement;
this stage does not claim reduced implementation proof size.

`apply_selected_expression_region_table_correct` consumes the existing table
certificates and source progress law. The new compiler theorem
`compile_selected_tensor_literal_regions_correct` composes this host with
SimplExpr, SimplLocals and the CompCert backend, obtaining a Csem-to-Asm
backward simulation for a successful compiler result. The marker list can be
arbitrary: semantic correctness continues to depend on checked ASTs and region
contracts, rather than on annotation provenance.

## Evidence and scope

The independent audit queries 13 endpoints over 438 dependencies. Six endpoints
are closed; the compiler has the same 42-global assumption set as the existing
literal tensor compiler. There are no added globals and the minimal kernel
remains closed. The frozen parent report is validated before and after.

Proof report:
`build/selected-polyhedral-region/proof/report.json`, SHA-256
`ac8d247c270efedb494927958bcec77f6c7051886049dca9acf9abd6b9c18408`.

The extracted compiler runs six C functions and twelve inputs across eight
policies plus an unannotated interchange run: 648 unmodified assembly calls.
Every call compares all 6,144 array words, public counters, first-region exits
and context markers against an independent signed32 source model and GCC
reference. Cases include a marked loop beside its identical unmarked loop, two
marked sites, an unmarked function with a misleading label prefix, static
rewrite refusal, runtime guard refusal, null-pointer empty execution and a
goto/memory context. Three accepted policies add 216 separate observations of
the generated Clight dispatch via GCC; those are not assembly path probes.

Native report:
`build/selected-polyhedral-region/native/report.json`, SHA-256
`d7289b763eaa6057ae83e17b8b63916ce4b04b46acea294d5662740d9f49ffd0`.

Fourteen additional frontend cases check paired and malformed markers,
declaration escape, nested-block declarations, multiple statements, name
collision, unrelated pragmas, preprocessor exclusion, `_Pragma` expansion and
independent functions. Actual labels are checked in all three AST dumps and
each assembly execution matches the reference result.

Frontend report:
`build/selected-polyhedral-region/frontend/report.json`, SHA-256
`617ffaf3ff080069021e93daaae96393ff2b482b39031d7ac20994ef712ffe14`.

There is no new performance experiment or source-only fresh rebuild. The
current optimizer family remains the existing rectangular, temporary-bound
three-axis tensor RMW with a literal innermost bound. Loaded-bound/dynamic-layout
composition and broader affine/domain families remain unfinished.

## Next: actual polyhedral optimization

Keep this selected host while replacing the direct candidate policy with the
real polyhedral pipeline. One additional source gap was confirmed during this
stage: `GuardMemoryInstr.to_openscop` returns `None`, in addition to the memory
IR's disconnected scheduler/phase export hooks. Simply calling the prepared
optimizer with the current instance cannot produce an external scheduling input.

Provide a compatible OpenScop exporter, connect the external phase runner and
verified phase import/validation, and obtain the candidate from prepared code
generation. Retain source model, scheduled/transformed model, witness/check
results and generated Loop. Check the generated Loop's supported lowering,
progress, parameters and actual guard-exit entry relation before installation.
The existing source guard, fallback, public exits and host should be reused
where those contracts still apply. Run the connected candidate on marked C and
retain its whole-program endpoint; the main polyhedral integration milestone
and the full goal remain open until this chain is established.
