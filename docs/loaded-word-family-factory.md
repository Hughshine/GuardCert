# Checked Loaded-Word Factory and Selected Compilation

The loaded-word family now has a data-only factory and selected Csem-to-Asm
correctness endpoints. A source proposer supplies AST description data; a tensor
proposer supplies a canonical model description; a scheduling/codegen proposer
supplies an actual affine or tiled Loop and witness data. The factory checks each
proposal before producing the local guarantee consumed by the existing Clight
host. Source users do not supply capture, frame, permission, condition or
execution proofs.

## Factory Inputs and Checks

`loaded_word_description` describes two loaded headers, a literal third axis,
a direct word-store leaf, its data pointer/index/value, profile caps and private
scan controls. It contains no semantic callback. `lwd_stable` computes the
protected scope and `lwd_rename` generates coordinate renaming. The internal
`loaded_word_static` and `loaded_word_site` records are checker outputs.

`check_loaded_word_static` checks exact leaf syntax, the signed-word expression
grammar, signed caps, nonnegative literal upper, frameability, cached source
scope, cache/helper freshness, distinct coordinates/controls, index scope and
stable input membership. The word grammar admits variable products; recognition
is not a mathematical no-wrap proof.

`check_loaded_word_site` binds the actual base original AST, verifies that every
used private name has a signed32 declaration in the supplied pool, calls
`check_tensor_region_description` on the generated canonical tensor syntax, and
checks that the Boolean result is private even to full-guard reads. The factory
removes capture/helper/scan names from the candidate pool, converts the remaining
typed resources to counter pairs, and calls `check_tensor_generated_region` on
the actual proposed/generated Loop. Invalid data yields no rewrite.

`check_loaded_word_generated_region_sound` derives the actual local
`projected_region_contract` from those algorithmic results and the frozen
loaded-word driver theorem. `checked_loaded_word_generated_regions_sound`
composes a checked table for repeated regions. The language host checks private
pool freshness, original source progress and selected placement, then installs
the table. These are compiler checks, not extra site-author proof arguments.

The base compiler endpoint is
`ClightSelectedLoadedWordGeneratedCompiler.compile_selected_loaded_word_generated_regions_correct`.
The proof is a backward simulation from Csem to Asm, conditional on that
compiler returning `OK`. It is parametric over the untrusted data proposers;
its correctness does not establish that a particular native proposer recognizes
or optimizes its intended input.

## Native Frontend Shape

The native C frontend introduces skip prefixes before nested resets and can
spell the root load as `header[0]`. `ClightLoadedWordFrontendFactory.v` reuses
`ncs_frontend_execution_equivalent` and `ncs_frontend_temps` to adapt these
actual shapes. It checks the complete proposed frontend AST before calling the
base factory. The selected frontend endpoint is
`ClightSelectedLoadedWordFrontendCompiler.compile_selected_loaded_word_frontend_regions_correct`.

The frontend adapter's target retains the equivalent base original AST as its
fallback. The existing language theorem proves exact terminating traces,
outcomes, memory and temporaries between this base source and the checked
frontend source. This adapter does not retain every administrative skip in the
frontend AST. The original source's progress and placement are still checked
by the host.

The real frontend also prefixes the leaf store with `skip`. The successor
`ClightLoadedWordPaddedFrontendFactory.v` checks this syntax and proves its
exact source-execution and temporary-footprint equivalence. It preserves the
previous supported frontend forms. Its compiler endpoint is
`ClightSelectedLoadedWordPaddedFrontendCompiler.compile_selected_loaded_word_padded_frontend_regions_correct`.

## Responsibility and Evidence

The minimal kernel is unchanged. The language library owns exact word
execution, source-licensed checks, conditional capture, frame transport,
frontend equivalence, private allocation, progress and installation. The domain
implementation binds source/model assumptions and actual generated candidates
to those services. The data factory makes those bindings checkable. No new
materialized kernel-rule package is added in this stage.

A dynamic-stride Horner RMW fixture uses the independent source expression
`a[((i*ld)+j)*5+k] += increment`, with two loaded bounds and a literal five.
The base factory recognizes its static site and canonical tensor package.
Both supported frontend shapes pass the actual source-progress checker.
Separate cases reject a wrong source AST, missing or wrongly typed private
allocation, a public cache, aliased controls, a changed leaf/index, a non-word
grammar and an unlicensed tensor dimension. These are static recognition cases;
they do not establish runtime full-guard acceptance or an installed native
candidate.

The frozen base-factory audit queries 26 endpoints over 554 dependencies:
21 endpoints are closed, and the compiler endpoints use the same existing
42-global set as the generated tensor compiler. The frozen frontend audit
queries eight endpoints over 606 dependencies, with two closed endpoints and
the same compiler baseline. The padded-leaf successor queries seven endpoints over 602 dependencies,
with one closed endpoint and the same 42-global compiler set. None adds a
global axiom; kernel assumptions remain empty. Their report hashes are:

- `build/tensor-loaded-word-factory/proof/report.json`:
  `1b32eb3c0e782599233c177f5ed7dbe4d15f6789c89adccc7197aa1ce291b5ab`
- `build/loaded-word-frontend/proof/report.json`:
  `3af393c4803e58b262b49cecf7d0d3bccfe85e3e9e7ed90e8c072637e6f189f8`

- `build/loaded-word-padded-frontend/proof/report.json`:
  `8414229ace7c0f96a30f69602b27fbbf61dc631aced1f63b0151efeaf7289e25`

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_tensor_loaded_word_factory.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_loaded_word_frontend.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_loaded_word_padded_frontend.py --validate
```

## Installed Same-C Pipeline

The succeeding v3 extraction uses the padded-leaf factory and an untrusted
native proposer. The same C input combines two loaded headers, a dynamic-stride
Horner RMW body and a literal third axis. It passes actual model extraction,
OpenScop export, Pluto scheduling and checked affine/tiling transitions,
PolCert prepared codegen, untrusted bound adaptation, the actual-candidate
checker, Clight lowering and selected Csem-to-Asm compilation.

Five configurations each execute six functions on 14 inputs: 420 unmodified
assembly calls. Every call checks all 6,144 array words, public counters,
first-region exits and continuation markers against a signed32 source model
and GCC. Row-major and column-major source orders both install real tiling
candidates. Independent instrumentation of the emitted Clight dump checks 168
calls' final candidate/fallback decisions; these are not assembly path counts.
Each installed configuration has five successful pipeline receipts. The mixed
function installs only its marked occurrence; the two-site function installs
both. The unmarked function and unsupported `alpha+1` value retain original
code. Unannotated, disabled and failed-scheduler configurations also preserve
original execution.

An alias input places both headers inside the output array; source stores
change them. Both installed configurations refuse the candidate and match the
original's changing-bound execution. Profile, nonzero-start and layout cases
also refuse. An empty-root case uses a pointer to one scalar as the header,
with its indexed child outside that object's allocation and an unavailable data
pointer. The full program terminates with the original counters and output;
the driver skips that child and later data checks.

The native report is `build/loaded-word-frontend-v3/native/report.json`, SHA256
`0044a0472ea97c5dcadc6551ab88f803ea650583c8f70b59c5d5b6d4b99b575e`. The proved endpoint begins at Csyntax. The native Cabs marker
pass and external proposer/scheduler remain unverified components whose output
is checked at the stated boundaries. Raw codegen and adapted candidate evidence
remain distinct; no raw-to-adapted equivalence theorem is claimed.

The first build and failed installation check remain under
`build/loaded-word-frontend/`. A v2 probe established that the real leaf was
`Ssequence Sskip store`; the v3 language adapter and checker close that
administrative-shape gap. Historical proof reports remain frozen, including
their pre-extraction flags. The newer native report supplies executable evidence
without rewriting those earlier checkpoints.

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/build_loaded_word_frontend_compiler_v3.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_loaded_word_pipeline_v3.py --validate
```

The next work is to improve and measure conditions on this same installed
family, quantify acceptance, guard work, code size and paired whole-execution
cost, and extend the source/domain capabilities required by the full objective.
The current cases are integration evidence, not representative benchmark
speedup or a comparison of author effort. The complete goal remains active.
