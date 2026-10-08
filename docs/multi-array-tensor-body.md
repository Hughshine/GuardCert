# Multi-array Horner bodies: source decoding and candidate execution

This checkpoint extends the runtime-Horner tensor model to a checked sequence
of assignments through several actual pointer temporaries. It is a library and
source/candidate prototype checkpoint. The selected loaded-word C-to-Asm
compiler still recognizes its previous single RMW body.

## Narrative Boundary

The remote narrative was checked again on 2026-10-07. The advertised
`topdown/research-positioning` head is
`12419c1e1e3da450bf378742a2fb4e204e51e060`; `paper-narrative.md` and
`context-lifting.md` match main. Their requirements govern this extension:

- The semantic kernel composes local certificates. It does not recognize
  assignments, infer alias conditions, or install Clight regions.
- The Clight library proves actual reads/stores, machine arithmetic, private
  frames, guarded control, and supported installation laws.
- The domain implementation checks source data, derives modeling conditions,
  checks the actual candidate, and supplies the chosen region guarantee.
- The site checker must produce scope, freshness, progress, and placement
  evidence before the language host installs a replacement.

The four certificate links in the narrative describe logical obligations, not
four simulation callbacks for a source user to fill. The open discussion of a
host contract algebra does not justify changing the kernel at this checkpoint.

## Source and Data Interface

The concrete prototype body is:

```c
q = ((i * ld) + j) * 5 + k; /* q denotes the expression, not a new source temp */
a[q] = b[q] + alpha;
b[q] = a[q] + alpha;
```

The actual checked Clight assignments contain the Horner expression directly.
The second assignment reads the memory produced by the first. Treating both
reads as observations of the entry memory would erase this flow dependence.

`GuardMemoryMultiTensorSource.v` pairs each checked tensor access with its
actual pointer identifier. Logical array identifiers are those pointer
identifiers. Each operation describes its write, its list of reads, and a
`value_expression`. The existing value language supports constants, parameters,
loaded values, and word addition/subtraction/multiplication. Access coordinates
use the existing affine-coordinate descriptor and exact Horner syntax checker.

`check_multi_tensor_source_operation` checks the actual assignment AST against
those data. Its successful dependent result contains the exact-source and
value-expression facts. A caller supplies description data, not an execution
proof. `check_multi_tensor_source_statement` retains this result together with
the source statement.

`GuardMemoryMultiTensorSequence.v` supports a heterogeneous list of these
checked operations. `multi_tensor_body_source_decode` consumes an actual
silent, normally completing body execution and produces the corresponding
`memory_nary_sequence_point`, with the same final memory and unchanged
temporaries. Its induction passes the intermediate memory to the next
operation. It also supplies the body's normal/quiet/temp-write facts from its
flattened list.

`ClightMultiTensorExample.v` is a small data factory for the two assignments
above. It checks both statements and obtains their instructions from the
checker results. Its body-execution theorem consumes the general decoder.
Recognition examples cover changed pointers, changed RHS, a missing statement,
and administrative `skip` nodes. Recognition of this fixed family is separate
from the dependence check on a proposed target.

Source decoding still needs an available logical access at each actual point,
a valid tensor layout, and the numeric parameter/dimension views. The new
factory has not yet generated a complete runtime condition or a nested loaded
source certificate that establishes those premises. The statement-level decoder
does not imply that the enclosing loops have been installed.

The same sequence exposes a condition-synthesis obligation beyond dependence
checking. `a[q]` may be uninitialized at entry: the original first assignment
initializes it before the second reads it. A read-only guard that copies the
second source RHS and evaluates it at entry can therefore introduce an undefined
word computation. Permission transport through stores licenses address probes;
it does not transport loaded values or their definedness to an earlier memory.
An address-only separation check avoids that particular data read. A condition
that uses the second operation's value must instead justify forwarding the first
store's result, or derive another source-licensed value expression. Such
load/store and frame laws belong to the language library; matching the body's
def/use structure and supplying its sufficient conditions belong to the domain
producer. This is not a reason to change the semantic kernel.

## Actual Pointer Views and Aliasing

`GuardMemoryMultiTensorBackend.v` defines the raw location view from the actual
entry pointer bindings. A cell resolves through its own pointer temporary and
the existing runtime tensor index. Several arrays may resolve to the same
allocation or to overlapping physical addresses. The source decoder and the
forward Clight lowerer preserve this possibility; neither assumes that pointer
names imply separation.

The current backend uses one shared list of runtime dimension sources for the
arrays. Different affine accesses within that layout are supported. Different
per-array layouts are a future extension, not an existing property of this
interface. The raw location view also sees other pointer bindings in the entry
environment. It is therefore inappropriate to demand that this entire view be
nonaliasing: an unrelated header pointer could overlap an array even when it is
not part of the modeled body footprint.

`ClightMultiTensorCandidates.v` instead computes the source model's actual event
footprint at its parameters. `multi_tensor_separated_source` requires physical
disjointness only between distinct logical cells in this footprint. The bridge
restricts the location view to these cells, invokes the existing candidate
certificate, and then unrestricts the validated candidate execution. The final
Clight lowerer uses the raw view, retaining the original memory and pointer
bindings.

This separation is a sufficient semantic modeling condition. Source completion
does not establish it. It is not an emitted runtime query, and no new executable
cross-array alias encoder is provided by this checkpoint. A future source/guard
factory must derive and safely encode it before installation. The current
certificate can conservatively refuse aliasing that a more specialized
transformation could tolerate; minimal alias conditions are not claimed.

## Candidate Interface and Guarantee

`check_multi_tensor_generated` takes checked source instructions, dimensions,
pointer identifiers, the canonical parameter layout, live temporaries, a private
counter pool, and a `tensor_generated_candidate`. The latter contains the
actual Loop AST plus mapped or tiled witness data. The function checks the
actual lowering and the existing source/candidate domain certificate. Unknown
pointer identifiers and unsafe scratch allocation refuse lowering.

`check_multi_tensor_generated_execution` supplies actual Clight target
execution with the same final memory when:

1. The generated candidate check succeeds.
2. The existing numeric/layout facts and dimension observation hold at the
   candidate entry.
3. The source footprint is separated in that same entry view.
4. The actual source Loop model executes from that entry.

The result preserves the canonical layout, pointer/dimension capability, and
declared live temporaries. It does not restore public source iterators by
itself, establish a local guarded rule, or install that rule in a function.
Those connections remain language/domain/site obligations.

## Proof Evidence

The fresh audit is `build/multi-tensor/proof/report.json`, SHA-256
`b69256117f29d5f1cff0c604079519a0e263d29b0563482321891677146ceac3`.
Five modules compile and 30 queried endpoints are checked independently:
17 are closed; the largest assumption set has 14 globals, all within the
existing 42-global compiler baseline. The audit binds the source/object inputs
and direct dependencies, and validates the historical compiler closure. No
new global axiom or kernel change is introduced.

Successful objects remain frozen. The audit queries those objects rather than
rebuilding them. Failed development logs remain under
`build/multi-tensor-work/`; they do not count as successful evidence.

```sh
# After the historical loaded-word compiler prerequisites are available:
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/compile_multi_tensor_sources.py
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_multi_tensor.py
```

## Extracted Prototype and Actual Pipeline

The extracted prototype passes eleven cases. Five accept and six refuse.
The eight candidate-checker cases all finish without an alarm. Recognition
rejects a changed pointer or missing assignment. The complete domain checker
rejects reversing the two stores or omitting the second store. Lowering rejects
an unavailable pointer identifier and a pointer/scratch collision.

For three pipeline cases, the caller supplies the checked source and tile sizes
`[2,3,2]`, `[1,3,2]`, or `[1,1,1]`. Actual OpenScop export, Pluto, affine import
and validation, and tiling validation run on the complete two-statement model.
`GuardPartitionedMultiTensorCandidate.ml` then calls the real prepared code
generator on each statement of that checked transformed model. It proposes
sequential composition of those generated loops. The existing coordinate
completion and bound adapter process this actual output, and
`check_multi_tensor_generated` validates the complete composed candidate
against the original two-instruction source before lowering it.

The composition proposes statement distribution; it does not assume that
distribution is legal. The final check supplies the whole-target certificate.
The per-statement codegen results are not a proved execution-equivalence
certificate for their composition. The nonunit, partial-unit, and all-unit
targets contain 137, 129, and 65 Clight statement nodes respectively; these are
syntax counts, not runtime work or evidence that those statements executed.

The report records actual source, scheduled/transformed model, individual raw
generated statements, composed raw/completed/adapted Loop outputs, phase
receipts, native sources, extracted executable, and checker results. It is
`build/multi-tensor/extracted-partitioned/report.json`, SHA-256
`52f8db57c062393bfbee3ef33f88f77a436bd516a16d58966ffe6ee745b64f0e`. The generated Clight statements are not executed
by this harness. There is no new C/assembly matrix, runtime alias encoder,
multi-array compiler entrypoint, guard installation, or profitability result.

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/build_multi_tensor.py
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/build_multi_tensor.py --validate
```

The build uses a fresh directory. Existing reports select validation. Use
`--work` with another directory to reproduce without overwriting a checkpoint.

Joint codegen was also attempted and its long runs were stopped deliberately.
A stage probe accepted affine validation and completed tiling validation in
about 6.3 seconds with 19,072 successful oracle queries and no exhausted query;
codegen remained running. Short CPU samples exposed unused diagnostic string
construction and GC. Inlining the transparent Rocq identity definitions
`Debugging.trace` and `Debugging.failwith` removed that message construction,
but joint generation was still slow. This is why the successor tests
per-statement generation plus a complete final check.

The stopped runs and samples are bound by
`build/multi-tensor/diagnostics-v1/report.json`, SHA-256
`d6af5650a1bbcce0fd818ac0f15eb5a4894c99f3cadc611ba251799af470dff2`.
They establish neither joint-codegen success nor failure. The diagnostic timing
and sampling are not a compiler benchmark or a measured speedup. All proof
objects and the previous selected compiler remain unchanged.

## Next Installation Gates

The difficult next steps are concrete state connections:

1. Decode the complete nested source with this checked body sequence. Produce
   point availability and numeric facts from the supported source description
   and accepted condition, rather than adding a source/model simulation field.
   Relate each point's actual temporary environment to the fixed entry location
   view on the checked body's array identifiers. Counter resets can change
   unrelated entries in the raw view; whole-view equality must not become an
   extra assumption. Pointer-frame and footprint transport should localize this
   obligation to the actual accesses.
2. License checks for every actual read/write from the original source prefix.
   When a header aliases either array, preserve each captured word before
   advancing to the next source test. The second operation uses the first
   operation's output memory. A check cannot assume the stability or separation
  that it is trying to establish.
   The existing single-RMW `alpha==0` preparation cannot be reused just by
   testing the same scalar: here `alpha==0` still replaces `a[q]` with the old
   `b[q]`, so an observation of `a[q]` can change. A value-preservation condition
   for this sequence needs a new derivation from its actual reads/writes.
3. Produce a safe executable sufficient cross-array alias condition over the
   active source footprint. The old flat multi-pointer guard library supplies
   proof patterns, but its flat index encoder is not a runtime-Horner encoder.
4. Transport source/model and condition facts to the actual complete guard
   exit; lower the actual generated candidate; restore public counters; produce
   a local region contract from checked data.
5. Consume the existing selected host and progress/placement checks, prove a
   new Csem-to-Asm endpoint, and run the same marked multi-array C programs.
   Cover disjoint arrays, same-allocation disjoint ranges, exact and shifted
   aliases, aliasing headers, empty paths, two sites, and visible continuations.

Real cross-iteration recurrences and general affine domains remain subsequent
coverage gates. A reversed two-store target tests intra-point dependence; it
does not constitute a recurrence example. Guard cost, acceptance, profitability,
and comparative author work remain separate evaluations.
