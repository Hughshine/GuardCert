# Unit tile coordinates and loaded positive offsets

This checkpoint extends the untrusted candidate producer and exercises another
source shape through the existing loaded-word compiler. It follows the
[narrative responsibility boundary](topdown/paper-narrative.md): the producer
proposes code and data, the domain factory validates the actual candidate, and
the language host installs the certified region. The generic kernel is unchanged.

## The codegen boundary

The preceding [tight-candidate checkpoint](tight-loaded-word-candidates.md)
recorded a real refusal. Unit tile sizes made prepared codegen eliminate
coordinates, while the proposed tiling witness still described three tile
links and six nested coordinates. Successful scheduling and codegen did not
establish final installation. That failed checkpoint and its outputs remain
immutable.

The new `GuardCompletedPreparedTensorCandidate.ml` retains the actual raw
codegen output and proposes a supported representation for the final checker.
For the current three-axis rectangular tensor family, the raw prefix contains
three tile coordinates; a unit axis identifies its point coordinate with that
prefix coordinate. Only nonunit axes retain separate point loops.

| Unit axes | Raw depth | Proposed depth | Final candidate interface |
| --- | ---: | ---: | --- |
| None | 6 | 6 | `TensorGeneratedTiled` |
| One | 5 | 6 | `TensorGeneratedTiled` |
| Two | 4 | 6 | `TensorGeneratedTiled` |
| All three | 3 | 3 | `TensorGeneratedMapped` |

For partial unit tiles, the producer inserts a singleton point loop
`[tile_axis,tile_axis+1)` for each missing axis. It lifts de Bruijn references
in expressions, tests and nested binders, then proposes the canonical three
point operands in each instruction. A structural check requires the expected
raw depth and point-variable positions at every instruction. The other
operands are retained with the appropriate lifting.

These structural checks are safeguards for the producer, not semantic
certificates. Singleton completion, operand rebinding and affine bound
adaptation remain untrusted. The final actual source/candidate checker must
accept the completed and adapted Loop with its witness before installation.
It checks the candidate against the conditional source model rather than
assuming equivalence to the raw codegen output.

All-unit tiling retains the real three-loop codegen result and proposes its
affine reindex data to the existing mapped checker. It does not fabricate
three redundant point loops just to meet the tiling bridge's depth convention.
The nonunit case uses the existing six-loop path unchanged.

Each successful phase retains distinct artifacts:

- `raw-generated.loop`: actual prepared codegen output;
- `completed.loop`: proposed coordinate completion;
- `generated.loop`: completed Loop after proposed affine bound adaptation;
- `coordinate-completion.txt`: unit mask, completion choice and candidate kind;
- phase/witness files and, in the diagnostic probe, the actual checker result.

The phase receipt still says `actual-candidate-check=pending`. Installation is
established separately by the final factory and the emitted Clight dispatch.
No raw-to-completed or raw-to-adapted equivalence theorem is claimed.

The original four-case probe confirms depths 5/5/5/3 and no installation with
the old producer. The successor probe checks all eight unit-axis combinations:
each actual domain checker returns `valid=true alarm-free=true`, and each
single-region program contains one installed dispatch. These programs do not
call the region at runtime; the probe alone is not native execution evidence.

## Positive offsets as an arithmetic condition service

The same source discovery and data factory already admit literal signed word
offsets in the two loaded bounds. The new source matrix uses

```c
for (; i < *h + 1; i++)
  for (j = 0; j < h[1] + 1; j++)
    for (k = 0; k < 5; k++)
      a[((i * ld) + j) * 5 + k] += alpha;
```

The column layout uses `((j * ld) + i)` instead. Both remain one-tensor,
single-RMW examples; they do not cover the full OLO Figure 2/BT body or general
loaded affine domains.

The source evaluates `Int.add` first. The profile constrains its actual cached
signed result, not an assumed mathematical `raw+1`. In particular raw zero
now denotes one iteration, raw `INT_MAX` wraps to `INT_MIN`, and raw `-1`
denotes an empty bound. The harness supplies a null output pointer only when
the wrapped root is inactive, rather than when the raw header is zero.
Conditional capture and scalar-read licensing remain those of the existing
source-prefix proof; this arithmetic service does not license a new load.

`CompCertPositiveOffsetFacts.v` proves the following reusable rule for signed
32-bit words:

```
0 <= signed(delta)
0 <= signed(add(raw,delta))
-------------------------------------------
signed(add(raw,delta)) = signed(raw)+signed(delta)
min_signed <= signed(raw)+signed(delta) <= max_signed
```

A nonnegative offset cannot underflow. If its signed sum overflowed above
`max_signed`, the word result would be negative; a nonnegative result rules
that out. The module also defines `positive_offset_profile` and proves its
Boolean acceptance implies the exact mathematical sum, positive cap and
signed range. It checks concrete raw-zero acceptance and wrapped-maximum
refusal. It does not synthesize conditions for arbitrary expressions, negative
offsets or products.

`ClightPositiveOffsetHeaders.v` consumes existing loaded/indexed capture
receipts and the actual cached profile. Its two header services retain the
actual pointer and `Mem.loadv` witness while deriving the mathematical sum and
no-overflow range. Its nested service consumes the actual
`ncs_observation_receipt` produced by the driver after both conditional reads.
No caller-supplied source/model simulation is introduced.

The five integer endpoints are closed. The three Clight receipt endpoints
inherit four existing globals, all within the unchanged 42-global compiler
baseline; there is no new axiom. These are additional presumption-interpretation
services, not a new runtime check or compiler theorem. The installed family
already models arbitrary literal word offsets correctly. The new Boolean
service has a logical soundness proof; a new Clight expression encoder for
that Boolean is not claimed. Existing source capture/profile execution and
safe fallback remain the installed proof path.

## What a user provides

For this supported family, the source user supplies a marked C region, layout
and phase/tile options. Discovery proposes the exact source descriptor; the
static checker produces AST, scope and private-resource evidence. The user
does not provide a per-site semantic callback or prove that raw bounds are
nonnegative.

An optimizer author can supply schedules, codegen output, tile witnesses or
coordinate adaptations as untrusted proposals. The existing checker must
validate the actual proposed target. Admitting another source family requires
its source/model and safe-condition proofs or suitable verified checkers.

The language library owns machine-word and capture laws, private-state
transport, source-licensed checking, control/progress, site installation and
the CompCert backend connection. The new arithmetic lemma belongs here;
the rectangular unit-coordinate proposal belongs to the domain producer.
The generic framework only composes the certificates supplied by these layers.

## Evidence and reproduction

The new compiler is `build/loaded-word-completed/compiler/ccomp`, built by
`scripts/build_completed_loaded_word_compiler.py`. It uses the same selected
entrypoint:

```
ClightSelectedZeroLoadedWordFrontendCompiler.
  compile_selected_zero_loaded_word_frontend_regions
```

The compiler theorem already quantifies over the untrusted producer. Its
frozen proof input remains `build/loaded-word-zero/proof-v2/report.json`.
The compiler entry, source factory, language host and generic kernel have not
been modified for coordinate completion or literal `+1` offsets.

The original and completed probes are respectively
`build/unit-tile-codegen-probe/report.json` and
`build/completed-unit-codegen-probe/report.json`. The former SHA-256 is
`acb5a9b6ba8a1044bed5a06e6881319e3e1c9dd6e56b7809edb64cad24d24717`;
the latter is
`17d7132f06e5a815ba63db6408e9c6ef8fa2a5ad9d2de20a3c25f74face47a1f`.

The positive-offset proof report is
`build/positive-offset-headers/proof/report.json`, SHA-256
`641c392554bd4d58d5ceddf1cb57a89f8bc7054e3b8d82d06517a6052adeb0c3`.
It audits eight endpoints in two new modules, with five closed and three using
four inherited globals. It binds the new sources/objects, assumption queries,
helper and unchanged historical compiler proof inputs. Its Boolean soundness
and receipt corollaries are distinct from installed compiler evidence.

The completed compiler SHA-256 is
`7f618578ccc9774d34a35cfa8cfad755fac85e75b032f08775017d89b3d991a5`;
its build stamp SHA-256 is
`84618c92afff5369c2b898ff783fedadbdb62beab01baf29525fdf2ba559643b`.

The complete unit-tile matrix passes 21 fresh configurations with 112 calls
each: 2,352 unmodified CompCert Asm calls and 1,792 separate Clight dispatch
calls. Sixteen installed configurations cover row and column layouts times all
eight masks over unit tile sizes. Each installed row configuration observes 45
accepted and 49 refused marked occurrences; each column configuration observes
55 accepted and 39 refused. Each has 25 zero-preparation entries. The acceptance
difference follows the layout-specific minor-extent/stride condition.
Five negative configurations exercise unannotated source, disabled policy and
failed/truncated/invalid scheduler output. The matrix checks full arrays,
public/first counters and context markers against the source word model and
GCC reference, including stable/changing header aliases, unavailable reads on
inactive paths, repeated rewrites and goto/memory contexts. Each installed
configuration retains five real phase invocations and verifies its exact raw,
completed and adapted depths, tile sizes, unit mask, witnesses and installed
Clight sites. The unsupported marked `alpha+1` body remains uninstalled.

Its report is `build/loaded-word-completed/native/report.json`, SHA-256
`2663b379eec470b7198b179859e29cf05ccefc84bed880819eada783218d6e35`.
This is new complete-program execution evidence for the reused compiler
theorem, not merely the earlier single-region installation probe.

The positive-offset native matrix has passed: nine configurations execute
135 calls each, giving 1,215 unmodified CompCert Asm calls and 540 separate
Clight dispatch calls. The four installed configurations are row `[2,3,2]`,
row `[1,3,2]`, column `[2,1,2]` and column `[1,1,1]`. Each installed
configuration observes 50 accepted and 64 refused marked occurrences, with
25 zero-preparation entries. Unmarked/unsupported/skipped occurrences report
no dispatch. Five negative configurations cover unannotated source, disabled
policy, scheduler failure, truncated output and invalid scattering.

All 6,144 array words, first/final public counters and context markers agree
with both the word-level source model and the `-O0 -fwrapv` GCC reference.
The source model reevaluates the actual wrapped loaded bounds after every
aliasing store, including between repeated regions. Cases include raw zero
with a nonempty effective root, `INT_MAX`/`INT_MIN`, empty child counts, null
output and unavailable child on inactive roots, 32-by-32 accepted domains,
over-cap refusal, changing-header nonzero aliases and two stable zero aliases.
Marked/unmarked twins, repeated rewrites, goto and memory contexts are retained.
The dispatch counts come from separate Clight derivatives, not instrumented Asm.

The report is `build/loaded-word-positive-offset/native/report.json`, SHA-256
`8c9db39f451feb8e6d8e89f10b20c30022a62a32ec8484555ba2e2455bcfc8e6`.
It binds the reused compiler/proof inputs, new fixtures/model/helper and all
source, phase, witness, Loop, Clight, assembly and execution artifacts.
It adds no proof module or compiler global; the two separately audited
presumption-service modules above are ancillary library results.

The helpers validate an existing checkpoint rather than overwrite it:

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/probe_unit_tile_codegen.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/probe_completed_unit_codegen.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_positive_offset_headers.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_completed_loaded_word_pipeline.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_positive_offset_pipeline.py --validate
```

Build or run a new checkpoint only when its directory is absent. Successful
sources, helpers, compiler and proof objects, dumps and reports are frozen.
Historical failures and cost evidence remain inputs, not files to regenerate.

## Remaining work

Coordinate completion and positive offsets do not establish a profitability
result. The previous fixed-size tight-candidate timing remains historical;
its ratios cannot be assigned to these unit variants or the new bound shapes.
The nonzero path still scans points to establish header stability.

The difficult next domain boundary is a genuinely dependent, multi-operation
and multi-array body in this same loaded-bound/runtime-Horner pipeline.
Existing multi-pointer and affine source services live on other verified
paths; their presence does not establish their composition with this factory,
real three-axis codegen and selected Csem-to-Asm entry. That composition must
produce actual source operations, read/write matrices, cross-iteration
dependence checks, safe conditions and public exits from source data.

A concrete next acceptance pair separates two obligations:

1. A two-statement body, `a[q]=b[q]+alpha; b[q]=a[q]+beta`, with the same
   loaded bounds and runtime Horner layout. Separate buffers can permit
   reordering independent points; overlapping shifted buffers require refusal
   or a suitable dependence certificate. The factory must check both source
   statements and produce both read/write operations. The prefix proof must
   license each actual pointer access and protect the captured headers across
   the complete statement sequence. Existing multi-pointer value decoding can
   be reused, but its buffer model and conditions must be connected to the
   tensor layout and the actual guard entry.
2. A genuine same-array recurrence with component range `1 <= k < 5`,
   `a[q]=a[q-1]+alpha`. Exchanging independent row/column axes may be legal;
   reversing the component dependence is not. This needs nonzero affine lower
   bounds and a proved neighbor-access domain, not merely a second pointer.
   Real scheduler/codegen outputs must be checked for both legal and illegal
   schedules, then installed with the corresponding public exits.

Neither pair is supported by the current selected loaded-word compiler.
Each is an implementation gate, not a request for callers to supply a missing
simulation: checked source data must produce the model, condition, candidate
and site evidence. A partial multi-pointer theorem or a direct Loop fixture
does not close either end-to-end gate.

Compact nonzero conditions need source-licensed physical observations and
state transport. Pointer subtraction or ordering across arbitrary CompCert
blocks is not automatically a safe alias check. General affine domains,
delinearization, full BT/OLO coverage, representative profitable workloads and
comparative author effort remain open. The full project goal stays active.
