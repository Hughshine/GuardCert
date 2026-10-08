# Zero-RMW preparation in the loaded-word compiler

This successor installs an effect-based condition in the same loaded-header,
runtime-Horner source family as the earlier pipeline. The minimal semantic
kernel is unchanged. A new source factory, selected compiler proof and extracted
compiler connect the condition to the actual generated candidate.

For the supported leaf `a[q] = a[q] + alpha`, `alpha == 0` preserves every
previously defined `Mint32` observation. This includes a loaded loop header
that aliases an output cell. The two header words may have different values.
Observation preservation alone makes no claim about arbitrary bytes or other
chunks. The derived source/cached execution theorem and the final generated
region contract do preserve the original final memory.

## Runtime path and read permission

The installed preparation has this order:

```text
if the original row starts at zero:
    capture the root header
    capture the child header only if the root is active
    if both captured counts pass their positive profile:
        if alpha == 0:
            initialize the literal helper and accept preparation
        else:
            initialize the helper and run the existing complete word scan
    else refuse
else refuse
if preparation accepted: evaluate the complete numeric/layout condition
if the complete condition accepted: execute the checked generated candidate
else: execute the equivalent original source
```

A successful original execution through a positive root, positive child and
positive literal component reaches an actual first RMW before memory changes.
Its signed addition establishes a defined integer value for `alpha`. That
source fact licenses the equality test. The proof does not assume that the
future cached loop is executable in order to license this read. Empty or
refused paths bypass it.

On the zero path, the checked body preserves actual header snapshots. The
existing nested-expression transport then produces the exact cached-source
execution. Helper and flag initialization preserve its entire temporary
footprint. Literal-test preparation produces canonical execution at the actual
preparation exit. The complete numeric/layout condition and generated candidate
checker consume that execution at the actual full-check exit.

The nonzero path uses the historical scan theorem. Header capture and the scan
are each emitted once. Refusal preserves the entire original temporary
footprint; this licenses execution of the original fallback after private
preparation writes.

## Interface and ownership

| Owner | Service or evidence |
|---|---|
| Framework | Existing condition/certificate composition; no new memory or overflow semantics |
| Clight library | Scalar read license, word observation effect, actual capture/frames, structured execution transport, preparation-to-complete-check adapter, selected host installation |
| Loaded-loop domain | Positive first-point extraction, actual header receipts, original/cached/canonical correspondence, source shape and canonical tensor model |
| Optimizer implementation | Untrusted source description plus scalar identifier, canonical-model proposal and generated schedule candidate; exact syntax, scopes, allocation and candidates are checked |

`tensor_preparation_certificate` in
[`ClightTensorPreparedGenerated.v`](../prototype/interface/ClightTensorPreparedGenerated.v)
is an internal language adapter. It records successful preparation execution,
private-state framing and accepted canonical execution. The checked source
factory produces these fields. Source users do not supply a semantic callback
record.

The static factory additionally checks the exact redundant RMW, scalar
stability, supported structured control and a positive literal bound. All
historical word grammar, private allocation and canonical-model checks remain.
An unsupported source is left unchanged. The frontend adapter handles the
actual administrative skips and zero-indexed root spelling using the existing
language equivalence proofs. Its fallback is the equivalent base source.

The actual entry is
`ClightSelectedZeroLoadedWordFrontendCompiler.compile_selected_zero_loaded_word_frontend_regions`.
When compilation returns `OK`, its `_correct` theorem gives the existing
Csem-to-Asm backward simulation. The selected host still checks source progress,
legal placement and private allocation; no contextual closure follows merely
from a local condition proof.

## Evidence

The independent proof audit compiles only seven successor modules. It queries
21 endpoints over 610 dependencies; two endpoints are closed. The new whole
compiler uses exactly the historical 42 global assumptions, with no additions.
The minimal kernel remains closed. The report is
`build/loaded-word-zero/proof-v2/report.json`, SHA-256
`c459fc936f65c8765bcf0a0494b1a7c7b0d769beb0a73bdbfc6a7d264231f483`.
The first audit incorrectly compared PolCert-dependent endpoints solely against
the 35-global CompCert baseline. Its rejected audit and explanation remain in
`build/loaded-word-zero/proof/`; the successor uses the existing installed
compiler baseline and checks exact equality of old/new compiler assumptions.

The extracted compiler is `build/loaded-word-zero/compiler/ccomp`, SHA-256
`85898580c9a8e42880b326d00a45472aa6697de44c61d1498bd631300610f5d5`.
Its build stamp binds the proof, extraction, parser/driver adapter and native
proposal helpers. Actual scheduling, tiling, prepared codegen and final candidate
validation use the same existing producer. Parser metadata remains outside the
Csyntax theorem boundary. There is still no separate proof of raw-codegen to
affine-adapted candidate equivalence.

The native successor checks 112 cases in five configurations: 560 unmodified
Asm calls and 224 independent instrumented Clight dispatch calls. Full 6,144-word
arrays, public/first counters and context markers match the source model and
GCC reference. Marked/unmarked code, two rewrites, continuations, changing-header
fallback, unavailable child reads, disabled selection and scheduler failure pass.
Each installed coordinate order executes the zero preparation 25 times across
the matrix. Both `(2,2)` and `(2,3)` header aliases with `alpha=0` enter the checked
candidate; their original scan-only counterparts refuse. These branch counts
come from separate Clight derivatives, not from assembly path instrumentation.
The report is `build/loaded-word-zero/native/report.json`, SHA-256
`fa1280ed5295c18b498d82bb2b8f9d9cbe56c14862c78720fac15da813895ad1`.

A fresh comparison of old/new unmodified assembly uses twelve randomized
paired rounds, two coordinate orders, twelve inputs and two modes: 1,152
batches. The pinned CPU/process-time protocol validates every complete array,
public exit and context marker at the actual repetition count. Separate Clight
work counters check the complete guard and result; they do not instrument
production assembly.

| Input | Old row cost/source | New row | Old column | New column |
|---|---:|---:|---:|---:|
| Zero, 3×2×5 | 5.47 | 4.56 | 5.59 | 4.86 |
| Zero, 31×31×5 | 17.57 | 20.65 | 20.09 | 18.98 |
| Zero, aliased headers 2 and 3 | 1.05 | 4.10 | 1.05 | 4.23 |
| Nonzero, 31×31×5 | 17.59 | 21.65 | 20.12 | 19.87 |

The dense zero path scans no points and executes 47 guard `if`s instead of
4,805 points and 22,243 `if`s. Nonzero adds one `if` to the historical complete
scan. Row/column guarded functions shrink from 1,500/1,484 to 1,483/1,474 bytes;
unmarked functions remain 267/268 bytes.

**There is no complete-call speedup on this simple RMW example.** The new row
case regresses despite scan elimination, and accepting zero aliases costs more
than the old fallback. Candidate execution, public restoration and backend
layout are included; these measurements do not isolate them quantitatively.
They use warm capped inputs, lack confidence intervals and do not establish
benchmark speedups, workload acceptance fractions or break-even points.

The report is `build/loaded-word-zero-cost/report.json`, SHA-256
`724f0611c71c2cf0ad466335bdc8865172624da4439ea2c8c6baa11ef575a02d`.
All historical assembly, reports and failed audit records remain unchanged.

## Remaining work

The zero condition expands acceptance and removes the memory scan on its path.
This alone establishes no speedup: complete-call cost also includes candidate
loops, public counter restoration and backend code. Profiling actual candidate lowering and public restoration is the next cost
investigation. Compact conditions for nonzero RMWs and profitability decisions
remain active work; neither extra acceptance nor smaller code guarantees benefit.
General loaded domains, dynamic layout/delinearization of the original OLO BT
kernel and comparative author effort remain separate acceptance requirements.

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_zero_loaded_word.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_zero_loaded_word_pipeline.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_zero_loaded_word_cost.py --validate
```

For an absent compiler directory, `scripts/build_zero_loaded_word_compiler.py`
builds the successor compiler. Run it only before its build checkpoint exists.

These validation commands require the pinned toolchain and historical proof/native
checkpoints. Existing reports are validated; frozen compiler/cost directories
are not rebuild targets.
