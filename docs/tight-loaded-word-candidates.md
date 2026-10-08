# Tight affine candidates for the installed loaded-word family

The zero-RMW compiler removed the stability scan on `alpha == 0`, but its
complete calls still cost much more than source. Inspection found a separate
candidate problem: affine bound adaptation discarded the tile-local bounds.
This successor changes the untrusted candidate producer. It reuses the same
zero-preparation factory, actual source/candidate checker, language host and
Csem-to-Asm theorem. The minimal semantic kernel is unchanged.

## The bound proposal

Prepared codegen emits a point loop of this form, with tile coordinate `t`:

```text
loop [max(0, 2*t, -1), min(n, 2*t+2, n+1))
    body
```

The earlier affine adapter proposed this candidate:

```text
loop [0, n)
    if original_lower <= point && point+1 <= original_upper:
        body
```

The candidate retains the intended points, but enumerates the entire source
extent for every tile. Nested point loops compound that cost. Removing the
stability scan does not remove these candidate iterations.

`GuardTightPreparedTensorCandidate.ml` instead selects affine leaves involving
outer loop coordinates. It proposes the point loop `[2*t, 2*t+2)` and retains
membership checks for the clipped source domain. In this family the generated
row, column and component point loops use tile widths rather than source
extents. Outer tile loops still use conservative affine envelopes with floor
membership guards; this change does not provide a general affine lowering of
floor division.

The producer also normalizes affine inequalities with arbitrary-precision
coefficients. It proposes removal of checks implied by the chosen loop bounds,
nonnegative outer loop coordinates, or stronger parallel inequalities. It
retains the raw prepared output, actual instruction arguments and tiling
witnesses. These are proposal algorithms, not proved simplification laws.

## Verification responsibility

| Owner | Responsibility in this successor |
|---|---|
| Generic framework | Existing local guard/preservation composition; no new kernel obligation |
| Clight language and loaded-loop domain | Existing safe checks, source/canonical correspondence, actual candidate execution, public restoration and private-state frames |
| Selected Clight host | Existing placement/progress checks, repeated installation and backend connection |
| Untrusted optimizer implementation | New affine bounds and simplified candidate guards, plus existing raw codegen and witness data |
| Verified candidate checker | Recheck the actual proposed Loop against the conditionally valid source; rejection cannot install an unchecked candidate |

The compiler entry remains
`ClightSelectedZeroLoadedWordFrontendCompiler.compile_selected_zero_loaded_word_frontend_regions`.
Its correctness theorem quantifies over the candidate proposer, so changing
that untrusted function requires no new proof module. The build stamp binds
the new native producer to the existing independent proof audit and extraction.
No historical proof object, compiler, source helper or report is rebuilt.

There is still no separate theorem relating raw prepared output to adapted
output. The raw output has the prepared pipeline's theorem; the installed
adapted output obtains its certificate from the final actual-candidate checker.
The implementation does not transfer one theorem to the other output by fiat.

## Degenerate tile refusal

The first native audit expected `[1,1,1]` tiles to install. Actual prepared
codegen eliminates their three tile coordinates and emits a depth-three Loop,
while the proposed witness retains three tile links. The final selected dump
contains no dispatch for those regions. The current tiling bridge checks
`memory_tiling_current_shape`: the current witness dimension must equal the
actual extracted instruction depth. This representation is outside that gate.
The original program remains in place and its complete output agrees with the
source model and GCC; it is not evidence of accepted unit tiling.

The rejected audit, outputs and source bindings are preserved in
`build/loaded-word-tight/native/failure.json`. Its successor reuses those
compilations read-only, reruns their assembly and source-reference executions,
and records unit tiles as a negative case. The original helper is retained.
Supporting this degenerate witness requires a separate proposal/bridge change;
it is not obtained by weakening the shape check.

## Measurement boundary

Native behavior, generated-Clight branch diagnostics, native complete-call time
and machine instruction counts are separate evidence. Timing uses untouched
compiler-produced assembly and includes preparation, candidate/fallback, public
exit and surrounding function work. Each generation has its own unmarked
same-input baseline.

The instruction diagnostic uses Callgrind's `Ir` event, toggled only during the
selected or unmarked function. It decodes instruction positions, excludes
inclusive call costs, and checks function entries and total self counts.
The harness invokes the kernel twice; complete arrays, public exits and context
markers are checked for both calls. On these x86 kernels, scaled 32-bit RMW
store counts are also checked against the independent source model. Instruction
counts are not CPU cycles, and store-PC classification is diagnostic evidence,
not a verified backend theorem. See the
[Callgrind manual](https://valgrind.org/docs/manual/cl-manual.html) for collection
and inclusive/self attribution semantics.

## Native evidence

The extracted compiler is `build/loaded-word-tight/compiler/ccomp`, SHA-256
`512b361150dae742a6901672535d241e40e30155bc69e0ff450f87522534633a`.
Its build stamp is SHA-256
`da3e66ae32ee1dc76060375a5c16c8b88cbdb8bb44bb8cb31184b107a3fa5496`.
It consumes the existing seven-module zero-preparation proof audit, SHA-256
`c459fc936f65c8765bcf0a0494b1a7c7b0d769beb0a73bdbfc6a7d264231f483`:
21 endpoints, 610 dependencies, exactly the existing 42 compiler globals,
no added assumptions, closed minimal kernel. No new Rocq proof endpoint is
claimed for this candidate-producer change.

Seven configurations execute 112 cases each: **784 unmodified Asm calls** and
**336 separate generated-Clight dispatch checks**. The row/column `[2,3,2]`
and column `[4,5,3]` candidates install, with five real scheduling/tiling/codegen
invocations per configuration. Unit `[1,1,1]` candidates do not install.
Unannotated, disabled and scheduler-failure programs also retain source.
Full 6,144-word arrays, public/first counters and context markers match the
source model and GCC reference. Zero alias acceptance, nonzero changing-header
refusal, unavailable child reads, repeated rewrites and supported context cases
retain their prior behavior. Each installed configuration takes zero preparation
25 times in the matrix; these counts come from separate Clight derivatives.

`scripts/native_tight_loaded_word_pipeline_v2.py` validates the successor report
at `build/loaded-word-tight/native-v2/report.json`, SHA-256
`89c7ed1b8802a7fe26a399542ba59416e02dc1b015be25b068167f6594023735`.
Its bindings include the rejected predecessor manifest, SHA-256
`eaade38fefda066e68cfbdc15a76aa808351ee577ba1996b65b637af61340aab`.
Three predecessor compilations are reused read-only; their assembly/reference
executions are repeated in the successor. The remaining configurations are
new compilations. This reuse is recorded rather than reported as seven fresh
compilations.

## Fresh complete-call cost

This comparison uses the frozen zero-capable compiler as **old** and the tight
candidate compiler as **new**. Both use the same zero-RMW preparation and the
same `[2,3,2]` tile sizes. It is a new comparison, not the earlier scan-only
versus zero-capable experiment. Twelve randomized paired rounds, four
generation/layout configurations, twelve inputs and two modes yield **1,152
batches** on the pinned Ryzen 7 7800X3D CPU. Process CPU time, warmup,
calibration and full-result checks use the previous protocol. Every timed batch
checks the complete result at its actual repetition count outside the timed
interval; production assembly is unchanged.

| Input | Old row cost/source | Tight row | Old column | Tight column |
|---|---:|---:|---:|---:|
| Zero, 3×2×5 | 4.74 | 3.24 | 4.88 | 3.27 |
| Zero, 31×31×5 | 21.00 | 2.97 | 19.36 | 2.97 |
| Zero, aliased headers 2 and 3 | 4.23 | 2.45 | 4.37 | 2.45 |
| Nonzero, 31×31×5 | 22.34 | 4.09 | 20.78 | 4.19 |

Dense zero row calls decrease from 58,495.5ns to 8,029.1ns and column calls
from 54,324.0ns to 8,175.1ns (medians). Each has its own matched unmarked
baseline, about 2.7–2.8µs. These are improvements over the old generated
candidate, **not speedups over source**. All accepted entries in this table
remain slower than source. Changing-header refusal is about 1.11/1.18 times
source before and 1.12/1.15 after; this is not a pure guard-cost estimate.

All twelve old/new complete Clight guard diagnostics agree for each coordinate
order. Dense nonzero still scans 4,805 points and evaluates 22,244 guard `if`s;
dense zero still scans none and evaluates 47. Row/column selected functions
shrink from 1,483/1,474 to 1,226/1,230 bytes; their unmarked functions remain
267/268 bytes. Timing includes changed candidate code and its backend placement
and allocation; it does not isolate the CPU cost of an individual guard or loop.

The report is `build/loaded-word-tight-cost/report.json`, SHA-256
`284bb3ad2f1b5ec6bfc8ba1301c968d567f58e2ecded434d18b5676aef976d75`.
The report retains all raw batches, ratio IQRs, calibration and bindings to both
native/compiler checkpoints. There are no confidence intervals, representative
benchmark conclusions, acceptance frequencies or break-even estimates.
Historical zero-condition measurements remain unchanged.

## Actual machine instructions

Valgrind 3.18.1 profiles four generation/layout configurations, two function
modes and six inputs: **48 profiles**, two calls per profile. The complete
outputs and dynamic scaled-word RMW store counts pass independent checks.

| Input | Source Ir/call | Old row | Tight row | Old column | Tight column |
|---|---:|---:|---:|---:|---:|
| Zero, 3×2×5 | 467 | 2,906 | 1,506 | 2,903 | 1,506 |
| Zero, 31×31×5 | 63,749 | 939,471 | 167,282 | 939,468 | 167,282 |
| Zero, alias 2/3 | 461 | 2,576 | 1,245 | 2,573 | 1,245 |
| Nonzero, 31×31×5 | 63,749 | 1,023,363 | 251,174 | 1,023,360 | 251,174 |

Both dense candidates still execute exactly 4,805 array RMW stores per call;
the small zero and zero-alias candidates execute 30. These inputs do not erase
or replace their RMW computation with a handwritten target. The instruction
counts support the inspected candidate-enumeration problem, while the separate
native timing measures its complete-call consequence. The nonzero-minus-zero
difference is 83,892 instructions in both generations on the dense inputs;
the historical stability preparation remains. This is an instruction-count
difference, not an attribution of CPU cycles.

The report is `build/loaded-word-machine-profile/tight-v1/report.json`, SHA-256
`d4b271a1e9483dd4a5e45b54bbddb075f50a637d8c1a4d853e3031ec404d5d0c`.
It retains commands, per-PC counts, disassembly, stdout/stderr, input hashes
and collection protocol. The initial exploratory profiles are retained
separately and are not included in this 48-profile result.

## Remaining scope

Tighter candidates do not enlarge the supported C source grammar or complete
the full original OLO/BT dynamic layout instance. Nonzero RMW still scans the
source points to prove loaded-header stability. Next steps include supported
proposal/bridge handling of degenerate tile dimensions, compact nonzero
conditions with source-licensed physical observations, and representative
workloads on which reordering can justify its overhead. Profitability policies,
general loaded affine domains, full dynamic layout and comparative author
effort remain requirements of the active project. Local or intermediate
acceptance never substitutes for the final actual-candidate/host contract.

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_tight_loaded_word_pipeline_v2.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_tight_loaded_word_cost.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_tight_loaded_word_instructions.py --validate
```

These commands validate existing immutable checkpoints. The new builder is
`scripts/build_tight_loaded_word_compiler.py`; run it only when its compiler
directory is absent. The native successor also requires the recorded rejected
predecessor. For cold reproduction, run
`scripts/record_tight_loaded_word_refusal.py --run-audit` under the pinned opam
environment before the successor. It runs the original native helper, requires
the expected unit-tile rejection and complete matching outputs, and records
the manifest. With existing evidence, its default validates the rejection only.
Neither path overwrites an existing checkpoint. Historical proof/native inputs
and the pinned toolchain remain prerequisites.
