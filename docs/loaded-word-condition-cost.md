# Loaded-word checks: measured cost and a value-preservation condition

This checkpoint measures the installed loaded-header/runtime-Horner RMW
pipeline. It also proves a new constant-time sufficient condition at the
framework's condition-encoding interface. The new condition is not yet installed
in that compiler. The complete research goal remains active.

## Complete-call measurements

The frozen v3 compiler, proofs, C, assembly and integration reports are inputs.
[native_loaded_word_cost.py](../scripts/native_loaded_word_cost.py) assembles
the existing `row-tile` and `column-tile` files into a new directory, renames
only the historical `main` symbol, and links a timing harness. The measured
`selected_one` and `unmarked` code receives no counters or edits.
The unmarked function in the same C/assembly configuration is the baseline.
Both contain the same loaded-header loop, header initialization, public-counter
stores and context markers; the selected occurrence adds guard and candidate.

The report is `build/loaded-word-cost/report.json`, SHA256
`f406cb2093aa3b50ecdc264bce6e47ed088c94ea5cf0a4fd75d64d71e8dc89c6`.
It records 20 rounds, two coordinate orders, nine inputs and two modes: 720
timing batches. Adjacent pairs use the same input/layout, with randomized pair
and mode order. Batches use process CPU time, a pinned CPU, one warmup call, and
a 0.04-second calibration target. Each process initializes its array outside
timing; the actual function constructs or resets headers on every call.
The harness checks all 6,144 words, six public/first-region counters and two
context markers before and after each batch at its actual repetition count.
An independent signed32 model accounts for accumulation, wrap and header resets.

The host is an AMD Ryzen 7 7800X3D. Ratios below are medians of paired complete
call costs, including capture, the complete check, dispatch, candidate/fallback,
public exits and backend code. They are not guard-only timings.

| Input | Guard scan points | Row cost/source | Column cost/source |
| --- | ---: | ---: | ---: |
| Accepted 3×2×5 | 30 | 5.47 | 5.64 |
| Accepted 31×31×5 | 4,805 | 17.69 | 20.43 |
| 2×32×5; row layout refuses, column accepts | 320 | 2.27 | 14.46 |
| Nonzero start; refuses before capture | 0 | 1.00 | 1.02 |
| Empty root; null data and unavailable child | 0 | 1.16 | 1.20 |
| Empty child | 0 | 1.04 | 1.14 |
| Stride profile refuses after scanning | 10 | 1.70 | 1.83 |
| Header aliases output and changes | 1 | 1.11 | 1.11 |
| Header aliases output, increment zero | 1 | 1.01 | 1.05 |

The selected function occupies 1,500 bytes versus 267 for the row baseline,
and 1,484 versus 268 for the column baseline. This simple RMW input obtains no
speedup. A proved installed candidate does not establish useful optimization.
These warm, capped inputs are not a representative benchmark suite, and their
acceptance counts are not workload acceptance frequencies. No confidence
interval or break-even result is claimed. Shared-host noise and function
placement can affect ratios.

Guard work is measured separately by a GCC execution of an instrumented Clight
derivative. The derivative runs the complete function and checks the same full
result; counters cover `if` evaluations from the original-row test through the
complete guard, excluding final dispatch. For the dense accepted input, it
observes 4,805 scan points and 22,243 `if` evaluations in each layout. A stride
profile refusal still visits all ten body points. A header alias refuses at the
first point even when its store preserves the header value. These are Clight
counts, not production assembly instruction counts. Complete-call timing does
not identify how much overhead comes from the scan versus the generated
six-loop tiled candidate or its backend lowering.

## A checked sufficient condition that permits aliases

For `a[index] = a[index] + alpha`, address disjointness is stronger than header
stability requires. When `alpha == 0`, a successful signed32 RMW writes back
the loaded word. A loaded `Mint32` header remains unchanged, even if that header
is the output cell. Unlike the older constant-store shortcut, this condition
does not require root and child raw words to equal each other or a uniform
stored constant.

| Module | Checked or proved result |
| --- | --- |
| [ClightZeroRmwObservation.v](../prototype/interface/ClightZeroRmwObservation.v) | A redundant full-word store preserves every previously defined `Mint32` word. A syntax checker lifts this law through finite structured control while protecting `alpha`. |
| [ClightZeroRmwCondition.v](../prototype/interface/ClightZeroRmwCondition.v) | Successful original addition licenses the scalar word domain. The pure equality check is available on that domain; acceptance implies the effect law. `zero_rmw_condition_encoding` has the existing `readonly_condition` type. |
| [ClightZeroRmwExample.v](../prototype/interface/ClightZeroRmwExample.v) | The loaded-Horner source passes the checker. An actual aliasing RMW preserves raw headers 2 and 3, while the old separation tree refuses and the new equality tree accepts. Nonzero equality and unsupported store/control syntax refuse. |

The presumption has a precise scope:

```text
For every finite execution of the checked fragment:
  load Mint32 before b ofs = Some (Vint w)
  implies load Mint32 after b ofs = Some (Vint w).
```

It does not assert equality of memories, arbitrary bytes, pointer fragments,
other chunks or traces. Successful accesses supply alignment facts that exclude
partial overlap at distinct `Mint32` addresses. The checker permits skip, break,
continue, protected temporary assignments, exact signed32 redundant RMWs,
sequences, conditionals and loops. Calls, other stores and assignments to
`alpha` refuse. The theorem consumes a finite original execution; it makes no
new termination claim.

Safety has an explicit boundary. A successful original RMW addition proves
`alpha` contains a word, so the equality test needs no pointer arithmetic or
memory probe. An empty region has no reached RMW witness. The loaded-family
producer must establish a reached first point from positive captured counts,
or skip this test. Source users should not provide a new incoming-state
definedness assumption in place of this derivation.

The independent checkpoint `build/zero-rmw/proof/report.json`, SHA256
`914e950d18146c7492b0f16f414b57116d62f9706e714db115c9383ae2e1f8e3`,
audits 23 endpoints over 554 dependencies, with four closed endpoints and at
most six existing CompCert globals per endpoint. It adds no axiom, leaves the
kernel closed and unchanged, and independently checks the installed compiler's
existing 42-global baseline. Only new modules are compiled; frozen source,
objects and reports remain inputs. It adds no new compiler or assembly claim.

## Responsibility split and next connection

| Owner | Responsibility |
| --- | --- |
| Framework | Consume the existing condition certificate and compose it with derivation, candidate and host certificates. The minimal kernel is unchanged. |
| Clight instantiation | Prove word-store observation, finite-control lifting, scalar-check safety and read-only encoding. Produce source-point licensing and private-state/frame transport for installation. |
| Domain implementation | Recognize RMW/increment and headers from data; connect preservation to cached-source/canonical-model execution, then reuse numeric/layout and actual-candidate checking. |
| Language host/site | Consume the new local guarantee after its derivation is proved; check progress, placement and private allocation, and compose whole-program installation. |

This certificate alone does not justify replacing the installed scan. Its
aliasing accepted states need a new source-to-canonical derivation; they do not
imply acceptance of the old separation tree. The remaining connection must
establish the scalar license from the actual source prefix, conditionally
initialize the helper, preserve public temporaries and both header observations,
transport canonical execution to the actual check exit, and then consume the
existing generated candidate and selected host. A successor compiler and
same-C/cost comparison will validate that installed path.

For nonzero increments, compact affine footprint conditions remain the main
performance direction. They must prove safe machine arithmetic, pointer
observations and header-effect coverage. The dense regression also motivates
separating guard and candidate costs, improving candidate lowering, and using
an untrusted profitability policy that may retain the original. Policy cannot
substitute for correctness. These tasks retain the narrative's distinctions
between encoding, source/model derivation, candidate execution and installation.

Reproduction uses the pinned environment:

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_zero_rmw.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_loaded_word_cost.py --validate
```

The audit builds only the new modules on its first run and subsequently checks
the proof checkpoint. The cost helper uses a fresh directory on its first run
and refuses to replace an existing timing report.
