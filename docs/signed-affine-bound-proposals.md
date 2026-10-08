# Signed affine bound proposals through the existing checker

2026-10-08. This stage follows the responsibility split in
[paper narrative](topdown/paper-narrative.md). The remote narrative head is
`12419c1`; its two design documents already match main. The implementation
change below addresses a candidate-production gap without changing the kernel,
condition service, region contract or installation proof.

## Problem and algorithm

The previous prepared-Loop adapter used zero when a generated lower bound was
not affine. A tile can have a negative coordinate: `floor(-1/2) = -1`. Starting
the proposed loop at zero loses source points. A membership guard can remove
extra iterations, but cannot restore points omitted by the envelope. The final
checker correctly refused this proposal under the signed source profile.

`GuardSignedAffineBounds.ml` proposes envelopes using mathematical integer
intervals from the original checked request. It handles signed scaling, sums,
positive-divisor floor division, minimum and maximum. For a maximum lower bound
or minimum upper bound, it prefers an affine leaf; otherwise it uses the
appropriate signed interval endpoint. The body retains the original-bound
membership tests, expressed using affine positive-divisor identities. Nested
iteration ranges feed later envelope proposals. Modulo bounds and nonpositive
divisors conservatively refuse this algorithm.

The successor `GuardSignedAffinePipelineCandidate.ml` still runs the actual
request through profiled model extraction, Pluto, affine validation, tiling
validation and per-statement prepared codegen. It applies this envelope proposal
to the generated Loop, preserves generated arguments and witnesses, and submits
the complete result to the existing source/candidate factory.

## Proof responsibility and reuse

| Work | Producer and certificate |
| --- | --- |
| Recognize source, propose ranges, run scheduler/codegen and enclose generated bounds | Ordinary untrusted algorithms; this stage adds no separately verified interval service |
| Conditional correctness, including actual generated Loop correspondence and machine-range obligations | Existing affine domain/checker, against the **original** source and request bounds |
| Source-point reading permission and safe runtime guard | Existing recursive affine source and materialized guard proofs; no rectangular-source substitution |
| Guarded region guarantee | Existing certified affine builder and private/public restoration |
| Legal site and whole-program installation | Existing selected Clight host: original source progress, scope, marker placement and private resources |
| Csem to Asm | Unchanged `compile_selected_polyhedral_regions_correct` and CompCert backend |

The source user supplies marked C and policy options. A new algorithm is not
registered as a proof-bearing language implementation. Final verification
licenses the returned candidate; the interval procedure itself is not a new
`C_derive` or `C_guard` theorem. This distinction is the concrete reuse tested
here. No new Rocq modules or axioms were added.

## Frozen evidence

- Compiler: `build/selected-affine-pipeline/signed-compiler-v1/ccomp`, built by
  `scripts/build_signed_affine_compiler.py`. The build stamp binds native
  proposals, extraction, driver/parser and the existing audited proof closure.
- Proof reused: `build/selected-affine-pipeline/proof-v1/report.json`, nine
  endpoints, inherited 42-global baseline, no additional global axioms.
- Signed matrix: `build/selected-affine-pipeline/signed-affine-2d-native-v1/report.json`,
  produced by `scripts/native_signed_affine_2d_validation.py`. Six configurations
  pass 1,152 unmodified assembly calls and 1,152 separate emitted-Clight calls.
- Same-binary word regression:
  `build/selected-affine-pipeline/signed-word-regression-v1/report.json`, 400
  assembly and 400 Clight calls.

The source profile uses floor `-2`, cap `4`, and child-bound proposals `[-2,4]`.
Inputs include starts `-1` and `-2`, empty/oversized domains, signed RHS overflow,
distinct blocks, identical pointers, small same-block offsets and widely
separated same-block views. Every array cell, public control and continuation is
compared with an independent word model and GCC reference.

Real tiling and automatic scheduling each install one triangular site plus two
sites in one function. Each observes 45 candidate selections and 51 runtime
refusals. Distinct-block negative-start inputs explicitly select the candidate
at all installed sites. Unmarked/disabled configurations install none;
scheduler/resource refusal retains the original source. The dependent chain's
unsupported model import is still statically refused. Phase files preserve the
actual source, profiled source, models, witnesses, raw/generated Loops and final
candidate-check diagnostics. A phase receipt alone is not installation evidence.

This is a signed **two-dimensional** tier. Three-dimensional functions remain
explicitly unmarked; the prior slow three-dimensional attempt remains separate.
The new matrix contains an additional input, so its totals are not a paired
performance or acceptance-rate comparison with the old nonnegative matrix.
No new compile-cost/profitability measurement or combined loaded/affine semantic
domain is claimed.

## Next obligation

The next priority is actual three-dimensional prepared codegen. Source inspection
shows Fourier-Motzkin projection followed by VPL canonicalization; the current
ordinary oracle's `add` retains all constraints. This suggests redundant-row
growth, but no isolated profile yet attributes the timeout to that cause.
`ExactCs.fromCs` checks the returned abstract representation against **all**
original constraints, in addition to the LCF forward guarantee. Any proposed
constraint compaction must retain both directions through that existing checked
path. Forward consequences alone do not justify dropping input constraints.

After actual rank-three generation, continue combining reached-point licensing
for nonrectangular domains with loaded-word observations, scalar/chunk examples
and OLO source adaptations. Neither a hand-written rank-three target nor this
passing rank-two matrix completes that goal.
