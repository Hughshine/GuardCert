# Actual rank-three affine compilation with checked constraint compaction

2026-10-08. This stage extends the actual-request
[signed affine pipeline](signed-affine-bound-proposals.md) to real
three-dimensional prepared codegen. It preserves the narrative's kernel,
language and optimizer responsibilities; no new kernel or host interface is
introduced.

## Change and checked boundary

PolCert's prepared code generator uses Fourier-Motzkin projection and VPL
canonicalization. The previous ordinary oracle returned all input constraints
from `PedraQBackend.add`, including redundant projected rows. A historical
rank-three attempt reached affine/tiling validation but exceeded its 600-second
compiler deadline before completing prepared codegen.

`GuardCompactMemoryOracle.ml` proposes a smaller representation. It compares
positive-normalized coefficient directions and retains the strongest parallel
row, preserves a contradiction when present, and removes tautological zero
rows. Returned constraints use the supplied certificates or the existing LCF
operations for equality orientation. The proposal does not manufacture an
unchecked constraint or claim an equivalence theorem of its own. Search limits
retain the original input; `GUARDCERT_CANONICALIZE=disabled` also retains it.

Two existing guarantees matter:

1. The abstract-domain `assume`/LCF contract gives the forward implication from
   the original assumptions to the proposed representation.
2. `ExactCs.fromCs` calls `checkCs` on **every original constraint**, proving
   the reverse implication before `canonize_Cs` returns the smaller
   polyhedron. Failure retains the original polyhedron. `canonize_Cs_correct`
   and `VplCanonizer.canonize_correct` provide the existing equivalence law.

Outside this exact canonicalization path, abstract-domain operations retain
their existing conservative or explicitly checked contracts. They must not be
described as exact merely because this oracle now compacts its rows.

The successor compiler maps `PedraQBackend.add` to this ordinary implementation.
It reuses the signed candidate proposer, actual source request, external Pluto,
transition validators, generated membership guards and final whole-candidate
checker. Source-point permission, safe guard, private/public restoration,
certified region builders, selected installation and Csem-to-Asm endpoint are
unchanged. No new Rocq module or global axiom is added. The new native algorithm
is not a separately proved condition service or generic assumption extractor.

## Real C and execution evidence

`scripts/native_compact_affine_validation.py` tests actual marked C with
parameterized two-dimensional triangular, three-dimensional triangular and
three-dimensional descending domains. The latter has child bounds `m-i` and
`p-j`; the former uses `i+m` and `j+p`. Stores use real flattened addresses
`64*i+8*j+k` and read two source arrays in the rank-three examples.

Real tiling uses sizes `2,3` or `2,3,4`; automatic scheduling does not pass
`--identity`. Both modes install five sites: one in each supported domain and
two in one function. The finite candidate table makes eight attempts, including
nested fragments; an attempt or phase receipt is not another installation.
The dependent chain's unsupported model import is statically refused.
An unmarked comparator remains unchanged.

Six configurations cover tiling, scheduling, unmarked C, disabled optimization,
scheduler failure and Fourier-Motzkin resource refusal. Each runs 240 calls,
for **1,440 assembly and 1,440 separate emitted-Clight executions**. Every cell
of three 2,048-word arrays, five public controls and a continuation is compared
with an independent sequential word model and GCC reference. Both normal modes
observe 81 candidate selections and 119 runtime refusals.

| Source | Candidate selections / runtime refusals per normal mode |
| --- | --- |
| Two-dimensional triangular | 18 / 22 |
| Three-dimensional triangular | 12 / 28 |
| Three-dimensional descending | 15 / 25 |
| Two regions in one function | 36 / 44 |

Identical pointers refuse. The contiguous rank-three accesses make small
same-block offsets overlap more often than in the strided rank-two example;
the observed acceptance differs accordingly. Distinct blocks and widely
separated views accept useful inputs. Each supported family explicitly selects
candidates at starts `-1` and `-2`, using the corresponding valid parameter
cases. Empty/oversized domains and signed RHS arithmetic remain in the matrix.
RHS word behavior is checked separately from the control/address assumptions;
a large RHS scalar need not force refusal of a reordering that preserves its
machine operations.

The same binary passes **400 assembly / 400 Clight** loaded-word regression
calls. Sharing this binary and language host does not combine the affine and
loaded-word semantic domains.

## Codegen diagnostic and retained attempts

`scripts/profile_compact_affine_codegen.py` selects only the triangular rank-three
region in the same C fixture and uses the same compiler binary in both modes.
With compaction enabled, one run completes in 9.588 seconds, passes the final
rank-three candidate check and matches all 240 assembly outputs. With compaction
disabled, one run reaches accepted affine/tiling transitions but is terminated
at the 90-second deadline without raw generated Loop or assembly. This shows
that enabling compaction resolves this bounded compile in the measured setup.
There is one observation per mode; it is not a statistical compile-time
benchmark, a speedup estimate or a runtime profitability result.

Oracle counters aggregate `add` and emptiness operations over the whole compile,
including proof queries; they are not counts of unique projection rows. The
normal full fixture records 255,978 `add` calls, peak supplied list length 69,
and no exhausted searches. Disabled-run counters are unavailable because the
compiler process group was killed at its deadline.

Two earlier smoke attempts are retained separately. The first matched assembly
outputs but expected six candidate attempts instead of eight. The second also
matched Clight outputs but expected acceptance where an ascending source's
first child was empty. The passing tier keeps that refusal and adds a separate
accepting parameter case. These were harness assertions, not observed compiler
miscompilations; their snapshots and logs remain bound in the attempts report.

## Frozen artifacts and commands

- `build/selected-affine-pipeline/compact-compiler-v1/ccomp` and its build stamp.
- Reused proof: `build/selected-affine-pipeline/proof-v1/report.json` (nine
  audited endpoints, inherited 42-global baseline, no additional axioms).
- Native: `build/selected-affine-pipeline/compact-affine-native-v1/report.json`.
- Word regression: `build/selected-affine-pipeline/compact-word-regression-v1/report.json`.
- Diagnostic: `build/selected-affine-pipeline/compact-codegen-profile-v1/report.json`.
- Historical harness attempts: `build/selected-affine-pipeline/compact-harness-attempts-v1/report.json`.

With the existing proof/toolchain checkpoint prepared, run:

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/build_compact_affine_compiler.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_compact_affine_validation.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_compact_affine_word_regression.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/profile_compact_affine_codegen.py
```

Existing successful artifacts validate instead of rerunning; build helpers
refuse to overwrite compiler checkpoints. Use distinct successor paths for a
fresh experiment. Historical-attempt recording is optional and requires its
retained input directories/logs.

## Remaining full-goal obligations

The affine source guard still requires `affine_first_path_flag`. An ascending
input with start `-2`, end `2` and `m=2` has an empty first child followed by
nonempty children, yet takes runtime fallback. This is a useful-acceptance gap
in source-entry construction, not a failure of the candidate checker or kernel.

The next joint case is a loaded root bound plus affine child bound, such as
`i < *N` and `K = i + *M`. The domain must derive stable captured parameters and
no-wrap/control/address facts for actual reached points. The language service
must read `*M` only after the source licenses that header, preserve public state,
and transport the actual guard exit to the candidate. The factory must produce
the existing region guarantee; the selected host still checks the site and
progress. A cached source cannot license its own unproved preloads.

The earlier two-dimensional `ClightAffinePrivateLoadedCandidates.v` path already
proves a narrower private-loaded-root source/snapshot bridge and uses affine
child bounds from stable temporary parameters. Its footprint, stability and
installation laws are reuse inputs, not absent work to reprove. First inspect
its actual request and candidate interface for connection to the real pipeline.
The conditional child load `*M`, recursive rank and word-body/general-domain
combination still need their own correspondence; a source with an explicit
unconditional preload is not evidence that the unprepared source is supported.

This requires a real joint source/model proof, not another dispatch between the
two existing factories. Continue scalar/chunk support, OLO source adaptations,
compact runtime conditions and complete guard/candidate cost evaluation. This
stage closes real rank-three codegen for the demonstrated affine families; it
does not complete the active goal.
