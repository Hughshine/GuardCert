# Zero-width candidate, factory and native installation

Date: 2026-10-08. This stage installs the
[zero-width source/stability proofs](zero-width-stability.md) in an extracted
CompCert compiler. Original `i<*N; K=i+*M` and `K=2*i+*M` regions now accept
supported inputs whose first child is empty and whose next child is nonempty.
The source user supplies ordinary C, `#pragma scop` markers and strategy
options; no model-correspondence or completion callback is required.

The new entrypoint is
`ClightSelectedZeroSnapshotPlannedCompiler.compile_selected_zero_snapshot_planned_regions`.
Its proved result is Csem-to-Asm backward simulation through the existing
selected host and CompCert backend. The generic kernel, host contract and
underlying polyhedral validators remain unchanged.

## A concrete accepted input

For `N=3`, `M=0`, `i=0`, the original source computes child widths `0,1,2`
(or `0,2,4` for the second function). Capturing M is licensed by the original
reached setup, even though the first body is not reached. The injected checks
then follow this order:

1. Check the original header and its arithmetic range environment.
2. Try the first-reached-row-zero condition. It refuses before body-input
   checks. The row-one alternative proves row zero empty and row one reached;
   original execution supplies the later leaf's input words.
3. Check geometry ranges, then run the existing source-licensed N/M stability
   scan under the wider nonnegative-width domain.
4. Check data-array separation and the validator/encoder range environments.
5. Execute the separately checked generated candidate and restore public
   iterators and the last inner bound. Any failed check executes the original
   repeated-load source.

The guard is a sufficient condition. Refusal of the first alternative is not
used as a proof of its negation; the second alternative is independently safe
in the same readonly header domain. No guard executes source stores to obtain
its receipts. All-empty input `N=1, M=0` refuses before body-only input reads.

## Certificates and responsibility

| Link | Concrete endpoint or implementation | Responsibility and direction |
| --- | --- | --- |
| Entry facts to safely executable preparation | `affine_zero_snapshot_preparation_condition` | Language/domain composition: original capture receipts, checked header/ranges, then alternative first-reached input licensing produce `affine_domain_ready` |
| Header and data facts | `affine_zero_snapshot_candidate_condition` | Actual readonly checks establish N/M observation preservation, source-footprint data non-alias and candidate ranges; these obligations remain distinct |
| Actual source to cached source | `affine_zero_snapshot_checked_cached_execution` | Language transport consumes the given original execution and accepted facts, preserving its exact final memory and temporary exits |
| Cached Clight to source Loop | `memory_zero_width_pointer_region_source_under_ranges` | Domain decoder uses the produced full input view and nonnegative widths; it is a one-way execution theorem, not a parser or standalone equivalence |
| Source Loop to candidate Loop | `check_affine_zero_pointer_model_sound` / `check_affine_zero_pointer_tiling_model_sound` | Actual candidate is rechecked under `memory_zero_width_assumed_loop`; an old first-positive certificate is not reused |
| Candidate Loop to actual Clight/public exits | `affine_zero_pointer_candidate_execution` | Existing pointer backend with the new certificate and model bridge; public exit restoration is explicit |
| Actual guarded region | `check_affine_zero_snapshot_planned_source_sound` | Checked factory binds source syntax, proposal, fresh typed caches/result, actual compiled code, original fallback and region guarantee |
| Whole program | `compile_selected_zero_snapshot_planned_regions_correct` | Existing language/site installation and verified CompCert backend; does not move contextual closure into the generic kernel |

The new envelope service needs a typed geometry view, nonnegative bounded widths
and observed pointer receipts. It does not require cached-source completion as
an extra invocation premise. The complete factory still produces original-source
and capture facts and consumes the execution bridges; they are not source-user
assumptions.

The ordinary pipeline request already contains the actual, unguarded affine
source Loop. That request and native proposer are reused. The new factory
checks the returned candidate under the wider assumed model. Its separate
schedule-proposal path also uses the new assumed Loop. This keeps proposer
metadata distinct from the certificate produced by the final checker.

The compact plan reuses the previous proved N/M scan plan and the previous
private-Boolean lowering. It does not materialize the complete decision tree
during extracted compilation. The new builder precedes the existing registry,
so an older recognizer cannot hide its wider acceptance domain.

## Validation

Eleven new modules, 1,272 source lines, audit 33 endpoints: one closed, at most
the existing 42 globals per endpoint, and no additional global axioms. The
1,934 proof bindings include the reachable source/object closure and all 23
source-build attempts: eleven successful and twelve rejected attempts, preserved
without replacing successful objects.

The new compiler passes six configurations: tiling, scheduling, unannotated,
disabled, scheduler failure and checker-resource refusal. Each compares 336
complete calls against an independent word model and GCC reference, then
independently executes emitted Clight. Total: **2,016 Asm / 2,016 Clight calls**.
Checks include all 19,200 array cells, loaded header words, public controls and
the continuation. Normal modes install two marked functions and leave the
unmarked function without a guarded installation.

Each normal mode has 60 actual fast selections, 164 runtime fallbacks and 112
unmarked calls. Among actual first-empty/nonempty-later sources, 30 accept and
12 refuse. Six further cases log `N` in `2,3,4` but alias N and M, so initializing
M to zero makes the actual outer count zero; these safely refuse. All sixteen
marked body-empty cases in the `N=1,M=0` input group also refuse (including two
with an empty outer loop from that alias). Comparing the same 264 old cases,
acceptance increases from 30 to 40 with no lost acceptance. The ten newly
accepted cases have `N=3, M=0`, including headers located in the unused first
row's write positions. Data overlap, distinct-allocation envelope refusal,
changing headers, arithmetic/cap refusal and unavailable M on empty outer
paths remain covered. Six proposal attempts per normal mode are two installed
sites, not six installations.

The **same binary** passes the existing word 400/400, recursive-affine 480/480
(including actual rank three and repeated marked regions), and private-loaded
270/270 Asm/Clight regressions. There is no new complete-call cost or
profitability measurement in this stage.

The manuscript's case-study and evaluation sections now record these bridges,
their premise producers and the wider acceptance matrix. Its evidence map binds
the report and compiler digests. Required repository anchors are distinct from
ignored experiment artifacts; the PDF builder records artifact availability
without claiming to rerun or validate the research results.

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_zero_width_installation.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_zero_width_snapshot.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_zero_width_snapshot_regression.py
```

Fresh extraction uses `scripts/build_zero_width_compiler.py`; a full matrix uses
`scripts/native_zero_width_snapshot.py`. Existing checkpoint directories are
preserved rather than overwritten. Individual successor modules compile through
`scripts/compile_zero_width_installation.py MODULE --attempt NAME`, which
archives source and log before each attempt and refuses successful objects.

| Artifact | SHA-256 |
| --- | --- |
| `build/zero-width-installation/proof-v1/report.json` | `9a45eecb279d0e965604602de3ca0a25fd2db6ede8414f0a8ae72c427caab192` |
| `build/zero-width-installation/compiler-v1/ccomp` | `f20b27581361e16e3978c85b35972080e3653908a9c4ed2003f36e9acf8f796e` |
| `build/zero-width-installation/native-v1/report.json` | `3a820869cb0df632e77304de5ee02fd950c119b3ea53028be257dd759ab13a19` |
| `build/zero-width-installation/regression-v1/report.json` | `edb9350565b6595def6217dfa534be0b780fd480e2f54c0a107a56aae6b3c960` |

## Remaining scope

The new source path is the declared two-dimensional loaded-affine family, with
first reached row zero or one and nonnegative widths. Negative-width public
exits, an all-empty body-input bypass, broader alias/value-preserving sufficient
conditions, general recursive loaded affine domains, scalar/chunk coverage and
the complete OLO/BT case study remain active. Existing recursive-affine and
loaded examples are not thereby one combined semantic domain. Complete guard
cost, compact condition derivation and useful acceptance must still be evaluated
for the broader workloads. The full goal is not complete.
