# Signed header profiles through the empty-rewrite condition client

Date: 2026-10-08. This successor extends the installed
[shared-fallback empty rewrite](affine-empty-plan-installation.md) to negative
header parameters within a checked profile. It also separates the condition
certificate from the source/capture/public-exit client. The selected compiler,
source grammar, kernel, host and polyhedral candidate validators retain their
existing interfaces.

## Scope and existing encoding support

For an original loaded loop with `K=i+*M`, `N=3`, `M=-4` and entry `i=0`, every
child is empty. The source exits with `i=3`, `j=0`, `K=-2`, without reading
body-only variables or array pointers. This input previously refused the
positive-root shortcut because its header profile required nonnegative M.
The new target accepts it, including when the body pointers are NULL or the
body-only local is undefined.

Inspection of `PolCertAffineClight.v` establishes a narrower diagnosis than
"the lowering requires nonnegative inputs": its intervals, `typed_view` and
`env_within` already support signed values. `analyze_sound` proves machine
safety for every intermediate operation in a checked interval environment;
`lower_test_exact` connects the mathematical test to the actual Boolean path.
The earlier source client selected nonnegative parameter intervals. Those
certificates cannot be used for negative values, but the generic encoder can
be instantiated with different intervals.

The new header profile retains the root interval `[0,row_cap]` and changes
other header intervals from `[0,cap-1]` to `[-cap,cap-1]`. The source user uses
the same configuration options. Actual range checks establish `env_within`
before the endpoint code runs. The original loaded-source receipts and first
reached setup supply signed header words; no speculative body access is added.

The domain condition remains the signed endpoint presumption:

```text
N > 0
Int.min_signed <= width(0)   <= 0
Int.min_signed <= width(N-1) <= 0
```

Its affine extrema implication, original-source zero-leaf execution and exact
public restoration are unchanged. An outer-empty path still skips M and
preserves the original j/K values. There is one original fallback statement.

## Reusable client and proof responsibilities

The condition client consumes a `readonly_condition` that is safe in the
original-source invocation domain and, on acceptance, provides the existing
`affine_empty_snapshot_facts`. A condition-library author supplies this
certificate. The source user does not supply semantic callbacks.

| Component | Contract and responsibility |
| --- | --- |
| Existing affine language encoder | Check interval proposals, prove safe actual expression evaluation and exact Boolean encoding; supports signed intervals without a new arithmetic semantics |
| Signed condition producer | `affine_empty_signed_range_condition`, `affine_empty_signed_width_condition`, `affine_empty_signed_condition`: combine original-source-licensed header reads, runtime interval gate and encoded endpoints |
| Local replacement client | `affine_empty_client_guarded_execution`: consume the condition certificate and reuse the same actual empty-source/public-exit proofs |
| Capture/choice client | `affine_empty_client_captured_execution`, `affine_empty_client_prefix_contract`: reuse conditional root/child capture, readonly alternative factoring, private Boolean transport and projected public observations |
| Checked factory | `check_affine_empty_signed_source_sound`: derive invocation/resource evidence from the checked source and profile, check typed/fresh caches/result, instantiate the condition client |
| Language installation | `compile_selected_empty_signed_regions_correct`: supply the existing projected region guarantee to selected installation and CompCert, yielding Csem-to-Asm backward simulation |
| Kernel | Existing local certificate composition; no new obligation or axiom |

The client's entry domain is produced from original execution receipts; that
execution is a proof starting point, not runtime pre-execution. On acceptance
there are no body loads, stores or events, and final memory is unchanged.
Private captures and Boolean writes are hidden from the original public scope;
exact iterator/header exits remain available to the continuation. On refusal
the original repeated-load AST executes.

Existing candidate builders retain static priority. After their static
refusal, the registry tries the signed empty builder, then the previous
nonnegative empty builder if the signed builder refuses during compilation.
This backup matters because a wider interval can make intermediate range
analysis fail. It does not add an empty runtime branch to a candidate already
returned by an earlier builder.

## Checked evidence

Five frozen modules, 391 lines, audit twelve new endpoints over 2,000 reachable
bindings, with at most the same 42 inherited globals and no added axiom. Seven
archived source-build attempts comprise five successes and two rejected proof
sources. A separate type-inspection probe with an invalid module filename and
its successful renamed probe are retained and bound; they are not new proof
endpoints.

The historical two source matrices and six configurations pass 2,280 assembly
and 2,280 independent Clight diagnostic calls. Every call checks all 12,000
array cells, public i/j/K and continuation effects. All historical fast paths
are retained. Per normal 190-input matrix:

| Source widths | Previous fast / fallback / unmarked | Signed fast / fallback / unmarked |
| --- | ---: | ---: |
| `i+M`, `2*i+M` | 33 / 107 / 50 | 87 / 53 / 50 |
| `i-M`, `2*i-M` | 87 / 53 / 50 | 87 / 53 / 50 |

All 54 added calls have negative M. They include eighteen calls with NULL body
pointers, twenty-one with an undefined body-only word and eighteen with
header/data overlap; these categories overlap. Each installed normal matrix
now accepts twenty-seven NULL-body, thirty-two undefined-body and twenty-seven
header/data-overlap calls. Empty outer acceptance with unavailable M remains.
Scheduler and oracle-resource refusal retain the independent rewrite;
unannotated and disabled configurations install none.

A separate 190/190 Asm/Clight run sets the header cap to `2147483647` with an
unavailable scheduler. For the subtraction source, the wider signed endpoint
interval exceeds machine range, while the old nonnegative interval remains
encodable. The actual dump contains the old nonnegative cap gate and lacks
the signed lower gate; it has one original fallback and the same 87 fast
selections as the normal subtraction matrix. This exercises the static backup.

The same binary passes word 400/400, recursive-affine 480/480,
private-loaded 270/270, zero-width 672/672 and RMW 816/816 Asm/Clight calls.
Their historical path/configuration records remain identical, and each normal
RMW mode retains 126 fast and 146 fallback selections. These checks preserve
the earlier candidate routes without identifying their semantic domains.

## Limits and next work

This is bounded signed-profile support. It does not accept arbitrary int32
parameters: out-of-profile values, including the tested `Int.min_signed`,
still fall back. A wider static box may refuse compilation even when a
particular runtime valuation would be safe. The existing dynamic wide-arithmetic
condition library is a possible next producer for the same condition client;
its integration here requires its own proof, compiler and acceptance evidence.
Body/candidate profiles and the source grammar are unchanged.

Runtime empty/candidate composition, mixed negative/active child domains,
general recursive loaded affine sources, broader scalar/chunk services,
complete-call costs and combined OLO/BT coverage remain required. This stage
has no profitability measurement and does not complete the full goal.

## Reproduction

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_affine_empty_signed.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_affine_empty_signed.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_affine_empty_signed_profile.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_affine_empty_signed_regression.py
```

Extraction uses `scripts/build_affine_empty_signed_compiler.py` and refuses to
overwrite a compiler checkpoint. Immutable checkpoints:

- `build/affine-empty-signed/proof-v1/report.json`
  (`f95d5100b783b88db7460a7b0ae5660fc6b8dbf162fa5c2bd54f9854fdf1f9a3`).
- `build/affine-empty-signed/compiler-v1/ccomp`
  (`f3ca07d8b1e92474eac5e49ce12bf7d877481f55037cd20a86f6ad603fb65efc`).
- `build/affine-empty-signed/native-v1/report.json`
  (`f03763720778ea458743ed964c127ccf5adb3604e46824b83615a9a7f0267f80`).
- `build/affine-empty-signed/profile-refusal-v1/report.json`
  (`7f024da1ecf62c6395888cd4a0fb65133f03532eed7e8ee82b8db3a98f40a488`).
- `build/affine-empty-signed/regression-v1/report.json`
  (`a4355e82ebe37dcd348fb10ed1b9a51ed8609c572a553fbce0ae3708fa650ecc`).
