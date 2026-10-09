# Shared fallback for header-only empty affine rewrites

Date: 2026-10-08. This successor retains the source family, safe endpoint
condition and exact public exits from [the empty rewrite](affine-empty-installation.md).
It changes the concrete choice representation and its checked private resources.
The kernel, installation host, candidate validators and native proposal API are
unchanged.

The [signed-header successor](affine-empty-signed-installation.md) now adds
bounded negative-parameter acceptance through a condition-certificate client.
The generic encoder already supports signed intervals; the nonnegative limit
below describes this historical client profile.

## Choice and responsibilities

Write `O` for the outer-empty tree, `E` for the positive all-children-empty
tree, `R` for the exact empty-child restore, and `S` for the original loaded
loop. The previous target embedded `S` at every refusal leaf:

```text
capture;
select(O, skip, select(E, R, S))
```

The new target evaluates the readonly alternative into a private Boolean,
then has one occurrence of `S`:

```text
capture;
flag := short_circuit(O or E);
if (flag)
    select(O, skip, R);
else
    S;
```

The accepting branch repeats the small outer test to distinguish the two
public exits. It reads the captured root and original iterator; it does not
read M or body inputs. When O accepts, E is skipped and the original j/K
values remain observable. When only E accepts, R sets i to N, j to zero and
K to the last reached affine width. The condition's machine encoding,
original-source header receipts and no-leaf execution certificate are reused.
This proof does not execute the previous target at runtime.

| Layer | New responsibility and endpoint |
| --- | --- |
| Clight choice library | `readonly_alternative_selected_execution` factors the two readonly choices into one selected branch; `readonly_alternative_planned_execution` transports that branch through private Boolean evaluation |
| Site/domain producer | `affine_empty_snapshot_planned_captured_execution` reuses the original capture and empty-source receipts, preserves final memory and all live temporaries |
| Checked factory | Three typed private temporaries are required: root cache, child cache and Boolean result. `check_plan_resources` checks frameability and that the result occurs in neither condition reads, branch temporaries nor public live set |
| Host/installation | `affine_empty_snapshot_planned_prefix_contract` supplies the existing projected region contract; `compile_selected_empty_snapshot_planned_regions_correct` composes it through the selected host to Csem-to-Asm backward simulation |
| Framework | Existing local composition; no new semantic kernel obligation |

The result may be undefined before invocation: every completed check path
assigns it before dispatch. Its write is private and hidden by the projected
contract. The source user still supplies marked C and ordinary policy/profile
options, without completion, equivalence or model-correspondence callbacks.
The generic Clight alternative service does not inspect an affine expression
or schedule. The empty-loop client supplies the existing local execution
certificate and automatically checked resource evidence.

## Evidence

Four frozen modules, 263 lines, audit nine new endpoints, with 1,988 reachable
bindings, at most the same 42 inherited globals and no added axiom. Seven
archived source-build attempts comprise four successes and three rejected
proof sources. Existing successful proof sources and objects remain unchanged.

Both historical width matrices run the same 190 inputs in six configurations.
All 2,280 assembly and 2,280 independent Clight diagnostic calls match the
word model, all 12,000 array cells, public iterators and continuations. The
actual fast/fallback/unmarked path records equal the frozen expanded compiler's
records for every input. Each tested source function contains exactly one
original fallback loop, including all three marked functions. The marked
triangle previously contained 32. NULL body pointers, undefined body-only
words, header/data overlap and an unavailable M on an empty outer retain their
previous acceptance.

The same binary passes word 400/400, recursive-affine 480/480,
private-loaded 270/270, zero-width 672/672 and RMW 816/816 Asm/Clight calls.
Their historical path/configuration records remain identical; each normal RMW
mode retains 126 fast and 146 fallback calls. These checks do not merge the
families' semantic domains.

This removes repeated fallback statements; the condition still uses a finite
logical decision tree and tree-shaped Boolean assignments. It does not prove
a general linear bound on generated condition size, minimize the condition,
or establish a runtime speedup. The accepted branch's repeated outer test is
part of the new actual execution proof.

A premature extraction invocation is retained in
`build/affine-empty-plan/compiler-build-v1.json`: the proof audit report was
not yet present, so extraction never began and no compiler output was created.
The subsequent build is separately recorded. It is not a compiler failure.

## Remaining work

The nonnegative header-parameter profile remains: `i-M` can have negative child
widths, but positive-root `i+M` with negative M still falls back. Existing
candidate builders keep static priority; a site already handled by them does
not receive this new runtime empty alternative. Safe signed-header encoding
and runtime composition with the actual existing candidate are next, followed
by general recursive loaded domains, broader scalar/chunk services, complete
cost and combined OLO/BT coverage. The full goal remains active.

## Reproduction

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_affine_empty_plan.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_affine_empty_plan.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_affine_empty_plan_regression.py
```

Extraction uses `scripts/build_affine_empty_plan_compiler.py` and refuses to
overwrite the compiler checkpoint. Immutable checkpoints:

- Proof: `build/affine-empty-plan/proof-v1/report.json`
  (`d434f1e7782c8883eb67d2ca6fccd6c126d947510e0383408408c98002a9ae0e`).
- Compiler: `build/affine-empty-plan/compiler-v1/ccomp`
  (`0e4f82b165b04dcaeb21f8c0392602118c57ed5421fc3625fb86436a0529ad64`).
- Native: `build/affine-empty-plan/native-v1/report.json`
  (`731c89361c5a95e6c069b802be42d52570949e90a09a5b2b25978d86179c9bb2`).
- Same-binary regression: `build/affine-empty-plan/regression-v1/report.json`
  (`8724d42a0a34d9c9d3b3d1645742644590081d626000caa81a1df47711dfee65`).
