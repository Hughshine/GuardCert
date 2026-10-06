# Deep affine guards through the current certificate interface

2026-10-06. This stage connects the existing recursive affine-nest source and
candidate route to the current `GuardInterface` kernel. It adds a Clight host
for checks that write a private Boolean and return normally, certified single-
and multi-pointer factories, and an extracted Csem-to-Asm compiler. It does not
introduce the existing deep source IR or a new polyhedral transformation.

The narrative branch was fetched and checked at
`7d94d810685a691efbf07df734f5fad8abfb4724`. Main's
`docs/topdown/paper-narrative.md` and context note match that branch. The minimal
kernel cutoff is unchanged: local guarded correctness is generic; check
processing is a library; concrete program installation belongs to the language
host and needs actual site evidence.

## What was connected

The older deep route used a stateful projected encoding and a forward guarded
region theorem. Its generated check runs normal-returning Clight statements
that read memory and write private temps. The existing current scan host uses
an escaping break to report rejection and prohibits its raw body from accessing
the result temp. Applying that host to these checks would require a different
representation.

The new [materialized-check library](clight-materialized-check.md) provides
actual check semantics, an exact check/branch execution law, inductive
primitive safety, defined dispatch, and soundness for every completed check
execution. A source-derived actual execution receipt discharges these language
obligations through proved quiet determinacy. Protected ports and public state
remain explicit; the premise is anchored at the original entry.

| Responsibility | Actual work in this stage |
| --- | --- |
| Minimal kernel | Reuse `guardify_preservation`; no source change |
| Clight library | Three modules for normal-returning private checks, execution certificates, cross-entry local preservation and projected region contracts |
| Domain/optimizer | Reuse actual affine source decoding, mathematical profile, footprint/alias coverage and source-to-candidate proofs; instantiate those facts in the new certificate |
| Factory/site | Retain untrusted proposal types and independent candidate checking; additionally check the actual guard body and normal exit |
| Program host | Reuse private pool, scope/progress/placement checks, finite rewrite-table installation and CompCert backend simulation |

The new rule does not invoke the old stateful guarded-region correctness
theorem. It consumes `affine_package_guard_execution` /
`affine_multi_guard_execution` and `affine_single_candidate_local` /
`affine_multi_candidate_local` directly. The old request record and modules
remain imported dependencies; no source-file reorganization was needed.

The public entry is
`ClightGuardedAffineNestCompiler.compile_materialized_affine_regions`, with
`compile_materialized_affine_regions_correct`. The supplied source/candidate
policies remain untrusted, and the driver allocates 32 integer private slots.
The recursive interface admits finite depths subject to source, namespace,
profile, lowering and resource checks. The native fixtures in this stage are
two- and three-level nests.

## Proof and execution evidence

The required proof closure compiled under the current Rocq toolchain. The audit
checks 26 endpoints: 12 language endpoints and 14 domain/factory/compiler
endpoints, with 462 reachable proof sources and 982 bound source digests.
Language endpoints use at most the existing six CompCert assumptions. The
whole-program endpoint retains the existing 42 assumptions; there are no new
global axioms. The five abbreviated imported printer names were checked by
reflexivity against their qualified names before comparison with the historical
deep-compiler assumption list.

Extraction and OCaml compilation passed. The build binds proof sources and
objects, the exact entry, driver/extraction text, native proposal/oracle sources,
and build helpers. No unrealized extraction axiom remains.

The new compiler recompiled the two unchanged C fixtures:

- `examples/native_affine_nest.c`: 283 calls per configuration, complete array
  and all public loop-control outputs;
- `examples/native_affine_nest_multiple_pointers.c`: 570 calls per configuration,
  complete three arrays and public controls, distinct blocks and overlapping
  views.

Both fixtures ran six configurations: disabled, interchange, 2×3 tiling,
wrong reindex, invalid domain, and oracle resource limit. All **5,118 new
unmodified assembly calls** match the independent word model and GCC reference.
The valid configurations install real two/three-level candidates; the incorrect
and resource-limited ones retain the source. The unsafe chain exchange is not
installed, and the independent model includes a counterexample to that exchange.

Four further configurations instrument the **actual emitted Clight**, compiled
by GCC. Each single-pointer mode observes 72 candidate and 154 fallback calls;
each multi-pointer mode observes 66 candidate and 391 fallback calls. The latter
includes 38 shared-storage but disjoint-access accepts and 74 overlapping-access
refusals per mode. Undefined child/leaf parameters have zero guard reads, and
negative roots and empty final child exits are checked. These 1,366 instrumented
calls are separate from the unmodified assembly count. This stage has **no new
machine branch or guard-comparison-order probe**.

| Artifact | SHA-256 |
| --- | --- |
| `build/affine-nest-materialized/proof/report.json` | `24da7e890fb2014ddf3f680415dbdd45cad6273c28507e6cec649100377ca07d` |
| compiler `ccomp` | `e8b77ecae5cba25566c987841f5406e2f87e20f7b9226601e524d6f94fb81cd8` |
| compiler stamp | `a23e4c65d3dca3833bddc43c3b06f0131956de1b20a819711c3bec542ded2bce` |
| `native/report.json` | `3382d3075286ff9eefb7c0f4f80635dd8a3a78c77df3ff4db27b56e5eccd901f` |
| `native/branch-report.json` | `24f8266becce7268aa1bb062db69fb2e8856e592ca4772de5d09a7e74db5aff2` |

## Current objects versus historical reports

Some pre-existing deep `.vo` files had incompatible assumptions on the current
toolchain. Recompiling their closure also changed shared object digests. The
frozen cursor validator correctly refused the current `GuardInterface.vo`
against its saved digest; a direct load of the old cursor compiler then found a
stale consumer of `GuardMemoryParametricSourceDomain`.

The old proof/native reports and compiler binaries were not rewritten. The
separate `scripts/audit_cursor_after_shared_rebuild.py` recompiles the affected
cursor consumers and writes a current regression report, rather than silently
rebinding frozen evidence. That current regression passed: 535 reachable proof
sources compiled, the cursor endpoint still has the exact 42 assumptions, and
152 object digests differ from the frozen report after rebuilding its consumers.
Its report SHA-256 is
`5a3a1597201fa0d7f2725a63aef7111c20da8aea43273921a4c5bf9c621e78a9`.
The new materialized compiler's proof objects were checked to remain unchanged
by that regression. No old native matrix is rerun or added to this stage's count.

## Reproduction and remaining work

With the repository's pinned toolchain and inherited source manifests available:

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make native-affine-nest-materialized
opam exec --root=/tmp/guard-opam --switch=guard -- make affine-nest-materialized-cursor-regression
python3 scripts/validate_affine_nest_materialized.py
```

All new output is under `build/affine-nest-materialized/`. The validator checks
the exact proof/build/native bindings and, when present, the separate Clight
instrumentation report. The CompCert lock identifies v3.18; the upstream VERSION
file still self-reports 3.17 as recorded by the lock. It was not changed here.

The deep route has affine child bounds over enclosing coordinates and stable
temp parameters, real Mint32 array bodies and actual source-point pointer
separation scans. The dependent cursor route handles two-level compound loaded
headers and multiple observations. Their capabilities have not been combined
into arbitrary-depth loaded bounds or typed pointer-store bodies. General source
domain shapes, that combination, physical stability checks across body/header
buffers, P4 timing and same-example comparisons with prior work remain active.
Neither test counts nor the migration establish performance, total proof-burden
savings, general Presburger condition synthesis or novelty. The full goal is
not complete.
