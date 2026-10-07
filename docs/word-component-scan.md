# Source-Licensed Word Component Scans

This stage extends the loaded tensor first-point service through one complete
literal-bound component loop. It preserves exact signed32 word arithmetic,
including variable products, while the executable scan uses private coordinates.
It does not install the complete loaded tensor optimizer.

For a source store `p[index] = rhs`, the optimizer instance supplies a coordinate
renaming, source and scan bindings, protected temporaries, observer receipts,
and a reached original-source prefix. These are internal proof-service inputs.
A data-only factory for this new family still has to derive its static syntax
and freshness evidence; it is not an additional set of semantic callbacks that
an end user is expected to fill in.

`word_rename_evaluation` and the sound/complete `word_evaluate` lemmas interpret
the supported const/temp/add/sub/mul grammar in CompCert's modular int32
semantics. Renaming requires matching values for the coordinates read by the
expression. It does not require a globally injective identifier map or a
mathematical no-wrap fact. Pointer resolution remains distinct from permission.

`word_component_point_domain` obtains the next actual source store from the
remaining source execution. The store licenses the corresponding pointer
comparison at the guard entry, using permission preservation through preceding
stores. Actual captured observations license the other operands. No future
access or cached-source execution is supplied to license this point.

The point condition accepts only when that store is separated from every
observed header cell. Acceptance proves preservation of their captured raw
values. `word_component_prefix_advance` then advances the actual source prefix
and exposes the next source store. A refusal stops the scan before that advance.

`word_component_scan_execution` proves actual Clight execution of a private
cursor loop, including its literal-limit initialization, Boolean result, memory
preservation, protected-temporary frame, and complete coverage on acceptance.
It consumes an initialized incoming success flag. The loop has one copy of the
point check; its runtime work still grows with the component count.

`word_component_accepted_source_transport` closes the next connection. Complete
acceptance supplies every component's observation-preservation law. The existing
expression-body transport library then derives actual cached-loop execution
with the same trace, exit temporaries, memory, and outcome as the original
literal-bound loop, and preserves all snapshots. The original execution is an
input to this transport theorem, rather than an assumed cached-model execution.

The fixtures allocate real CompCert memory, place two headers and data in the
same allocation, and execute five actual source stores. Their index uses the
wrapping product `2*MAX`: exact word evaluation yields `5+k`. With pointer base
16, the stores address bytes 36 through 52 and the actual scan accepts. With
pointer base -20, the first store aliases the root header and the actual scan
refuses. The scan preserves source coordinates through its private cursor.
Neither fixture claims that the wrapping input passes later no-wrap/model checks.

## Responsibility and Evidence Boundaries

| Layer | Work in this stage |
| --- | --- |
| Minimal kernel | Existing certificate composition; no changed definitions or new primitives. |
| Clight library | Exact word execution/renaming, permission transport, read-only point checks, private scan execution, and cached-loop transport laws. |
| Optimizer instance | Source-prefix wiring, coordinate/scope bindings, captured observations, accepted-point preservation and original component transport. |
| End user / proposal checker | No new compiler entry in this stage; the new family's data-only checker/factory remains pending. |

The independent audit is `scripts/audit_word_component_scan.py`; it validates the
unchanged first-point parent before and after querying the new endpoints.
`scripts/build_word_component_scan.py` runs extracted word evaluation and scan
construction. These extracted cases do not execute generated Clight or assembly;
the Rocq fixtures provide the actual source and scan execution evidence.

The audit queries 40 endpoints over 447 dependencies. Fifteen endpoints are
closed; the others use at most six globals from the existing CompCert baseline,
with no added axiom. The proof report SHA256 is
`b38e8a98058879c85c8908af900914ac23168d5b8422ecc97828a9380946083f`.
All ten extracted cases pass; their report SHA256 is
`1a952dc9d065733a87d53d2cd4b8dcb6e9ceb05ddb2e84302bd48f6fae5274e5`.

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_word_component_scan.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/build_word_component_scan.py
```

The remaining loaded/dynamic integration is explicit: derive inner/outer
prefixes for this word-address family, cover every reached component and row,
transport the full nested source to the canonical tensor model, connect numeric
and dependency checks and actual candidate entry/exit state, then install through
the language host and validate complete C acceptance/refusal/context execution.
This stage adds no whole-program compiler entry, native C matrix, or cost result.
