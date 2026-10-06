# Short-Circuit Cursor Scans for Dependent Affine Rows

This checkpoint addresses the first code-size obligation after the
[dependent-header compiler](research-checkpoint-2026-10-06-dependent-compiler.md).
It is a proof-library stage for readers integrating an optimizer with the Clight
host. The existing compiler still generates its previous sequential plans.

## Result and Boundary

The new Clight code scans a reached row with one private column cursor and one
private Boolean. Its body contains one copy of the address probes, independent
of the column cap. The cap occurs in the ceiling comparison. Logical unfolding
remains a proof specification; the runtime statement contains an `Sloop`.

The loop accepts when the activity test is false or the ceiling is reached. An
active probe that rejects exits before the next activity test, probe, or
increment. Only acceptance advances the cursor. Actual initialization writes
the Boolean and cursor, so their values need not exist at entry. Signed ceiling
and cursor bounds justify the machine comparison and increment.

For dependent affine rows, the specialized runtime probe is exactly the old
constant-column probe. The logical row specification is exactly the previous
`memory_affine_dependent_row_probe`. Its existing condition certificate supplies
availability from the reached-row domain. The new code has a finite, silent
execution, preserves memory and public temps, and satisfies the existing
primitive-safety judgment. Any completed execution returning true preserves
both the pointer-cell and bound-cell observations across each covered physical
write sequence, by the original row preservation theorem.

This is not a new optimizer factory, outer-loop scan, compiler entrypoint,
extraction, or native result. The earlier default 64×64 functions still have
20,710 and 20,711 `if` nodes. This checkpoint supplies the inner-row lowering;
removing that growth requires actual integration and new measurements.

## Responsibility Split

The fetched narrative remains at `7d94d810685a691efbf07df734f5fad8abfb4724`.
The local [paper narrative](topdown/paper-narrative.md) and
[context note](topdown/context-lifting.md) match that branch. Its minimal kernel
ends at local guarded correctness. This implementation adds language and domain
libraries without changing the kernel or reorganizing its files.

| Owner | New proof or service | Remaining integration obligation |
| --- | --- | --- |
| Minimal kernel | Existing certificate composition remains unchanged. | Consume the resulting local contract after installation is connected. |
| Clight library | Actual short-circuit loop, private initialization, cursor specialization, check-plan body, public frame, signed increment, primitive safety. | Connect checked scratch resources and the actual outer scan to host placement and dispatch. |
| Affine domain | Symbolic write-address template, specialization to the old dual-observation probe, exact row specification, accepted-row preservation. | Supply freshness/read scope from the checked package and typed pool; prove outer-prefix advancement and complete row coverage. |
| Existing language host | The dependent compiler remains a checked regression with its previous source progress and whole-program simulation. | Consume the new installed lowering and obtain a new extraction and native validation. |

The row theorem consumes the previous reached-row domain, including actual
write receipts and width coverage. It does not infer those facts from a runtime
cursor. The difficult outer obligation also remains: permission to check another
row must follow the source-prefix proof after both observations have been
preserved. A successful comparison at one point does not license arbitrary
future addresses.

## Proof Sources

- [ClightBoundedCheckLoop.v](../prototype/interface/ClightBoundedCheckLoop.v)
  relates the logical scan to actual initialization, short-circuit control and
  bounded signed increments. Its point callback is restricted to the reached
  interval.
- [ClightCursorSpecialization.v](../prototype/interface/ClightCursorSpecialization.v)
  transports expression/lvalue evaluation and decision-tree runs when the
  private cursor has the specified word. It tracks the remaining public reads.
- [ClightCursorCheckBody.v](../prototype/interface/ClightCursorCheckBody.v) and
  [ClightCursorBoundedScan.v](../prototype/interface/ClightCursorBoundedScan.v)
  reuse the existing check-plan lowering for the runtime point body.
- [GuardMemoryAffineCursorProbes.v](../adapters/compcert-memory/GuardMemoryAffineCursorProbes.v)
  proves that symbolic column addresses and both chunk probes specialize to the
  old affine conditions for nonnegative columns.
- [GuardMemoryAffineCursorRow.v](../adapters/compcert-memory/GuardMemoryAffineCursorRow.v)
  proves exact row correspondence, actual execution, availability, safety and
  observation preservation after actual acceptance.
- [ClightCursorScanExamples.v](../prototype/interface/ClightCursorScanExamples.v)
  proves that a first-point rejection leaves the cursor at zero, with both
  private slots initially absent. A later dereference is formally undefined;
  the rejected execution never evaluates it. This is a Clight semantic fixture,
  not a C frontend or machine experiment.

## Validation

Run `opam exec --root=/tmp/guard-opam --switch=guard -- make affine-cursor-scan-proof`.
[The audit script](../scripts/audit_affine_cursor_scan.py) compiles the selected
dependency closure and checks all printed endpoint assumptions. It binds the
previous dependent compiler report, its sources, compiled objects and parent
reports without rewriting them.

The incremental audit passed: seven new modules, 34 endpoints (23 language),
531 dependencies and 968 source digests. Every new endpoint has at most six
assumptions, all within the CompCert baseline. The independent existing
dependent-compiler theorem still has its original 42 assumptions. No additional
global axiom was introduced. This is not a clean rebuild of the entire closure.

Report: `build/affine-cursor-scan/proof/report.json`.
SHA-256: `dc4358e19c132f97841464a735f134dc1212ad5e75f7bfd53810ff1d2446c555`.
Parent proof report:
`c4b519808a8b2b4da82bfd9eec7e535bfa989eb121723b79e29d6cd9d2613391`.

Both existing dependent native validators passed again. They checked the frozen
compiler/proof/C/report bindings; the 444 calls and 28 machine probes were not
rerun and are not new cursor-scan evidence. No performance, profitability or
total proof-burden claim follows from this stage.

The next delivery is the complete outer scan and checked-resource connection,
followed by installation into the dependent factory, extraction, actual C
acceptance/refusal tests, and separate code/compile/execution cost measurements.
General deep affine sources, physical alias acceptance for distinct body bases,
legal pointer-store bodies and the same-example prior-work comparison remain in
the active goal.
