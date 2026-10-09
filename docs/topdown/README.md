# Top-down research track

Imported review snapshot from `topdown/research-positioning` at
`39df0d0a40c2c16642b4e4ed91fd8137a87a46c6`. The notes retain their reviewed
`cf4d442` implementation boundary. Decisions and subsequent implementation are
tracked in [the synthesis](../review-synthesis-2026-10-05.md) and
[the current work plan](../current-work-plan.md).

This branch is reserved for top-down positioning and design notes that run in
parallel with the bottom-up implementation work on `main`.

The 2026-10-08 acceptance decision, synchronized from `8ce9c8b`, prioritizes PolCert and CGO 2017
functionality, sequential optimization effects and benchmark alignment, with
mandatory whole-program Csem-to-Asm correctness. The [current work plan](../current-work-plan.md)
and [functional target](../polcert-integration-target.md) give the case-based
implementation order; [context lifting](context-lifting.md#delivery-requirement-2026-10-08)
fixes the installation requirement. Explicit SCoP selection and the real
optimizer pipeline remain required. The CAV 2027 [working manuscript](../../paper/README.md)
continues alongside implementation. Earlier imports and integration reviews
retain their historical implementation boundaries.

The [pinned inventory and work order](../benchmark-alignment.md) retain all 62
PolCert cases, including 19 with saved concurrent best routes, and identify the
serial NPB sources. This is source inventory evidence; the complete original-case
comparison has not run.

The working object is **verified guarded transformation**: a transformation may
be correct only under a semantic condition; that condition is turned into a
safe executable guard; rejection falls back to the source fragment; and the
local result is lifted into whole-program verified compilation.

Polyhedral/CompCert integration is the first demanding instantiation, not the
definition of the framework.

Current notes:

- [Paper narrative](paper-narrative.md): subsequent design note imported from
  `8c098ed`; a small semantic framework and a substantive CompCert optimizer
  instance form one argument. Assumption extraction remains optimizer-specific.
- [Context lifting and boundary contracts](context-lifting.md): open design note
  imported from `8c098ed`; language installation theorems, optimizer guarantees,
  site requirements and clause reuse. The current-code response is
  [the Clight contract review](../clight-boundary-contract-review.md).
- [Review of main at cf4d442](main-review-cf4d442.md): source-grounded assessment
  of the existing abstract choice, read-only front end, concrete lowering,
  dependent condition services, conditional-progress gap, and evaluation scope.
  This is a code/document review, not a new build or test run.
- [Abstract guarded choice](host-control-structure.md): a language instance
  implements and verifies conditional semantics; concrete if/while/goto syntax
  is transparent to the generic framework. The pinned main review identifies
  where this design is already implemented.
- [C/Clight as the first guard host](c-level-host.md): why evaluating and
  lowering guards at the structured C/Clight layer changes the design compared
  with three-address code, LLVM IR, JIT IR, or assembly. These concrete semantic
  obligations belong to the language adapter, not the generic choice kernel.
