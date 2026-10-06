# Top-down research track

This branch is reserved for top-down positioning and design notes that run in
parallel with the bottom-up implementation work on `main`.

The working object is **verified guarded transformation**: a transformation may
be correct only under a semantic condition; that condition is turned into a
safe executable guard; rejection falls back to the source fragment; and the
local result is lifted into whole-program verified compilation.

Polyhedral/CompCert integration is the first demanding instantiation, not the
definition of the framework.

Current notes:

- [Paper narrative](paper-narrative.md): intended framing as a small language-independent verified optimistic-transformation framework plus a substantive CompCert/Clight domain-specific optimization instantiation; separates framework, language, and optimizer responsibilities and records the claims to avoid.
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
