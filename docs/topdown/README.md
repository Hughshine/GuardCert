# Top-down research track

This branch is reserved for top-down positioning and design notes that run in
parallel with the bottom-up implementation work on `main`.

The working object is **verified guarded transformation**: a transformation may
be correct only under a semantic condition; that condition is turned into a
safe executable guard; rejection falls back to the source fragment; and the
local result is lifted into whole-program verified compilation.

Polyhedral/ComSert integration is the first demanding instantiation, not the
definition of the framework.

Current notes:

- [C/Clight as the first guard host](c-level-host.md): why evaluating and
  lowering guards at the structured C/Clight layer changes the design compared
  with three-address code, LLVM IR, JIT IR, or assembly.
