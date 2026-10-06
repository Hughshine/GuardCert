# C/Clight as the first GuardCert host

Date: 2026-10-05.

GuardCert's generic semantic theorem need not be tied to C, but the first serious
evaluation is not merely "the same framework at a different IR".  Working at
CompCert's structured C-like layer (Clight, reached from real C input) changes
what conditions are observable, what checks are safe to execute, how private
state is introduced, and what can be inherited from the verified backend.

## 1. Separate the generic kernel from the guard host

The generic object remains:

```
semantic condition A
A -> candidate refines source
executable guard G
G accepts -> A
G preserves/restores the source-visible entry on refusal
---------------------------------------------------------
if G then candidate else source  refines source
```

The C/Clight-specific part should enter through a **guard host** interface, not
through the statement of conditional equivalence itself.

A host determines at least:

- which entry observations are actually available to generated code;
- which operations may be used to implement checks;
- the definedness/effect semantics of those operations;
- how fresh private temporaries are introduced and hidden from the context;
- where a region may be entered/exited and how structured control is preserved;
- how the local result composes with the rest of compilation.

This makes the host stage a first-class design dimension.  The same semantic
condition may admit different executable guards at Clight, RTL, LLVM IR, or
assembly.

## 2. Observable facts are different at C level

A proof may mention semantic facts that generated C/Clight code cannot directly
observe.  In CompCert memory, for example, proofs can reason about block
identity, permissions, offsets, and injections.  A C-level guard cannot simply
"read the block id" or inspect proof metadata.

Therefore condition synthesis should be parameterized by an **observation
algebra** whose atoms have actual Clight realizations and safety proofs.

This is especially important for aliasing:

- semantic non-aliasing may be easy to state using blocks/ranges;
- source-level pointer equality is not a general byte-range disjointness test;
- relational comparison of unrelated pointers is not a portable replacement
  for an abstract address-ordering oracle;
- object extent or allocation metadata is unavailable unless the source program
  already carries it or the compiler introduces a justified representation.

A condition can be mathematically sufficient but still be unimplementable at
the chosen host level.

## 3. Guard definedness is source-semantic, not just Boolean correctness

At a structured C-like layer, moving a read into an entry guard can evaluate
something on a path where the source program would never evaluate it.

Thus the guard compiler must prove more than

```
boolean result = formula value.
```

It must prove that each executed check operation is defined on the path where it
is executed.  A typical case is:

```c
if (n > 0)
    use(*p);
```

A guard may not unconditionally preload `*p` merely because the final semantic
condition mentions its value.  It must first establish the source/path fact that
makes the load admissible, or conservatively refuse before loading.

This is the C/Clight analogue of the preload issue in Doerfert--Grosser--Hack
CGO 2017, but in GuardCert it becomes an explicit mechanized host obligation.

The same point applies to:

- arithmetic whose check can itself overflow or otherwise be undefined;
- volatile/atomic observations;
- evaluation order and short-circuiting;
- loads whose permissions or addresses are only established by earlier tests.

## 4. Fresh locals are more visible than in SSA

At LLVM/SSA or assembly level, creating temporary values for a guard is routine.
At Clight, versioning may introduce fresh temporaries, private Boolean results,
snapshots of loaded bounds, or addresses while preserving:

- lexical/local-environment lookup;
- labels and `goto` behavior;
- public live-out temporaries;
- source-visible memory;
- continuations and exits.

The natural proof device is a projection or state relation that forgets
guard-private state.  "The guard is read-only" is too strong for some useful
lowerings and too weak as a semantic explanation: a lowering may write fresh
private locals while leaving all public observations unchanged.

## 5. Structured control is an advantage and an obligation

Working before three-address-code lowering retains structured loops and
conditionals.  This can make the intended guard placement and the scope of a
dynamic assumption much clearer than reconstructing a region from CFG code.

It also creates explicit host obligations:

- the selected region must have legal entry/exit structure;
- an external `goto` must not accidentally jump into the middle of a newly
  versioned region;
- loop exits and public iterators/live-outs must be restored exactly as required;
- a guard inserted before a structured region must dominate only the executions
  for which its observations are safe.

This suggests that GuardCert should distinguish the **semantic condition** from
the **placement proof** for a particular host.

## 6. C-level evaluation can preserve information lost downstream

CGO 2017 is motivated partly by semantic information lost or weakened at
LLVM-IR: multidimensional structure, static-control information, language-level
bounds, and source evaluation intent may be harder to recover at a low-level IR.

A Clight-level instantiation may sometimes derive a different or cheaper
condition because structured control, source types, and object-level information
are still available.  This should be tested rather than assumed: Clight is
already a compiler IR and still uses CompCert's explicit memory semantics, so it
does not preserve every ISO-C source fact automatically.

A useful evaluation question is therefore:

> For the same optimization, which assumptions/checks are necessary when the
> guard is synthesized at Clight versus after lowering?

This could make the choice of host stage an empirical/result dimension rather
than only an engineering detail.

## 7. Backend composition is a real systems advantage

If source-to-guard lowering and guarded transformation are proved at Clight,
then the existing CompCert backend correctness theorem can carry the transformed
program to assembly.

This gives the evaluation a concrete end-to-end claim:

```
real C input
 -> Clight guarded transformation
 -> verified CompCert backend
 -> assembly
```

The guard itself is therefore not a hand-written C snippet compiled by an
unverified side path.  Its actual Clight execution is part of the proof chain.

This does **not** make "working at C level" a novelty claim by itself; source-level
guard synthesis, contracts, and verified C transformations all have prior work.
Its value is that it changes the trusted boundary and the executable-condition
problem in a way that should be made explicit in comparison with low-level
systems.

## 8. Limitations of choosing C/Clight as the first host

Some optimizations depend on facts that are naturally available only later:

- concrete alignment/address bits;
- target ISA features;
- register allocation facts;
- exact machine instruction costs;
- backend-introduced control/data flow.

A general GuardCert framework should therefore not equate "guardable" with
"guardable in Clight".  The host interface should permit future lower-level
instances, or allow a semantic condition to be residualized until a later stage.

## 9. Positioning consequence

The first GuardCert paper should probably say two things simultaneously:

1. the semantic architecture is host/language general;
2. the main evaluation deliberately chooses a structured C/Clight host and
   proves actual source-level guard execution through the CompCert backend.

The interesting contrast with CGO 2017/COVE/CoreJIT/low-level verified rewrite
systems is then not merely syntax level.  It is:

- what runtime facts can be observed;
- whether guard evaluation itself can introduce source-level undefined behavior
  or extra effects;
- how private guard state is hidden;
- how region placement interacts with structured control;
- and whether the generated check is inside the end-to-end verified compilation
  chain.
