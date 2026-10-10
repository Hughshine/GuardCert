# Context lifting: local guarded correctness to whole-program correctness

Date: 2026-10-06.

This note records an open top-down design question.  It is intentionally not a
final API proposal.  The current implementation already has generic
`context_certificate`/`rewrite_context` boundaries and several concrete
Clight hosts; the purpose here is to make the semantic gap explicit and ask
whether the current factoring is the right one.

## Delivery requirement (2026-10-08)

The functional and benchmark target is PolCert plus CGO 2017, with concurrent
execution optional. Whole-program correctness is mandatory for the delivered
optimizer, not just a local or Loop-to-Loop result. Each supported compiler
configuration must connect its actual checked source, guard, candidate and
fallback to the successful-compilation Csem-to-Asm backward-simulation theorem
for the corresponding source `Csyntax.program`, within the existing CompCert
parsing/assembly/linking boundary.

Factories and site checks must establish the applicable invocation, scope,
placement, progress, typing and resource premises; source users do not supply
unproved semantic callbacks. Public state, memory, traces and control outcomes,
and private freshness/frame properties must support the actual continuation.
For repeated installation or passes, evidence applies to the current
intermediate program, not a stale source or site.

Reuse the existing finite or open Clight host according to the required
progress semantics; terminating-execution evidence alone cannot justify a
potentially divergent replacement. Extend those services only for a concrete
benchmark obligation. This acceptance requirement does not mandate re-proving
the whole compiler per benchmark, a new generic context algebra, a second IR,
or new axioms. The factoring questions below remain design questions, not a
reason to defer or assume the installation proof.

### Direct codegen delivery (2026-10-10)

The main polyhedral route connects the actual selected Clight source to its
PolCert model, validated model transformations, original codegen/cleanup and
proved Clight lowering, then consumes the existing region contract and
Csem-to-Asm installation. Candidate execution must be constructed at the same
captured parameters. Forward execution/existence and progress for generated
code, machine floor/min/max bounds, private-state transport and public exits
are concrete domain/language obligations; the host does not infer them.

Native semantic adaptation followed by re-extraction and matching against a
source statement list is no longer the default installation gate. Model-level
optimization validation remains required. A necessary post-generation change
must have a separate general execution-preservation proof; its actual output
must be consumed by lowering and the region contract. Existing static site,
scope, resource and placement checks still supply their language obligations.

The complete direct compiler is pending. Keep previous compiler definitions,
checks and reports as evidence for their own routes. Deleting a final check
does not complete candidate progress or installation. Reuse the current finite
or open host as required by the source and continuation, without inventing a
new host interface or postponing whole-program correctness to evaluation.

## 1. What must be lifted

GuardCert's most language-independent result is local:

```
guard correctness
+ conditional source/candidate correctness
------------------------------------------
local guarded replacement refines/preserves the source fragment
```

The compiler needs a program-level result:

```
C[target]  refines/preserves  C[source].
```

The implication is not automatic.  A local theorem can be conditional on an
entry domain, expose only part of the exit state, cover only selected control
outcomes, or say nothing about divergence.  A surrounding program may observe
exactly the state/control distinctions that a local theorem hides.

The local-to-global gap therefore includes at least:

- **entry/placement:** every actual entry to the replaced region must satisfy the
  local domain and must enter through a supported boundary;
- **post-state observations:** the continuation may read only state that the
  local replacement relates strongly enough;
- **memory/effects:** later code may observe memory or events not included in a
  weak local relation;
- **control:** normal completion, break/continue/return/goto, successor edges,
  and labels must be related in a way understood by the surrounding language;
- **progress/divergence:** a completed-run theorem cannot by itself justify a
  replacement when source or target can remain in the region forever;
- **private representation state:** fresh guard/cache temporaries, scratch
  registers, flags, or private memory may differ only when the context cannot
  observe those differences.

This is a language/IR installation problem, not another assumption-extraction
problem.

## 2. Concrete Clight example

Suppose the source function is schematically:

```c
x = 7;
SOURCE_REGION;
return x + a[0];
```

and the optimizer constructs:

```c
x = 7;
if (guard)
    CANDIDATE_REGION;
else
    SOURCE_REGION;
return x + a[0];
```

The local GuardCert theorem may establish only that the guarded region and the
source region have related exits.  To install the replacement, Clight must still
justify that the relation is strong enough for the continuation.

For example, a useful region guarantee can permit:

```
source exit:
    x = 7
    i = n
    memory = M

target exit:
    x = 7
    i = n
    _cached_bound = n
    _guard_result = 1
    memory = M
```

Raw Clight states are not equal.  The difference is harmless only if
`_cached_bound` and `_guard_result` are fresh/private and the continuation
cannot read them.  Conversely, if the target changed `x`, a local relation
that ignored `x` would be insufficient at this placement because the
continuation immediately observes it.

The current projected Clight host embodies one relatively strong choice:
selected live temporaries agree, memory satisfies the concrete
`memory_equivalent` relation, execution is silent, and the supported finite
region exits normally.  Private/fresh temporaries may differ.  This is not
literal whole-state equality, but it is also not the weakest possible
contextual interface.

The open-region host demonstrates a second important case.  A whole loop whose
fallback may diverge cannot be justified only by comparing completed region
exits.  It needs a small-step protocol that can match source steps indefinitely
and relates an exit only if one is reached.

These two existing hosts suggest that "context lifting" should not be presented
as one universal theorem with one fixed post-state relation.

## 3. Who should be responsible

A tentative responsibility split is:

```
generic GuardCert:
    prove local guarded correctness

language/IR library:
    define reusable boundary/region contracts
    prove installation theorems for supported host classes

optimizer/domain implementation:
    prove its concrete source/candidate satisfies a chosen region guarantee

site/placement analysis:
    prove the concrete surrounding context needs no more than that guarantee
    and that the region is legally placed
```

The important distinction is between a reusable **language theorem** and
per-rewrite **site evidence**.

The optimizer should not have to reprove, for every tiling/interchange rule,
that Clight continuations preserve a relation on live temporaries.  Conversely,
the language instance should not decide which temporaries or memory footprint a
particular optimizer preserves.

## 4. Boundary contract as guarantee versus requirement

A potentially cleaner model is to distinguish the region's guarantee from the
context's requirement.

Let `B` describe a boundary contract.  Then:

```
RegionGuarantee B source target
ContextAccepts  B context source target
```

and the language provides an installation theorem:

```
RegionGuarantee B S T
ContextAccepts  B C S T
--------------------------------
ProgramRefinement (C[T]) (C[S])
```

This makes "public boundary" site-relative: it means the observations that the
surrounding context may consume across this region boundary, not a globally
fixed set of public variables.

An optimizer chooses or instantiates a suitable contract and proves its
guarantee.  The placement/context side proves that the actual surrounding
program relies only on that contract.

It may be useful to allow the two sides to use different strengths.  If an
optimizer guarantees `G` and the context requires only `R`, installation is
valid when the language library proves:

```
G entails R.
```

For example:

```
TempAgree {x,y,z}  entails  TempAgree {x,y}.
```

This is analogous to conservative strengthening on the condition side.

## 5. Contracts likely share clauses

It is probably wrong to model every useful host as a completely separate
monolithic record.  Finite regions, shared-guard regions, open regions, CFG
blocks, and assembly peepholes can reuse many of the same boundary clauses.

Candidate reusable clauses include:

- **state/frame:** equality or agreement on a selected set of temps/registers;
- **memory:** exact equality, CompCert memory equivalence, framed memory
  differences, injections, or another host-defined relation;
- **trace/effects:** silence, trace equality, or a trace relation;
- **control:** normal-only exit, a relation on break/continue/return outcomes,
  successor-edge relations, etc.;
- **progress:** finite completion, lockstep/stuttering simulation,
  divergence-preserving open simulation;
- **private resources:** fresh temps, scratch registers/flags, private memory or
  stack slots;
- **entry facts:** scope, typing, legal entry points, and other facts needed to
  interpret the boundary.

Different useful contracts may differ in only one clause.  For example, a
finite Clight region and an open potentially-divergent region may share state,
memory, trace, and private-resource clauses while using fundamentally different
progress clauses.

There should therefore be some notion of clause reuse and perhaps
strengthening/weakening, rather than a proliferation of names such as
`NormalPrivateProjectedRegionContractV3`.

However, the clauses are not necessarily a free Cartesian product.  For
example, an exit-state clause has a different meaning under finite completion
than under an open simulation ("if an exit is reached").  A framed memory
relation can also depend on freshness/private-allocation conditions.  Any
"contract algebra" must account for such dependencies rather than assuming that
all clause combinations are valid.

## 6. Relation to the current generic context records

The existing generic `context_certificate`/`rewrite_context` records are
logically sound responsibility boundaries.  Their lifting field is essentially:

```
legal placement
+ admissible replacement
+ local refinement/equivalence
--------------------------------
whole-program refinement/equivalence
```

But this does not itself solve contextual closure: the difficult
`lift_refinement`/`rewrite_lift` theorem is supplied as a field by the host.
The generic theorem merely composes it with local GuardCert correctness.

This is acceptable as a minimal kernel boundary, but it may be too abstract to
serve as the main explanatory model in the paper.  In particular,
`legal_placement` and `admissible_replacement` are uninterpreted predicates;
all semantic work could be hidden inside the lifting field.

The concrete Clight implementation already appears closer to the more
structured model:

```
local guarded rule
    -> projected/open region contract
    -> scope/progress/freshness/placement evidence
    -> Clight transformation simulation
    -> CompCert backend
```

The top-down question is therefore not whether the current generic record is
sound, but whether the framework should expose a more informative host contract
structure above that minimal kernel.

## 7. Questions for the implementation/review agent

The next implementation review should answer these from the current code rather
than redesigning from taste:

1. Which clauses are actually duplicated across `projected_region_contract`,
   open-region protocols, shared realizations, sequence transport, and other
   Clight hosts?
2. Which differences are essential semantic differences (especially progress
   and control) rather than accidental API duplication?
3. Can the current hosts be factored around a reusable boundary relation or
   small set of clauses without weakening their theorems or increasing rule
   obligations?
4. What is currently optimizer-specific, what is site-specific, and what is
   already proved once by the Clight language library?
5. Does the current "live temps + memory_equivalent + silent + normal exit"
   boundary unnecessarily constrain realistic optimizations?  If so, identify a
   concrete currently-blocked transformation before generalizing it.
6. Would a guarantee/requirement plus entailment interface materially reduce
   duplicated proofs for current rules, or only rename existing obligations?
7. How should finite completion and open/divergence protocols share boundary
   clauses while retaining their different progress semantics?
8. For a future SSA/CFG or assembly host, which clauses transfer directly and
   which require genuinely different notions (phi/live-out, successors,
   flags/scratch registers, PC)?

Do not refactor the kernel solely to make the diagram prettier.  A change is
worthwhile only if the current CompCert cases demonstrate actual proof reuse,
cleaner optimizer obligations, or support for a previously awkward region
class.

## 8. Provisional paper wording

Until the design is re-reviewed, avoid saying that GuardCert "provides generic
context lifting."  A more accurate statement is:

> GuardCert proves local guarded-transformation correctness independently of
> program context.  A language/IR host supplies reusable region contracts and
> installation theorems that connect such local certificates to supported
> program contexts; each optimizer and rewrite site supplies the corresponding
> region and placement evidence.

This wording keeps the generic kernel claim precise while leaving room for a
richer, clause-based host-contract design if the implementation evidence
supports it.
