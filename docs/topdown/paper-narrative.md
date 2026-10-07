# Paper narrative: verified optimistic transformation with a substantive CompCert case study

Date: 2026-10-05.

This note records the intended top-down presentation.  It deliberately separates
the small language-independent semantic kernel from the language- and
optimizer-specific work that gives the abstraction substance.

## 1. Central framing

The paper should be framed as **verified optimistic transformation** rather than
as a polyhedral-specific verifier.

The generic situation is:

```
source fragment S
candidate fragment T
semantic precondition P
executable guard G
```

with a conditional correctness argument

```
P -> T is equivalent/refines S
```

and a guard certificate

```
G accepts -> P.
```

A language/host instance provides a concrete realization of guarded choice and
proves that it has the required semantics.  The framework then derives
correctness of the versioned rewrite and composes accepted local replacements
into a whole-program transformation.

The framework does **not** claim to know how an optimizer discovers its
assumptions or why those assumptions make its candidate correct.

## 2. Why the framework alone is not the whole paper

The final composition theorem is conceptually simple.  If the paper stopped at

```
G accepts -> P
P -> T ~= S
-------------------------------
select(G,T,S) ~= S
```

it would risk looking like a thin semantic wrapper.

The contribution has substance only if the interface captures obligations that
real optimistic optimizations actually need, and if reusable verified services
remove proof/implementation burden across transformations.

The main case study therefore has two jobs:

1. demonstrate that the language-independent abstraction can express a realistic
   optimistic compiler transformation;
2. force the framework to confront the nontrivial issues that disappear in toy
   examples: machine arithmetic, conditional reads, alias/stability, private
   snapshots, entry-condition construction, guard simplification, fallback,
   control exits, repeated rewrites, and whole-program compilation.

The concrete CompCert/Clight instance is therefore part of the scientific
argument for the abstraction, not merely an implementation appendix.

## 3. Three responsibility layers

### 3.1 Generic framework responsibility

The language-independent framework should provide the reusable semantic and
composition infrastructure:

- an abstract language/host interface for code, checks, execution, observations,
  and guarded choice;
- certificates for executable conditions;
- conditional source/candidate correctness;
- accepted/refused entry relations when checks use private state;
- a clean boundary between local guarded correctness and host-specific installation into whole programs;
- composition of repeated certified rewrites;
- reusable condition-processing combinators where they can be stated
  independently of a particular optimizer or language.

The framework should not inspect concrete C syntax, machine pointers,
polyhedral schedules, or a particular assumption extractor.

For clarity, the **minimal semantic kernel** should be understood to stop at
local guarded correctness.  Concretely, its essential objects are the abstract
host/check semantics, guard certificates, conditional/preservation
certificates, and the theorems that compose them into a correct local guarded
replacement.  The read-only API is a convenient frontend; condition
composition, prefix scans, simplification, and assumption derivation are
reusable libraries above the kernel.  Whole-program installation is a
language/IR-host responsibility, even if a small generic record is retained as
a composition hook.

This cutoff is primarily a documentation and architecture boundary, not a
request to reorganize files immediately.  It should be revised only if a real
optimizer or host exposes a semantic obligation that cannot be expressed
without changing the kernel.

### 3.2 Language/IR instance responsibility

A concrete language instance explains what the generic objects mean and proves
the host laws once.

For the CompCert/Clight instance this includes, as needed:

- actual statement/check execution semantics;
- a concrete realization of abstract guarded choice;
- safety/definedness of check primitives;
- short-circuit/control behavior;
- private temporary allocation and freshness;
- public observation/frame/state relations;
- legal region placement, exits, labels, continuations, and progress/divergence
  obligations;
- connection of the transformed Clight program to the verified CompCert backend.

The concrete choice does not have to be syntactically an `if`.  It may use
nested conditionals, branches/goto, a private Boolean with shared exits, or
another control representation, provided the instance proves the same abstract
law.

Local-to-whole-program lifting should be described carefully.  GuardCert's
generic kernel establishes local guarded correctness; a language/IR host is
responsible for reusable region/boundary contracts and installation theorems,
while an optimizer and concrete rewrite site supply the corresponding region
guarantee and placement evidence.  The current open design question is whether
these host contracts should be factored into reusable clauses (state/frame,
memory, trace, control, progress/divergence, private resources) with
strengthening/weakening, rather than treated as monolithic context records.  See
[context lifting and boundary contracts](context-lifting.md).  This is a design
question to test against the existing Clight hosts, not a settled API rewrite.

### 3.3 Optimizer/transformation responsibility

The optimization supplies the domain-specific intelligence:

- recognize/select the source fragment;
- construct or propose the candidate;
- extract or propose the assumptions required by its modeling/transformation;
- show that those assumptions are sufficient for the candidate's correctness;
- provide any optimizer-specific derivation from local obligations to an entry
  precondition, or submit a result to a verified checker;
- provide transformation-specific local execution/model correspondence.

For a polyhedral optimizer these assumptions may include no-wrap, stable loaded
bounds, multidimensional address validity, non-aliasing, and bounded domains.
A different optimizer may expose completely different conditions.

The framework should not pretend these obligations can be inferred generically.

## 4. The important certificate chain

The paper should distinguish at least the following logical links:

```
C_opt:
  A -> candidate correct with respect to source

C_derive:
  B -> A
  (e.g. entry condition establishes all local/model obligations)

C_guard:
  executable G accepts -> B

C_host:
  concrete select(G,T,S) implements the abstract guarded-choice semantics
```

These compose to justify the rewrite.

The boundaries matter because the producers can be different:

- `C_opt`: optimizer proof or verified candidate checker;
- `C_derive`: polyhedral projection/range reasoning/SMT/abstract
  interpretation/domain library;
- `C_guard`: verified condition compiler and language primitives;
- `C_host`: language/IR adapter.

The generic kernel consumes certificates; it need not trust the algorithms that
propose candidates or conditions.

## 5. Assumption extraction stays optimizer-specific

An optimizer may generate many local assumptions:

```
Q1(site/state), Q2(site/state), ..., Qn(site/state)
```

and separately prove that their conjunction is enough for its model and
transformation.

The framework should not define a universal function

```
extract_assumptions(source,candidate)
```

and should not claim to infer weakest preconditions for arbitrary program pairs.

A useful domain library may nevertheless automate a recurring middle step:

```
local obligations
   -> entry semantic condition
   -> simplified/strengthened checkable condition.
```

For optimistic polyhedral compilation, Presburger projection is one such domain
algorithm.  For other transformations it might be range analysis, symbolic
execution, shape reasoning, or a transformation-specific construction.

This is a library/plugin boundary rather than the semantic kernel.

## 6. Condition processing is partly reusable and partly domain-specific

The framework can make condition handling a first-class verified pipeline
without claiming that every step is universal.

Potentially reusable mechanisms include:

- Boolean composition and short-circuiting;
- dependent checks, where a later check is safe only after an earlier one
  succeeds;
- conservative refusal/unknown;
- certified strengthening rather than requiring logical equivalence;
- residualization under certified static facts;
- repeated-probe elimination;
- safe lowering with private temporaries;
- generic installation and fallback.

Domain-specific services may include:

- Presburger projection and simplification;
- affine footprint/range construction;
- arithmetic range propagation;
- model-specific alias conditions;
- optimizer-specific cost/acceptance heuristics.

Language-specific services include:

- checked arithmetic in the language's machine semantics;
- actual pointer/load operations and their definedness;
- concrete control-flow lowering;
- preservation of public state and events.

This separation should be explicit in the paper so that "framework" does not
silently absorb work still performed by an optimizer author or language adapter.

## 7. Repeated application is an important framework payoff

A user pass may choose locations and candidates using arbitrary heuristics.
Correctness should be local to each accepted rewrite.

Conceptually:

```
P0 ~= P1
P1 ~= P2
...
Pn-1 ~= Pn
```

where each step is produced only after its local certificates pass.

Then any **finite sequence** of successful applications composes to a correct
whole-program transformation.  The search/traversal strategy may be untrusted
with respect to semantic correctness; it affects which optimizations are found,
their profitability, and whether the compiler terminates, but not the semantic
validity of a produced finite rewrite sequence.

This is stronger and more useful than proving one hard-coded guarded example.

The paper should be precise here: it is arbitrary finite repeated application,
not a claim that an endlessly running optimization pass is itself a valid
compiler output.

## 8. The main evaluation should be a demanding high-level compiler instance

The paper should use CompCert/Clight plus a domain-specific loop/polyhedral
optimization as the principal instantiation.

The case study should include both the optimization algorithm and its
conditional correctness proof, not only guard insertion around a pre-proved
candidate.

The ideal end-to-end story is:

```
real C input
   -> Clight source region
   -> optimizer/model proposes candidate + local assumptions
   -> verified conditional correctness
   -> derivation of an executable entry condition
   -> verified guard construction/simplification
   -> guarded source/candidate versioning
   -> repeated application in a pass
   -> CompCert verified backend
   -> assembly
```

The point is not that the generic framework understands polyhedra.  The point is
that a realistic optimizer can instantiate its obligations and obtain the rest
of the verified optimistic-transformation infrastructure.

The strongest examples should exercise the reasons the abstraction exists:

- loaded bounds that can only be read conditionally;
- alias assumptions needed to justify stability;
- machine-integer/control/address correspondence;
- private cached parameters;
- real loop reordering/tiling rather than algebraic toy rewrites;
- safe fallback on failed/unknown checks;
- condition simplification without changing the transformation proof;
- multiple guarded rewrites in one function;
- preservation of public exits/state through CompCert.

### Functional coverage and usability: implementation order

Clarification from the 2026-10-06 discussion: first complete the proof chain for
the agreed implementation scope, then improve condition derivation and guard
generation. A certified scan is a valid intermediate implementation; there is
no need to interrupt that proof work merely because its checks are expensive.
This sequencing does not make efficient condition handling an optional polish
item or require completing every roadmap extension before improving guards.

[Optimistic Loop Optimization (CGO 2017)](https://pollylabs.org/publications/grosser-2017-Optimistic-Loop-Optimization.pdf),
especially Figures 2a–2b and Sections 5–7, is a functional and usability
reference as well as related work: assumptions are generalized to parameter
conditions, simplified, and checked with measured runtime cost. Within our
declared scope, the target is an end-to-end usable optimizer with mechanized
guarantees. Assess automatic condition handling and per-instance manual work,
not just whether one guarded example can be proved.

Keep three guard properties separate: generated code size, runtime checking
cost, and the useful inputs accepted. Replacing an unrolled scan with a cursor
loop reduces code growth but does not eliminate per-point work. For supported
affine obligations, pursue compact entry checks through verified projection,
range/footprint reasoning, or certified sufficient-condition proposals; retain
scans or conservative refusal where justified. Mathematical projection alone
does not establish safe machine arithmetic, pointer observations, or dependent
reads. A replacement guard must prove safety, acceptance implying the required
semantic obligations, and entry-state transport; it should reuse the existing
candidate and host proofs where their contracts still apply. Identical old/new
acceptance sets and globally minimal conditions are not required.

Use selected C examples and benchmark kernels from the CGO 2017 work to compare
the source problem, required assumptions, enabled transformation, guard cost,
and acceptance. Record source adaptations and attribute gaps to frontend/source
coverage, condition algorithms, unfinished proofs, or a specific semantic
difference. LLVM/Polly and CompCert/Clight need not produce identical guards or
support every same program, but verification alone does not explain a
functional gap. Correctness, functional coverage, and usability are separate
acceptance criteria; this note does not claim that the comparison or cost
evaluation is already complete.

## 9. How to present generality

The main body should not attempt to demonstrate every possible application
domain.

A restrained statement is:

> The framework is language- and transformation-independent at its semantic
> boundary.  Our principal instantiation is CompCert/Clight optimistic loop
> optimization; other transformations can use the same interface by supplying
> their own semantic preconditions, conditional-correctness certificates, and
> host-specific executable guards.

Potential examples for discussion/related work include runtime alias
disambiguation, vectorization under alignment/alias conditions, arithmetic
rewrites under no-overflow conditions, type/layout specialization, and guarded
library fast paths.

These illustrate the interface; they should not be presented as evaluated
capabilities unless implemented.

### Cross-IR applicability and related-work perspective

The same semantic interface should also admit lower-level hosts when useful.
For example, a three-address/SSA instance could interpret `code` as CFG regions,
`check` as a decision-producing CFG fragment, and guarded choice as a
conditional branch with appropriate live-out/phi/state relations.  An assembly
instance could expose registers, flags, memory, and control exits, allowing a
peephole or superoptimization rule to use runtime conditions while the host
proves that scratch registers/flags and branch control satisfy the abstract
choice contract.

This is not a main implementation goal for the current paper.  The CompCert/
Clight instance should remain the primary evaluation because it exercises the
high-level source-definedness and structured-control obligations that motivate
the current design.

Related work nevertheless helps explain why the abstraction should not be tied
to Clight syntax.  In particular:

- **Peek** is an important precedent for verified local rewrite-to-whole-program
  lifting at the assembly/peephole level.  It motivates comparison of host and
  contextual-proof responsibilities, while its central contribution is not
  runtime optimistic guarding.
- **COVE/cSTOKE** is a direct precedent for conditional equivalence and runtime
  selection of x86 candidates.  It shows that the same source/candidate +
  condition pattern arises at assembly level; GuardCert should compare its
  verified executable-condition and host boundary rather than claim that
  runtime-conditioned assembly optimization is new.
- **Chamois** and **CoreJIT** remain relevant for lower-level block simulation
  and verified dynamic assumptions/deoptimization, respectively; their exact
  interfaces should constrain any claim that GuardCert uniquely provides
  language-independent local-to-global or speculative transformation support.

A second concrete IR instantiation may be useful later as a validation of the
host abstraction, especially if it exposes an obligation absent at Clight
(e.g. flags/scratch registers at assembly level).  It is optional evidence, not
a prerequisite for the current main contribution.

## 10. Contribution structure for the paper

A plausible two-part contribution structure is:

### Contribution A: language-independent verified optimistic transformation

A semantic interface and proof architecture that separates:

- optimizer-specific conditional correctness;
- executable evidence for semantic preconditions;
- language-specific safe guarded choice;
- contextual/whole-program composition;
- repeated certified rewrites.

The novelty argument cannot simply be "conditional equivalence plus an if".
It must rest on the exact reusable services and proof boundaries after direct
comparison with prior verified rewrite/speculation systems.

### Contribution B: substantive CompCert/Clight instantiation

A verified optimistic loop/domain-specific optimizer that demonstrates the
framework on real C input and actual CompCert memory/control semantics, including
difficult dynamic conditions and guard implementation, and composes through the
backend to assembly.

This instantiation is evidence that the generic abstraction has realistic
expressive power and that its separation of responsibilities removes duplicated
verification work.

## 11. Suggested paper organization

One possible narrative:

1. **Motivating optimization.**  Present one realistic transformation that is
   profitable/natural but blocked by dynamic semantic preconditions.
2. **Problem decomposition.**  Show why conditional correctness, executable
   checking, safe fallback, and whole-program insertion are distinct proof
   obligations.
3. **GuardCert framework.**  Introduce the language-independent certificates and
   composition theorem.
4. **Condition services.**  Present the reusable construction/composition/
   strengthening/simplification mechanisms that actually remove user burden.
5. **CompCert/Clight realization.**  Show how the abstract host and guard
   semantics are implemented at a structured C-like layer.
6. **Domain-specific optimizer instance.**  Show assumption extraction,
   conditional optimizer correctness, and how the optimizer discharges the
   framework obligations.
7. **Evaluation.**  Measure correctness coverage, proof reuse, acceptance,
   guard cost, code growth, compile time, and performance separately.
8. **Related work/discussion.**  Position the generic boundary and explain where
   other transformation domains could instantiate it without claiming they have
   been evaluated.

This ordering keeps the framework and case study as one argument rather than two
loosely connected projects.

## 12. Claims to avoid

Do not claim, unless future work establishes them:

- generic automatic assumption extraction;
- weakest-precondition inference for arbitrary source/candidate pairs;
- generic optimal guard synthesis;
- that any semantic proposition can be compiled into a runtime check;
- that local conditional equivalence automatically gives whole-program
  correctness without a language host;
- that a large number of input calls is evidence of optimizer generality;
- that source-level/Clight placement is by itself novel;
- that the generic composition theorem alone is enough to support the paper.

The intended claim is instead that the framework provides the reusable verified
boundary around domain-specific optimistic transformations, and that the
CompCert case study demonstrates that this boundary is strong enough for a
realistic optimizer.
