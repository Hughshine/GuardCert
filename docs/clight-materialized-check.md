# Clight checks that return a private Boolean

This language library supports a check that updates private temporaries,
finishes normally, and leaves a defined Boolean expression for dispatch:

```text
check_body;
if (result) candidate else source
```

It complements the existing scan host, whose raw body reports refusal with
`break`. The deep affine-nest guards already use the normal-returning form.
Their source and candidate proofs can therefore use the current semantic kernel
without converting their checks into a different control representation.

The minimal kernel is unchanged. The responsibility boundary follows the
[paper narrative](topdown/paper-narrative.md): local certificate composition is
generic; actual Clight check execution and installation are language services;
affine source/model correspondence, coverage, and candidate validity remain
domain obligations.

## Language interface

[ClightMaterializedCheck.v](../prototype/interface/ClightMaterializedCheck.v)
defines `materialized_check`, its actual execution relation, and
`materialized_host`. `describe_materialized_check body condition` checks the
body syntax and constructs a description that retains those exact expressions.
The supported grammar contains assignments to temps, sequencing, conditionals,
loops, and loop breaks. It excludes stores, calls, labels, returns, switches,
and other exits. A separate normal-outcome checker excludes breaks that escape
the check body.

This syntax check does not prove that loads or arithmetic are defined. The
guard certificate must establish `materialized_safe`: safety of each reached
primitive and definedness of the dispatch expression after every completed
check execution. `materialized_select_execution_exact` relates actual guarded
statement execution to actual check execution followed by the selected branch;
it places no termination assumption on that branch.

[ClightMaterializedCertificate.v](../prototype/interface/ClightMaterializedCertificate.v)
provides `materialized_execution_certificate`. The caller supplies, for every
entry in its domain, an actual finite check execution together with:

- the dispatch expression's Boolean value;
- agreement on the protected input ports;
- acceptance implying a premise at the **original** entry.

The library derives the inductive primitive-safety judgment and proves soundness
for every completed check execution. These derivations use the checked grammar
and Clight quiet determinacy. An existential execution receipt is thus an input
to a proved safety derivation, rather than the definition of safety.

No freshness claim is implicit in this API. The caller's frame proof must
protect the stated ports even though the check may write and read its own
result and counters. The concrete compiler also checks the allocated private
namespace and source placement.

## Local rule and installation

[ClightMaterializedPreservation.v](../prototype/interface/ClightMaterializedPreservation.v)
defines `materialized_preserving_rule live source`. Its user supplies the actual
candidate, check, entry domain and premise, protected ports, source temp writes,
guard certificate, and a conditional source-to-candidate execution theorem.

The latter compares source execution from the original entry with candidate
execution from the checked temps, given agreement on the protected ports. It
does not require the premise to be re-established at the checked entry. On
refusal, the language's structured-execution transport resumes the source with
the same public behavior. On acceptance, the supplied local theorem establishes
the candidate's memory and public-temp behavior.

`materialized_guarded_preservation` consumes these facts through the current
kernel's `guardify_preservation`. `materialized_preserving_region_contract`
then produces the existing language-specific projected region contract. The
whole-program host must still check scope, private resources, progress, and
placement and prove its program simulation. The local contract alone is not a
contextual closure or divergence theorem.

## Deep affine instance

[ClightAffineNestMaterialized.v](../prototype/interface/ClightAffineNestMaterialized.v)
instantiates this library for both existing single-pointer and multi-pointer
affine packages. It reuses their actual source-derived guard executions and
conditional candidate executions. The source IR is a recursive canonical nest:
child bounds are affine expressions of enclosing coordinates and stable temp
parameters, with real checked array operations in its leaf. This migration
does not introduce that IR or increase its body expressivity.

The domain is an actual finite normal source execution. A quiet-source transport
lemma obtains the execution under the chosen call semantics. It does not assume
the guard succeeds, that pointers are disjoint, or that arithmetic does not
wrap. Those facts are obtained on acceptance by the existing affine guard and
candidate proofs. Arbitrary divergent source regions and memory-loaded bounds
at arbitrary depth are outside this instance.

The single-pointer frame protects parameters, root controls, and public temps.
The multi-pointer package already checks that its parameters, pointers, and
root iterator belong to the public scope, so it uses the public scope as its
protected ports. Both instances keep the premise at the original entry.

[ClightAffineNestMaterializedCompiler.v](../prototype/interface/ClightAffineNestMaterializedCompiler.v)
keeps the existing untrusted proposal types and independent source/domain/
dependence/tiling checks, adds the actual materialized-check syntax checker,
and returns a certified guarded replacement or declines it.
[ClightGuardedAffineNestCompiler.v](../prototype/interface/ClightGuardedAffineNestCompiler.v)
collects a finite table of these rewrites and installs it through the existing
private-region host before the verified CompCert backend. Its public entry is
`compile_materialized_affine_regions`, with a Csem-to-Asm backward-simulation
theorem.

The new proof uses the existing guard-execution and candidate-local theorems;
it does not obtain local correctness by invoking the older stateful guarded
region theorem. Imports retain the older request record and its dependencies.
This is a concrete reuse boundary, not a measurement of total author effort.

Proof, extraction, and native validation have separate scripts:

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_affine_nest_materialized.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/build_affine_nest_materialized.py
python3 scripts/native_affine_nest_materialized.py
```

Each script writes to `build/affine-nest-materialized/`; the older affine-nest
reports and compiler outputs remain historical evidence. Current results and
remaining work are recorded in the [stage checkpoint](research-checkpoint-2026-10-06-materialized-affine.md).
