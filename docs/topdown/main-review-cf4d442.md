# Main review: abstract guarded choice, realization, and remaining proof boundaries

Reviewed snapshot: `cf4d44292cd1e834e79db31d0ac3a75696a7d40c` on `main`.

This is a source-and-document review, not a new Rocq build or native regression run. Implementation statements below refer to that pinned snapshot. Test and assumption-audit numbers are the repository's reported results, not independently reproduced results. Proposed interfaces and priorities are marked as design recommendations. No implementation files on main are changed by this note.

## 1. The main design already implements the proposed abstract choice

The user's intended boundary is semantic: a language instance provides a control structure behaving like an observationally pure conditional; its concrete implementation may use if, branches, goto, or a finite state machine. The generic framework should not inspect that representation.

This is already present in [`GuardInterface.v`][kernel]:

```coq
select : check -> code -> code -> code;
select_exact : forall test yes no entry observed,
  runs (select test yes no) entry observed <->
  exists accepted checked,
    checks test entry accepted checked /\
    runs (if accepted then yes else no) checked observed
```

The `if accepted` on the right is a Gallina selection between abstract code objects. It does not require an object-language if constructor. `code`, `check`, `observation`, `runs`, `checks`, and `check_safe` all come from the language instance.

The exact law is stronger than a construction-only rule: it excludes extra declared observations that cannot be explained by checking and then executing one branch. The law does not by itself settle what observations contain or how safety connects to concrete execution. Those remain host obligations.

**Assessment:** do not introduce a competing generic `choose` record. The conceptual boundary requested in our discussion has already been implemented. The next question is whether every concrete lowering consumes this boundary uniformly.

## 2. The public interface deliberately specializes the more general core

[`GuardedRewrite.v`][rewrite] defines:

```text
guarded_rewrite H source candidate condition
  = select H condition candidate source
```

Its `readonly_condition` requires safety, an available check execution, and, for every check execution on domain D:

```text
checked = entry
accepted = true -> P(entry)
```

Its conditional equivalence compares observations of the actual source and candidate under D and P. `guarded_rewrite_equivalent` composes these contracts.

The lower-level `guard_certificate` in `GuardInterface.v` additionally permits distinct accepted/refused state relations; `conditional_certificate` explicitly relates branch execution from the checked state back to source execution from the original state. Refinement and preservation have separate contracts and theorems.

The older [`StatefulGuard.v`][old-stateful] is not the same interface under another name: it supplies a conditional-introduction rule and an existential execution certificate for a source-to-target preservation theorem. The new exact dispatch interface supports stronger decomposition obligations. These layers should not be treated as interchangeable solely because all their names contain guard.

**Recommendation:** retain the small read-only front end for the current project. Do not require every optimization author to reason about arbitrary effectful guards. Keep the more general state relations as implementation/extension machinery where needed.

## 3. Concrete Clight choice is already verified, but has a stated semantic scope

[`ClightReadonlyRewrite.v`][clight-host] instantiates `guard_host` using:

- actual Clight statements;
- finite `decision_tree` checks;
- `tree_statement` as the selection constructor;
- `decision_run` with unchanged entry state as check execution;
- actual `exec_stmt` executions, optionally saturated by an observation relation, as fragment observations.

`readonly_tree_execution_exact` proves the decomposition required by `select_exact`. `readonly_tree_safe` requires every reachable expression test to have a result and requires safety after every possible result. Finite tree structure excludes internal check loops. This is substantially more than asserting that the Boolean formula is correct.

However, this particular `runs` relation uses completed big-step fragment executions. The language-independent type permits other observations, but this instance does not automatically acquire divergence coverage merely because `observation` is abstract. The full-program connection uses additional small-step/progress machinery.

**Design invariant:** the meaning of 'no extra effect' must include the declared traces and control outcomes, not just memory equality. A while/goto realization would need an actual finite, silent checking/dispatch proof on its admissible domain; syntactic representability is not sufficient.

## 4. A real representation-independence result already exists: shared exits

The direct tree lowering duplicates candidate and fallback bodies at leaves. [`ClightSharedGuard.v`][shared-code] instead emits:

```text
run the same decision tree, writing 0/1 to a fresh private result at a leaf;
if private_result then candidate else source
```

The raw temporary map changes. [`ClightSharedProjectedCompiler.v`][shared-compiler] proves freshness, source/selected-branch execution transport, public temporary agreement, and memory equivalence. It consumes the original read-only condition and projected local rule; the optimization's alias and scheduling proofs do not need to be repeated.

The existing implementation therefore already demonstrates the user's point: one abstract check and local rule can support materially different concrete control encodings.

There is nevertheless a remaining architectural distinction. The direct realization is packaged as `readonly_clight_host` with `select_exact`. The shared realization is implemented through separate `shared_projected_selected`, `shared_projected_region_contract`, and compilation-adapter proofs. It is not simply another interchangeable value of the same complete lowering-certificate interface. `ClightSharedGuard.v` supplies constructive execution lemmas, not by itself a second complete `guard_host` instance with the same exact semantics.

This is not an identified soundness bug. It is a modularity opportunity visible in the actual code.

**Recommendation:** factor a reusable certified realization boundary for abstract guarded choice. A realization should account for concrete code, private resources, freshness, a state/observation relation, and the simulation required by the compiler host. It need not demand literal equality of concrete states or full source/assembly equivalence. Direct trees, shared exits, and a future CFG/DAG lowering should consume the same read-only and local transformation certificates through this boundary.

Do not weaken `readonly_condition.checked = entry` silently to describe raw Clight writes. Maintain purity at the abstract level and prove how the concrete lowering realizes it.

## 5. The framework is doing more than packaging a versioning lemma

The generic choice theorem is small. The more substantial reusable services currently visible are:

### Dependent checking

[`ReadonlyConditionComposition.v`][stages] requires a language-provided `readonly_check_algebra`: constant checks, sequential checks, exact execution laws, and safety laws. The framework then proves:

```text
first  : CheckCertificate(D, P)
second : CheckCertificate(D and P, Q)
----------------------------------
first then second : CheckCertificate(D, P and Q)
```

Thus a later check can use facts established by an earlier accepted check to justify its own execution. Check order is supplied; it is not an automatically inferred optimal ordering.

### Branch evidence and prefix scans

[`ReadonlyPrefixScan` documentation][prefix] describes a generic bounded generator with activity classifiers, point checks, and a ghost invariant transported between points. The actual indexed and nested memory-bound instances consume it.

The important distinction is that the runtime guard stays at the same entry memory. The source-execution cursor, access permissions, and stability witnesses advance in the proof, not by running the source program at runtime.

The generator's zero-fuel result is acceptance of the bounded prefix already represented. It does not mean 'all source accesses have been checked'. A separate coverage theorem is essential. Non-activity at one point also needs a suitable domain property before it can stand for the end of all relevant activity.

### Probe simplification

[`ReadonlyProbeTree` documentation][simplifier] describes a language-independent optimization based on equality of opaque probes and determinacy at the same entry state. A previous actual Boolean test result removes later tests of the same probe. Its concrete Clight instance uses expression syntactic equality.

This preserves the same D, P, candidate, and local proof, and proves execution-result equivalence and safety. It does not infer arbitrary arithmetic implications between different expressions, create an arbitrary shared DAG, or treat guard rejection as proof of not-P.

**Assessment:** these services are a more informative description of the framework's current direction than 'a general if theorem'. They support a program of verified construction, composition, optimization, and realization of executable evidence.

## 6. Condition discovery and symbolic projection remain different from these services

[`AssumptionDerivation.v`][derivation] provides actual-position obligations (`site_occurs`, `site_holds`), collected requirements, existential violations, and:

```text
collected_obligations <-> not projected_violation
```

It also supplies an `entry_derivation` certificate, one-way strengthening, and a theorem connecting the derived entry condition to actual guarded rewriting.

The file does not implement Presburger quantifier elimination or a general source/candidate precondition discovery algorithm. The projection theorem is a logical characterization; `entry_derivation` is a certificate interface. An external solver may propose a condition, but the certificate or a verified checker must still establish its implication.

The current [OLO acceptance ledger][olo] explicitly records the remaining external-solver representation and general projection work. Concrete rules generate checks using known source/optimization templates, range arguments, and proved footprint scans.

**Assessment:** the current strongest automation is in composing and compiling checks whose semantic ingredients are supplied by the instance. Do not describe this as a general implementation of OLO's symbolic assumption-extraction and projection pipeline.

## 7. The central remaining host issue is conditional progress

The shared compiler requires:

```coq
SUPPORTED : forall source,
  supported source = true -> exists MODEL : region_progress source, True.
```

The [common pass][common] similarly establishes a source progress model before installing a whole-region replacement. This proof route reconstructs a completed source execution and then consumes the local rule.

That is compatible with the implemented classes but does not yet cover a different, important use case:

```text
P holds:     source and candidate have a finite optimizable domain.
P fails:     the original region may diverge; execute that region unchanged.
```

The generic conditional-choice idea does not require source termination on rejected inputs. The current whole-region host is more restrictive than that idea. A finite rewrite at each head of an otherwise infinite loop is a useful existing capability, but is not the same as versioning the entire possibly divergent loop.

The repository already recognizes this in [`conditional-progress-host-design.md`][conditional-progress], explicitly marked as not implemented. Its unsigned example is:

```c
for (; i != *bound; ++i)
  *out = i + 2U;
```

With `out == bound` and the stated starting configuration, the target value keeps moving, so the source can run indefinitely. A stable-bound fast path may terminate, but rejection must preserve the divergent original region.

**Recommendation:** prioritize this semantic acceptance test above another closely related rectangle template. Use finite source-prefix evidence to establish the guard domain, a P-dependent rank for the accepted path, and small-step matching of the untouched source on rejection. This extends the host contract without adding alias or loop-bound knowledge to the generic kernel.

## 8. Current implemented scope is substantial, but not a consolidated general polyhedral pass

The pinned [checkpoint][checkpoint] and the actual [common compiler source][common] show separate whole-region and finite-expression/head hosts, combined in a real C-to-assembly entry point.

The recent [dual dynamic rectangle instance][dual] handles two independently loaded runtime bounds, snapshots them in distinct private temporaries, performs an actual loop interchange, and restores public counters and memory observations. The common pass now combines one-cache and two-cache rules using a three-slot private pool and preserves the existing rule priority.

Important implementation limits remain explicit:

- the dual rectangle selector caps static extent at 12, although the local theorem does not have this extra engineering cap;
- stride is static in that dual-loaded instance;
- the body is a checked affine store template, not arbitrary C;
- multiple dependent preloads, larger/general-pointer layouts, and the combination of two loaded bounds with parameter stride remain incomplete;
- the older affine/tiling pipeline has not yet been migrated to the primary read-only interface;
- the current whole-region host still needs source progress independent of acceptance.

The older affine route's broader capabilities and the newer read-only route's stronger interface factoring are not yet one fully integrated pipeline. Likewise, many native function calls validate an instance over input families; they are not counts of independent optimization kernels.

## 9. Evidence: correctness engineering versus optimization performance

At the snapshot, the checkpoint reports 54 closed language-independent endpoints, 59 Clight-adapter endpoints, and 368 full-compilation endpoints with 850 proof-source hashes, 24 configurations, and 39 native reports. 'No new global axioms' is relative to explicitly inherited baselines, not a claim that the entire end-to-end chain has no assumptions.

The dual-rectangle fixture reports 113,330 calls. Its documented acceptance statistics are input/model classifications, not instrumented fast-path counters. The tests exclude identified source-invalid and explicitly divergent executions.

The certified simplification and shared-exit work does have concrete static output evidence. For the single-loaded fixture, reported printed Clight body sizes are 332,491 -> 61,039 -> 6,584 bytes for direct trees, shared exits, and shared exits plus probe simplification. For the dual-loaded fixture, shared-exit body size falls from 129,224 to 14,234 bytes, with if counts 413 -> 69 and alias-comparison positions 248 -> 48.

These are printed-IR/structural measurements, not assembly size or runtime speedups. Current documents explicitly report no runtime performance measurements for these new instances. A proof of equivalence does not establish that the generated fast path pays for its guard.

## 10. Suggested top-down architecture and next decisions

Retain the following responsibility boundaries:

```text
rule/domain provider:
  actual source/candidate + semantic obligations + conditional local theorem

condition services:
  entry derivation certificates, atom encodings, dependent composition,
  bounded scans with coverage, certified simplification

generic semantic kernel:
  readonly condition + abstract select + local-to-context certificate composition

language realization and host:
  concrete checks/control, fresh private resources, state/observation transport,
  admissible placement, progress/divergence handling, compiler simulation

user pass:
  source recognition, candidate proposals, traversal, priorities, resource budgets
```

This is not a recommendation for a single mandatory linear pipeline: a user can directly supply a certified check, while a richer domain can use the full condition services. Nor should C-specific pointer or continuation semantics move into the generic kernel.

Priorities suggested by this review:

1. Freeze and document the existing `select_exact`/read-only boundary instead of adding another abstract choice API.
2. Establish the conditional-progress whole-region host with a possibly divergent rejected source.
3. Factor certified realization sufficiently that direct and shared control encodings reuse the same installation infrastructure; use the already implemented alternatives as the test, rather than inventing while/goto examples solely for variety.
4. Replace one template-specific or enumerative condition path with a proved symbolic entry-condition/footprint algorithm and connect it to an actual candidate and compiler endpoint.
5. Measure guard runtime, actual fast-path acceptance, compiled code size, and compile time on useful-size inputs. Keep those distinct from the existing correctness regressions.

A candidate positioning supported by the current direction is **verified executable-condition processing for guarded transformations**, with a source-level Clight/CompCert host as the demanding evaluation instance. This is a design hypothesis, not a novelty conclusion; no new external literature audit was performed in this review.

## Snapshot sources

[kernel]: https://github.com/Hughshine/GuardCert/blob/cf4d44292cd1e834e79db31d0ac3a75696a7d40c/prototype/interface/GuardInterface.v
[rewrite]: https://github.com/Hughshine/GuardCert/blob/cf4d44292cd1e834e79db31d0ac3a75696a7d40c/prototype/interface/GuardedRewrite.v
[old-stateful]: https://github.com/Hughshine/GuardCert/blob/cf4d44292cd1e834e79db31d0ac3a75696a7d40c/theories/StatefulGuard.v
[clight-host]: https://github.com/Hughshine/GuardCert/blob/cf4d44292cd1e834e79db31d0ac3a75696a7d40c/prototype/interface/ClightReadonlyRewrite.v
[shared-code]: https://github.com/Hughshine/GuardCert/blob/cf4d44292cd1e834e79db31d0ac3a75696a7d40c/prototype/interface/ClightSharedGuard.v
[shared-compiler]: https://github.com/Hughshine/GuardCert/blob/cf4d44292cd1e834e79db31d0ac3a75696a7d40c/prototype/interface/ClightSharedProjectedCompiler.v
[stages]: https://github.com/Hughshine/GuardCert/blob/cf4d44292cd1e834e79db31d0ac3a75696a7d40c/prototype/interface/ReadonlyConditionComposition.v
[prefix]: https://github.com/Hughshine/GuardCert/blob/cf4d44292cd1e834e79db31d0ac3a75696a7d40c/docs/readonly-prefix-scan-interface.md
[simplifier]: https://github.com/Hughshine/GuardCert/blob/cf4d44292cd1e834e79db31d0ac3a75696a7d40c/docs/readonly-probe-simplification.md
[derivation]: https://github.com/Hughshine/GuardCert/blob/cf4d44292cd1e834e79db31d0ac3a75696a7d40c/prototype/interface/AssumptionDerivation.v
[conditional-progress]: https://github.com/Hughshine/GuardCert/blob/cf4d44292cd1e834e79db31d0ac3a75696a7d40c/docs/conditional-progress-host-design.md
[common]: https://github.com/Hughshine/GuardCert/blob/cf4d44292cd1e834e79db31d0ac3a75696a7d40c/prototype/interface/ClightCommonRewriteCompiler.v
[checkpoint]: https://github.com/Hughshine/GuardCert/blob/cf4d44292cd1e834e79db31d0ac3a75696a7d40c/docs/research-checkpoint-2026-10-05.md
[dual]: https://github.com/Hughshine/GuardCert/blob/cf4d44292cd1e834e79db31d0ac3a75696a7d40c/docs/clight-dual-dynamic-rectangle-case.md
[olo]: https://github.com/Hughshine/GuardCert/blob/cf4d44292cd1e834e79db31d0ac3a75696a7d40c/docs/optimistic-loop-acceptance.md
