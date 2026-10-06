# Dependent header: actual compiler installation and complete C validation

Date: 2026-10-06. This stage follows the [joint local candidate proof](research-checkpoint-2026-10-06-dependent-joint.md).

The new extracted entry recognizes an actual signed Clight loop with `i < **root`, captures the pointer and bound in two fresh temporaries, checks both observations against the source write footprint, and installs a checked mapped, scheduled, or tiled candidate. Failed runtime checks execute the original compound-load loop. Candidate or source rejection during compilation leaves the source in place.

This closes the preceding factory, capture-domain, typed-resource, host, extraction, and native gaps for this source family. It does not finish the overall polyhedral integration goal.

## Source and Replacement

The complete [triangle input](../examples/native_affine_dependent_loaded.c) has this region:

```c
void dependent_triangle(int *p, int *q, int **root, int start, int a) {
  int i=start, j=77, k=91, rp, rq, snapshot=123;
  rq=*q; rp=*p;
  for (; i<**root; ++i) {
    k=i+1;
    for (j=0; j<k; ++j)
      p[32+64*i+j]=q[4096+64*i+j]+a;
  }
  /* The surrounding program observes counters, retained reads and memory. */
}
```

The second [input](../examples/native_affine_dependent_ragged.c) uses `k=2*i+1`. Neither input contains a public bound snapshot. Retained `rq=*q; rp=*p` reads are still required by the current source adapter to establish body-pointer receipts.

The actual transformed Clight code starts with a pointer-typed cache and an integer cache. For the triangle fixture their fresh names are `$93` and `$94`:

```c
$rq = *$q;
$rp = *$p;
$93 = *$root;
$94 = *$93;
/* Preparation, source-prefix dual-observation checks, candidate conditions. */
/* Accepted candidate plus public-counter restoration, or original **root loop. */
```

The matcher compares the original normalized statement against the exact compound-loop syntax. Casts, volatile loads, unsigned headers and different increments are not silently accepted. The installation table uses the original source statement as its key. The internal cached source is a modeling and proof interface.

## Certificate Chain and Responsibility

| Owner | Obligation discharged in this stage | Source |
| --- | --- | --- |
| Minimal semantic kernel | Existing local condition/preservation composition; no new kernel laws | [paper narrative](topdown/paper-narrative.md) |
| Libraries above the kernel | Existing readonly sequencing/prefix scan and plan/code correspondence | Reused unchanged from the preceding service and joint stages |
| Clight language services | Exact original source selection, safe ordered captures, private/public scope projection | [source adapter](../prototype/interface/ClightDependentLoadedSource.v), inherited `dependent_snapshot_insertion_contract` |
| Clight/domain entry adapter | Derive typed captured observations and body-pointer receipts from actual prefix and subsequent original header | [capture-domain producer](../prototype/interface/ClightDependentCaptureDomain.v) |
| Polyhedral instance | Bind original source to the checked cached model, construct a plan exactly equal to the certified full condition, consume actual candidate certificates | [checked syntax](../prototype/interface/ClightAffineDependentSyntax.v), [plan](../prototype/interface/ClightAffineDependentCheckPlan.v), [local planned rewrite](../prototype/interface/ClightAffineDependentPlannedRewrite.v), [factories](../prototype/interface/ClightAffineDependentCandidates.v) |
| Clight host | Allocate typed fresh names, consume original-source progress, scope and table installation; connect frontend and backend simulations | [host](../prototype/interface/ClightDependentRegionHost.v), [compiler](../prototype/interface/ClightGuardedAffineDependentCompiler.v) |

`dependent_capture_header_receipt` uses the actual capture execution and reached original header to obtain both cached values and their types. The original-entry preparation theorem separately establishes that the extra captures are safe. A completed source execution includes its first header even when the body runs zero times. Private initial values need not be defined or equal to source values.

The prefix contract retains only the entry's row value, two captured observations and body-pointer evidence as its static entry domain. When its consumer receives an actual remaining source execution, it reconstructs the completed-source evidence for that execution's function environment. It does not place future bound or pointer stability in the entry domain.

The accepted guard establishes preservation of both the Mptr pointer-cell load and Mint32 bound-cell load. The preceding joint stage supplies actual row decoding, write receipts, signed ranges and cap coverage. The new factory invokes the existing mapped/tiling checkers and checked schedule-generation path. Those checks establish conditional candidate correctness; the kernel does not discover or validate polyhedral schedules itself.

The private pool contains **19 slots**: one `int *` pointer cache, one signed bound cache, one integer Boolean result and sixteen integer counter slots. Source matching and factory checks enforce the pointer/integer types, distinctness and freshness. The actual host consumes `signed_expression_region_progress_supported` for the original compound source. Its progress obligation remains independent of whether dynamic observation-stability checks accept.

## Proof and Extraction Evidence

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make affine-dependent-compiler-proof
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/build_affine_dependent.py
```

Nine new `.v` modules, 873 lines including imports, statements, proofs and fixtures, compile. The dedicated audit has **40 endpoints, 29 within the CompCert-only language baseline, 531 selected dependencies and 961 source digests**. Two factory-refusal fixtures are audited with the domain baseline because they reduce the actual impure factory. The complete compiler endpoint has the inherited 42 assumptions; no additional global axioms were introduced.

The complete program theorem is
`ClightGuardedAffineDependentCompiler.compile_guarded_affine_dependent_correct`:
a successful `mayReturn` result implies backward simulation from actual `Csem.semantics` to `Asm.semantics`. Its proof composes SimplExpr, SimplLocals, actual dependent table installation and the verified CompCert tail.

The proof audit verifies all inherited source and compiled-object bindings, including sources within the selected closure. It is an incremental closure audit, not a clean rebuild. The proof report itself excludes frontend, extraction and native claims; the build stamp and native reports supply those separate results.

| Artifact | SHA-256 |
| --- | --- |
| `build/affine-dependent-compiler/proof/report.json` | `c4b519808a8b2b4da82bfd9eec7e535bfa989eb121723b79e29d6cd9d2613391` |
| Extracted `compiler/ccomp` | `d34f41762a577e49dd151f83ee49c718aa8d817095a5f136ecfcd0791b41cabf` |
| `compiler/.guard-build.json` | `c33ccfb879973b2651877c882e386660d2ada433fb9d7d706013a32e082c3761` |
| Triangle native report | `037fdf6684a89749f6da9adac98c56226cc1ccd5d3713650a3f47ff83be7e76d` |
| Ragged native report | `e5288adf6c50583f8ff48a066f437c19d2a75120d4d9664efcb5eaad71dc0410` |

Extraction retains sequential plan structure and omits `check_plan_tree` expansion. The same existing untrusted metadata/candidate callback and checked LCF oracle are used; no new trusted candidate oracle was introduced. The older private-loaded compiler and its frozen proof report remain independent evidence.

## Complete C and Machine Paths

```sh
python3 scripts/native_affine_dependent.py
python3 scripts/native_affine_dependent.py --ragged
make affine-dependent-compiler-validate
```

The native scripts' GDB probes require local ptrace permission. This session's sandboxed matrices passed, but GDB could not start its inferior. The final complete runs used the permitted local-debugging execution environment.

Each shape has six configurations: mapped candidate, scheduled candidate, 2×3 tiling, 4×1 tiling, default 64×64 caps and an invalid candidate. All have **37 calls**, for **444 new-entry calls** across both shapes. GCC and the Python model agree with every complete output buffer, public counter/read/marker value and surrounding context result. A separate same-source comparison executes the old private-loaded entry for 37 calls per shape; it does not install a transformation on the compound header. These 74 calls are not included in the 444 new-entry count.

The **28 machine probes**, including two old-entry comparisons, observe actual store order and values. Accepted mapped/scheduled/tiled cases write watched positions in the order `32,160,97`; source fallback uses `32,97,160`. Different-block bound cells and same-buffer non-write offsets accept. First- and second-row bound collisions refuse and preserve the source's early termination and final bound. Body alias, conservative different-body-base refusal, cap refusal and invalid candidates keep source behavior. All probes check public exits and preservation of the live pointer cell.

The short-array source has only its first row's write cell available. That first write changes the bound from 3 to -1, and the original loop stops. The output and machine store probe are checked. This stage does **not** instrument the complete dual-observation comparison sequence, so it does not count that probe as independent machine evidence of guard comparison order or early stopping. Those properties have formal guard proofs.

Pointer cells in these C programs are separate live `int *` objects. The earlier Mint32/Mint64 partial-overlap memory fixture remains proof evidence, not a defined C loop benchmark. This suite does not add pointer-store body support.

## Remaining Work and Cost

The complete normalized triangle function has 190 `if` statements with caps 4×4; the ragged function has 271 with caps 4×8. Default 64×64 functions have **20,710 / 20,711 `if` statements**, and their pretty-printed bodies are **12,974,466 / 13,264,404 bytes**. These are Clight syntax counts, not machine-code size or runtime measurements. No profitability or performance benefit is claimed.

The next priority is loop-based or certified symbolic scan lowering that reuses the existing safety, condition and candidate certificates. Further obligations remain for general deeper affine sources, complex bodies including legal pointer stores, physical alias acceptance for different body bases, P4 measurements and same-example comparisons with related work and author proof burden.

The fetched narrative is still `7d94d810685a691efbf07df734f5fad8abfb4724`, and its local text is identical. Its clarification is applied here: the kernel ends at local guarded correctness; condition processing is a library; concrete installation belongs to the language host. This stage required no new kernel law or file reorganization. The overall goal remains active.
