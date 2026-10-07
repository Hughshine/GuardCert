# Loaded Word Driver, Canonical Tensor, and Actual Candidate

This stage connects conditional header capture to the complete private word
scan, then supplies canonical tensor execution to the existing numeric/layout
guard and actual generated-candidate checker. The resulting local guarantee has
the type consumed by the Clight finite-region host. A loaded-family data factory,
selected compiler entry, extraction and same-C native acceptance are still
required before this becomes an installed optimizer.

## One Actual Execution

`ClightTensorLoadedWordDriver.v` emits the following sequence:

```text
if original row == 0:
    capture loaded root bound
    if original row < captured root:
        capture loaded child bound
    if 0 < root <= root profile cap:
        if 0 < child <= child profile cap:
            initialize private literal helper
            run complete private row/column/component stability scan
        else refuse
    else refuse
else refuse

if scan accepted:
    run complete numeric/layout check

if complete check accepted:
    execute checked generated candidate and restore public counters
else:
    execute the literal original loaded-bound source
```

The first two gates inspect cached words with signed comparisons. They do not
read layout parameters or data. An inactive root skips child capture and all
subsequent checks. This driver conservatively refuses empty roots and children;
the original source handles them. A nonzero original row refuses before either
header capture. Helper initialization occurs only after both count gates accept.

Original silent normal completion supplies the initial row's definedness,
conditional capture, active-child observer receipts and source execution after
private capture. It does not assume header stability, no-wrap, a valid tensor
model, or a completed cached source. The audited full scan obtains each address
permission from a reached original prefix and advances that prefix only after
the earlier checks accept.

`tensor_word_driver_receipt_transport` transports header/cache receipts across
private helper initialization. Runtime observation syntax still uses the fixed
address templates of the source shape. The helper has no incoming definedness
premise: emitted code sets its literal word.

On scan acceptance, `tensor_word_driver_captured_scan` executes the cached nest
from the actual scan exit and applies `literal_tests_prepare` to its literal
component tests. The prepared source uses cached root/child bounds and the
initialized helper. Its actual execution reaches the original final memory and
agrees on protected public exit temporaries. This is the canonical syntax
consumed by `check_tensor_region_description`.

## Complete Check Exit and Candidate

A `tensor_region_package` for that canonical syntax supplies the existing
source/model and full numeric/layout condition services.
`tensor_word_driver_complete_execution` obtains check definedness from the
derived actual canonical execution. Scan refusal skips the entire full
condition. When the full check accepts, both canonical-source execution and
the accepting decision-tree execution are transported to its actual Boolean
materialization exit.

`tensor_word_driver_generated_execution` consumes
`check_tensor_generated_region`, which checks an actual affine or tiled Loop
plus witness data. It calls the existing forward candidate execution and
public-counter restoration theorem at that same actual check exit. The branch
reaches the original final memory and related public temporaries. Its premise
is the checked candidate's algorithmic result, not a caller-supplied execution
callback. The raw-codegen/adapted-candidate boundary remains the one recorded in
the [tiling integration](narrative-to-tiling-integration.md).

Rejected checks may leave private caches and controls changed. The driver
protects the entire original source footprint as well as declared public temps.
`tensor_word_driver_execution_with_fallback` uses that agreement to execute the
literal original AST from the checked state with the same final memory and
public exit. Retaining the original AST in an else branch alone would not prove
this transport.

`tensor_word_driver_generated_contract` delivers
`PrivateRegion.projected_region_contract`. It relates the concrete target to
the source in actual Clight small-step execution for completed finite regions.
Typed private allocation, source progress, legal selected placement and
whole-program compilation remain additional host/site obligations. This new
contract is a concrete local guarantee; the stage does not add a materialized
kernel-rule package or change the minimal semantic kernel.

## Responsibility and Factory Gap

The kernel's local certificate composition is unchanged. Language services
provide capture execution, receipt/frame transport, literal preparation,
short-circuit scans, Boolean materialization and the region-host semantics.
The domain adapter wires its loaded-bound shape to those services and supplies
the canonical tensor package and checked actual candidate.

The new theorem parameters for word grammar, source equality, scopes, control
renaming and private names are static facts. A factory must produce them from
the actual AST, metadata and typed private pool, together with the canonical
tensor package and appropriate accepted-entry evidence. They are not intended
as per-site proofs for a source user. The existing literal-family compiler's
data interface is not yet a loaded-family factory.

Exact machine-word capture and address evaluation are distinct from the
mathematical assumptions of the tensor model. Capture may safely wrap a header
offset or an index product. Count gating and stability acceptance do not by
themselves prove mathematical no-wrap; the complete numeric/layout guard and
the tensor correspondence retain that responsibility.

## Actual Memory Cases

`ClightTensorLoadedWordDriverExample.v` removes both caches and the literal
helper from the audited two-loaded-bound fixture's incoming state. Actual
capture and helper initialization restore the scan entry. With data offset 16,
the complete twenty-point scan accepts; an instance of the new driver theorem
derives canonical and original-fallback executions from that same checked exit,
with the original final memory and public agreement. Offset -20 yields an
actual alias refusal even though the original source's loaded bounds may change.

The fixture retains its parent's wrapping `2*MAX+7+k` index, which ignores row
and column. It establishes driver assembly and execution transport, not full
numeric/layout acceptance or the intended runtime-Horner RMW C example. The
generic full-check/candidate contract is compiled against any supplied canonical
tensor package and accepted actual candidate; this fixture does not instantiate
that complete candidate path.

A root profile cap of one refuses captured count two before helper initialization
or scanning, even with an undefined data pointer. The empty-root case executes
both the original source and the complete driver while the indexed child address
is beyond the real allocation; child cache, helper and data pointer remain
undefined. A separate nonzero-start case has no header pointer and skips capture.
The profile-refusal case is check-execution evidence; its undefined data pointer
is not a claim that the active original source completes.

## Evidence and Next Installation

The independent audit validates both frozen parents, binds source/object/helper
hashes and the pinned toolchain, and excludes the preserved draft modules from
the required closure. It queries 22 endpoints over 524 dependencies. Two endpoints
are closed; the others use at most 14 globals, within the existing CompCert and
PolCert/VPL baseline. The generated compiler baseline remains the same 42-global
set. No global axiom is added, and no older proof or native report is replaced.

The report is `build/tensor-loaded-word-driver/proof/report.json`, SHA256
`54ecdd0930f4fadb6a220c97153588d38e4135a60cb4ca8761b0b5692b3aa5b7`.

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_tensor_loaded_word_driver.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_tensor_loaded_word_driver.py --validate
```

The next integration must produce the static evidence and canonical package
through a data-only loaded-family factory, connect its local guarantee and
accepted-entry evidence to selected installation and Csem-to-Asm, then extract
and run the same loaded/runtime-Horner C through actual scheduling/codegen.
Acceptance must cover alias/profile refusal, conditionally unavailable reads,
marked/unmarked regions, repeated sites and continuation-visible effects.
Compact conditions, acceptance and guard/whole-execution cost remain required
later work. This stage adds no compiler entry, C/assembly calls or cost result;
the complete goal remains active.
