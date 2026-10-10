# 后继状态

[Source-aware 后继](double-tree-source.md)已安装完整原 tricky3 区域，并新增
21 个 runtime inputs 和九次实际路径／store 顺序观察。以下保留本 checkpoint
当时的证据；general piece correspondence、真实 tiling 和 OLO 成本仍待完成。

# Common source coordinates and complete five-stage stencil fusion

This successor closes the complete marked-region stencil refusal recorded in
[the point-origin checkpoint](double-tree-shifted.md). The extracted compiler
now installs the original `multi-stmt-stencil-seq` as one fused loop with five
original IEEE assignments, delayed dispatch, accurate public exits and the five
original loops as fallback. `fusion1` remains accepted. Whole `tricky3` remains
refused; its two installed internal ranges are not whole-region success.

## The source-order defect and the repair

The previous OpenScop exporter removed zero schedule coordinates separately for
each statement, then reconstructed a source-like schedule. A binary sequence
of sibling loops has common hierarchical sequence coordinates. Per-statement
compaction moved the varying coordinate into different positions and could
invert the order of whole ranges. The frozen N=16 receipt had statement 3 at
`(1,1,3,1,0,0)` before statement 2 at `(1,2,1,0,0,0)`, although the original C
executes the second complete range before the third.

`export_double_common_model` preserves each extracted `pi_schedule` in one
coordinate system and appends zero rows to a common output width. It retains
the original domains, typed statement bodies, access relations, parameter
layout and array table. The new export is proposal construction: it is not
assumed to be a verified semantic serialization. The authoritative source
PolyLang model is unchanged. Imported schedules are checked against that model;
the final checker separately checks the actual candidate that will be lowered.
The new numerical receipt at N=16 orders all five sibling ranges correctly.

## From fifteen generated copies to five actual candidate positions

After the source-coordinate repair, the real Pluto phase, affine and tiling
validation, and prepared codegen succeed on the whole stencil. The resulting
one-dimensional schedule is emitted as five peeled prefixes with 1, 2, 3, 4
and 5 statement copies. Positional final attachment cannot accept fifteen
candidate positions for five source statements.

`GuardSelectedDoubleTreeCommonPolicies` proposes coalescing a chain of
adjacent prefixes with a common final upper bound and increasing point lists.
It requires each body to be a structural prefix of the next; the final body
contains only instruction points. It proposes one loop and guards newly
introduced points by their first prefix boundary. It uses no benchmark name or
source-array-specific pattern. Its shape tests, guard removal and numerical
shift proposals are untrusted. Actual domain, typed instruction, dependence,
representation and machine-range checks decide whether the proposal is usable.

For the original stencil, the final Loop is structurally:

```
for k = 1 .. n-2:
    a1 assignment at source coordinate k
    if k >= 3: a2 assignment at k-1
    if k >= 5: a3 assignment at k-2
    if k >= 7: a4 assignment at k-3
    if k >= 9: a5 assignment at k-4
```

The actual generated code also retains verified domain membership tests.
The final checker consumes point shifts `[0,-1,-2,-3,-4]` and checks dependencies
on the original arrays. The original floating operand trees are retained; no
reassociation or real-number replacement is introduced. Executable restoration
recovers each original public counter, including empty ranges.

## Responsibility and the complete compiler

The semantic kernel and language host laws are unchanged. The domain instance
supplies source modeling, common-coordinate proposals, representation witnesses
and actual `C_opt` checks. The existing profile/capture/footprint services derive
accepted machine parameter and point facts (`C_derive`). Existing language
proofs establish safe original-path header reads, private capture writes,
public framing, refusal replay, actual IEEE/Mem execution and machine lowering
(`C_guard`). The current-program host discharges scope, private allocation,
placement and independent source progress (`C_host`). A C source user supplies
markers and numerical configuration, without dynamic model callbacks.

The new factory consumes these services and the actual final checker. Its
current-program compiler endpoint is:

```
DoubleTreeCommonCompiler.compile_selected_common_double_tree_program_correct
```

It proves Csem-to-Asm backward simulation for the original Csyntax input through
SimplExpr, SimplLocals, the checked guarded pass and the CompCert backend. The
projected local contract and Clight forward simulation are intermediate facts;
the compiler result is not advertised as standalone whole-program equivalence.
Five new modules add 517 lines and eleven queried endpoints, none closed. The
maximum remains 42 inherited globals, with no new global assumption. The audit
traverses 563 reachable sources, binds 10,453 files and retains seven module
attempts: five successful, two failed. See [proof receipt](double-tree-common.json).

## Actual runs and runtime checks

[The native receipt](double-tree-common-native.json) binds both extracted builds,
the earlier successful phase diagnosis, all original runs and runtime paths.
The three frozen originals run in five configurations each: unmarked, requested
untiled, requested tiled, wrong shift and profile cap 4. All fifteen complete
state digests match same-source GCC with contraction and fast math disabled.
Unmarked and wrong-shift controls install no region. Stencil's emitted Clight
has one candidate loop, five original fallback loops and dispatch thresholds
3/5/7/9. Ordinary and tightened profiles install exactly one complete stencil
region. Requested tiling still yields the same unblocked fused loop; it does
not establish actual new tiling coverage.

A separate adaptation replaces the original constant global `n=4096` with an
argv-supplied global. The marked computation, arrays, initialization and complete
state observer are unchanged. One binary, compiled with profile `[0,32]`, matches
same-source GCC for seventeen inputs from -1 to 4096, covering empty ranges,
dispatch boundaries, accepted bounds and profile refusal. This adaptation is
not counted as an unchanged original corpus program.

GDB observes seven inputs in linked, unchanged assembly. Inputs 0/3/9/32 enter
the accepted branch once and perform five shared-header checks. Inputs
-1/33/4096 enter fallback once and stop after the first header check. Their
complete outputs also match. The first sandboxed attempt failed because ptrace
was prohibited; its inputs and rejected report are retained, followed by the
successful authorized observation outside the sandbox. No target instrumentation
or assembly change is used. Counts are not CPU timings: the five repeated reads
also show that OLO shared-condition memoization is still missing.

## Remaining work

Whole `tricky3` has four source assignments at different depths and nineteen
raw generated copies. The current prefix coalescer is limited to one-dimensional
instruction-only prefixes; it cannot provide that mixed-depth correspondence.
General piece-to-source mapping, coverage/disjointness and forward execution
construction remain to implement. PolCert's existing ISS backward theorem alone
does not supply the forward/progress obligation of this guarded compiler.

Actual tiling and other domain transforms on whole trees, the original full
sequential corpus/configurations, compact OLO entry-condition construction and
simplification, complete guard/fallback/exit cost, and the larger original
benchmark tiers remain part of the active goal. This checkpoint adds no timing
or aggregate full-corpus replay and does not complete that goal.
