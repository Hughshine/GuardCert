From Stdlib Require Import List Bool ZArith.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Guard Require Import ClightGuard ClightCondition ClightTempFrame ClightRegionProgress
  ClightPrivateRegion CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryAffineReindex GuardMemoryRecursiveSource
  GuardMemoryRecursiveRestore GuardMemoryDynamicTensorBackend GuardMemoryTensorSource.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightRegionBoundary
  ClightReadonlyPreservation ClightReadonlyProjectedCompiler ClightReadonlyPreservationKernel
  ClightGuardRealization ClightTensorRegionPackage ClightTensorBoxGuard ClightTensorCompleteGuard
  ClightTensorCompleteCandidates ClightTensorSourceGuard ClightTensorCandidates.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Inductive tensor_region_candidate :=
| TensorRegionMapped(candidate:L.stmt)(steps:list memory_affine_reindex)
| TensorRegionTiled(rows columns:Z).

Section PACKAGE.
Variable source : statement.
Variable package : tensor_region_package source.
Let d:=tensor_description package.
Let nest:=tensor_nest package.
Let dimensions:=tensor_region_dimensions d.
Let scalars:=tensor_region_scalars d.
Let pointer:=tensor_region_pointer d.
Let logical_array:=tensor_region_array d.
Let operation:=tensor_operation package.
Let cap:=tensor_region_cap d.
Let profile:=tensor_region_profile d.
Let tree:=tensor_region_box_tree package.

Definition tensor_region_guard := tensor_complete_tree dimensions nest scalars cap profile tree.
Definition tensor_region_premise entry := tensor_complete_flag dimensions nest scalars cap profile
  (tensor_operation_accesses operation)entry=true.
Definition tensor_region_domain := tensor_original_defined nest(adapter_entry false).
Definition tensor_region_branch code := Ssequence code(memory_recursive_restore nest).
Definition check_tensor_region_candidate live pool proposal := match proposal with
| TensorRegionMapped candidate steps=>check_tensor_mapped(length(memory_nest_iterators nest))cap(length scalars)
    [tensor_source_instruction operation]dimensions pointer logical_array(memory_nest_bounds nest++scalars)live pool candidate steps
| TensorRegionTiled rows columns=>check_tensor_tiled(length(memory_nest_iterators nest))cap(length scalars)
    [tensor_source_instruction operation]dimensions pointer logical_array(memory_nest_bounds nest++scalars)live pool rows columns end.

Lemma tensor_region_protected_tail : forall identifier,In identifier(memory_nest_iterators nest) ->
  ~In identifier(pointer::tensor_dimension_registers(tl dimensions)++scalars).
Proof.
  intros identifier ITERATOR MEMBER; apply(@tensor_region_protected source package identifier ITERATOR).
  destruct MEMBER as [POINTER|MEMBER]; [left; exact POINTER|right].
  apply in_app_or in MEMBER as [DIMENSION|SCALAR]; apply in_or_app;
    [left; apply tensor_dimension_registers_tail; exact DIMENSION|right; exact SCALAR].
Qed.

Definition tensor_region_condition temps live : readonly_condition
  (readonly_clight_host(adapter_entry temps)(boundary_observe(public_exit_ports live)))
  tensor_region_domain tensor_region_premise tensor_region_guard.
Proof.
  pose proof(@tensor_complete_condition dimensions nest scalars pointer logical_array operation(adapter_entry false)cap
    (tensor_region_signed_cap package)(tensor_region_shapes package)(tensor_region_fresh package)
    tensor_region_protected_tail(tensor_region_used package)(tensor_region_dimension_reads package)
    profile tree(tensor_region_box_compile package)fragment_observation(boundary_observe(public_exit_ports live)))as OLD.
  constructor; [exact(readonly_safe OLD)|exact(readonly_available OLD)|exact(readonly_sound OLD)].
Defined.

Theorem tensor_region_candidate_execution fe ge locals le memory after final live pool proposal code :
  CoreAlarmed.Base.mayReturn(check_tensor_region_candidate live pool proposal)(Some code) ->
  exec_stmt fe ge locals le memory source E0 after final Out_normal ->
  decision_run(Entry ge locals le memory)tensor_region_guard true ->
  exists exit,exec_stmt fe ge locals le memory(tensor_region_branch code)E0 exit final Out_normal /\ temp_agree live after exit.
Proof.
  intros CHECK SOURCE GUARD; apply(tensor_region_source_execution package)in SOURCE; destruct proposal as [candidate steps|rows columns].
  - exact(@tensor_complete_mapped_execution dimensions nest scalars pointer logical_array operation fe cap
      (tensor_region_signed_cap package)(tensor_region_shapes package)(tensor_region_fresh package)(tensor_region_unique package)
      (tensor_region_protected package)(tensor_region_used package)(tensor_region_dimension_reads package)
      profile tree(tensor_region_box_compile package)ge locals le after memory final SOURCE GUARD live pool candidate steps code CHECK).
  - exact(@tensor_complete_tiled_execution dimensions nest scalars pointer logical_array operation fe cap
      (tensor_region_signed_cap package)(tensor_region_shapes package)(tensor_region_fresh package)(tensor_region_unique package)
      (tensor_region_protected package)(tensor_region_used package)(tensor_region_dimension_reads package)
      profile tree(tensor_region_box_compile package)ge locals le after memory final SOURCE GUARD live pool rows columns code CHECK).
Qed.

Definition tensor_region_preserving_rule live pool proposal code
    (CHECK:CoreAlarmed.Base.mayReturn(check_tensor_region_candidate live pool proposal)(Some code)) :
  readonly_preserving_clight_rule live source.
Proof.
  refine {|preserving_candidate:=tensor_region_branch code;preserving_guard:=tensor_region_guard;
    preserving_domain:=tensor_region_domain;preserving_premise:=tensor_region_premise;
    preserving_writes:=memory_nest_iterators nest;preserving_source_writes:=tensor_region_source_writes package|}.
  - intro temps; pose proof(tensor_region_condition temps live)as OLD.
    constructor; [exact(readonly_safe OLD)|exact(readonly_available OLD)|exact(readonly_sound OLD)].
  - intros temps p locals le memory after final SCOPE SOURCE DOMAIN PREMISE.
    assert(DEFINED:tensor_original_defined nest(adapter_entry temps)(Entry(Clight.globalenv p)locals le memory)).
    { exists after,final; change(exec_stmt(adapter_entry temps)(Clight.globalenv p)locals le memory
        (memory_nest_source(tensor_nest package))E0 after final Out_normal).
      apply(tensor_region_source_execution package); exact SOURCE. }
    assert(GUARD:decision_run(Entry(Clight.globalenv p)locals le memory)tensor_region_guard true).
    { apply(@tensor_complete_guard_exact dimensions nest scalars pointer logical_array operation(adapter_entry temps)cap
        (tensor_region_signed_cap package)(tensor_region_shapes package)(tensor_region_fresh package)
        tensor_region_protected_tail(tensor_region_used package)(tensor_region_dimension_reads package)
        profile tree(tensor_region_box_compile package)_ DEFINED true); symmetry; exact PREMISE. }
    destruct(@tensor_region_candidate_execution(adapter_entry temps)(Clight.globalenv p)locals le memory after final
      live pool proposal code CHECK SOURCE GUARD)as [exit [RUN PUBLIC]].
    exists exit,final; split; [exact RUN|split; [exact PUBLIC|apply memory_equivalent_refl]].
  - intros temps p locals le memory after final SOURCE; exists after,final.
    change(exec_stmt(adapter_entry false)(Clight.globalenv p)locals le memory
      (memory_nest_source(tensor_nest package))E0 after final Out_normal).
    apply(tensor_region_source_execution package).
    eapply quiet_execution_preserved; [split; reflexivity|exact SOURCE|apply tensor_region_source_quiet; exact package].
Defined.

Definition tensor_region_direct_target code := tree_statement tensor_region_guard(tensor_region_branch code)source.
Theorem tensor_region_direct_contract live pool proposal code :
  CoreAlarmed.Base.mayReturn(check_tensor_region_candidate live pool proposal)(Some code) ->
  PrivateRegion.projected_region_contract live source(tensor_region_direct_target code).
Proof.
  intro CHECK; exact(@readonly_kernel_realized_region_contract live source(@tensor_region_preserving_rule live pool proposal code CHECK)
    (direct_normal_realization live tensor_region_guard(tensor_region_branch code)source)).
Qed.
End PACKAGE.
Print Assumptions tensor_region_condition.
Print Assumptions tensor_region_candidate_execution.
Print Assumptions tensor_region_preserving_rule.
Print Assumptions tensor_region_direct_contract.
