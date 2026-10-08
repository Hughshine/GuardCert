From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightNoWrap ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryScalarLoops GuardMemoryScalarChecker GuardMemoryRecursiveSource GuardMemoryRecursiveDomain
  GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend GuardMemoryMultiTensorBackend GuardMemoryMultiTensorSource
  GuardMemoryMultiTensorSequence GuardMemoryMultiTensorSourceCapabilities GuardMemoryMultiTensorFrame
  GuardMemoryMultiTensorSourceRegion.
From GuardInterface Require Import ClightTensorRegionPackage ClightTensorCompleteGuard ClightTensorSourceGuard
  ClightTensorBoxGuard ClightTensorBackendGuard ClightMultiTensorCompleteGuard ClightMultiTensorDataPackage.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma tensor_dimension_suffix_member dimensions identifier :
  In identifier (tensor_dimension_registers (tl dimensions)) ->
  In identifier (tensor_dimension_registers dimensions).
Proof.
  destruct dimensions as [|dimension rest]; [cbn; tauto|].
  destruct dimension; cbn; auto.
Qed.

Lemma multi_tensor_body_pointers_check dimensions layout
    (items : list (multi_tensor_source_statement dimensions layout)) :
  multi_tensor_pointer_check (multi_tensor_body_pointers items) (map mt_instruction items) = true.
Proof.
  unfold multi_tensor_pointer_check; apply forallb_forall; intros instruction MEMBER.
  apply in_map_iff in MEMBER as [item [<- MEMBER]].
  apply forallb_forall; intros access USED.
  change (tensor_member (fst access) (multi_tensor_body_pointers items) = true); apply tensor_member_true.
  unfold multi_tensor_body_pointers; apply in_flat_map; exists item; split; [exact MEMBER|].
  unfold mt_instruction,multi_tensor_source_instruction in USED; cbn [instruction_write instruction_reads] in USED.
  unfold multi_tensor_operation_pointers; cbn [map].
  destruct USED as [<-|READ].
  - left; reflexivity.
  - apply in_map_iff in READ as [actual [<- READ]].
    right; change (In (fst actual) (map fst (mts_reads (mt_operation item)))); apply in_map; exact READ.
Qed.

Definition multi_tensor_package_setup_guard source (package : multi_tensor_region_package source) :=
  tensor_complete_tree (mtr_dimensions (mtr_description package)) (mtr_nest package)
    (mtr_scalars (mtr_description package)) (mtr_cap (mtr_description package))
    (mtr_profile (mtr_description package)) (mtr_tree package).

Section EXECUTION.
Variable source : statement.
Variable package : multi_tensor_region_package source.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Let description := mtr_description package.
Let dimensions := mtr_dimensions description.
Let nest := mtr_nest package.
Let scalars := mtr_scalars description.
Let items := mtr_items package.
Let cap := mtr_cap description.
Let profile := mtr_profile description.

Lemma multi_tensor_package_suffix_protected : forall identifier, In identifier (memory_nest_iterators nest) ->
  ~ In identifier (multi_tensor_body_pointers items ++ tensor_dimension_registers (tl dimensions) ++ scalars).
Proof.
  intros identifier MEMBER BAD; apply (mtr_protected package identifier MEMBER).
  repeat rewrite in_app_iff in *; destruct BAD as [POINTER|[DIMENSION|SCALAR]]; auto.
  right; left; apply tensor_dimension_suffix_member; exact DIMENSION.
Qed.

Theorem multi_tensor_package_setup_run ge locals temps memory after final :
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  decision_run (Entry ge locals temps memory) (multi_tensor_package_setup_guard package)
    (tensor_complete_flag dimensions nest scalars cap profile (multi_tensor_body_accesses items)
      (Entry ge locals temps memory)).
Proof.
  intro SOURCE.
  assert (DEFINED : tensor_original_defined nest fe (Entry ge locals temps memory)).
  { exists after,final; eapply multi_tensor_region_source_execution; exact SOURCE. }
  apply (@multi_tensor_complete_guard_exact dimensions nest scalars items fe cap (mtr_signed_cap package)
    (mtr_body package) (mtr_nonempty package) (mtr_shapes package) (mtr_fresh package)
    multi_tensor_package_suffix_protected (mtr_used package) (mtr_dimension_reads package)
    profile (mtr_tree package) (mtr_compile package) (Entry ge locals temps memory) DEFINED).
  reflexivity.
Qed.

Theorem multi_tensor_package_setup_accept ge locals temps memory after final :
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  decision_run (Entry ge locals temps memory) (multi_tensor_package_setup_guard package) true ->
  let counts := memory_recursive_counts (memory_nest_bounds nest) temps in
  let values := memory_recursive_parameters scalars temps in
  exists sizes,
    length counts = length (memory_nest_iterators nest) /\
    Forall (fun count => count <> O /\ signed_range (Z.of_nat count)) counts /\
    memory_nest_bindings (memory_nest_bounds nest) (map Z.of_nat counts) temps /\ memory_nest_initial nest temps /\
    memory_nest_bindings scalars values temps /\ Forall signed_range values /\
    tensor_observe_dimensions dimensions temps = Some sizes /\
    decision_run (Entry ge locals temps memory) (tensor_backend_guard dimensions) true /\
    multi_tensor_body_box items counts values sizes = true /\
    MemoryNested.A.env_within (memory_scalar_static_bounds (length counts) cap (length values))
      (map Z.of_nat counts ++ values).
Proof.
  intros SOURCE GUARD.
  apply (@multi_tensor_complete_source_setup dimensions nest scalars items fe cap (mtr_signed_cap package)
    (mtr_body package) (mtr_nonempty package) (mtr_shapes package) (mtr_fresh package)
    multi_tensor_package_suffix_protected (mtr_used package) (mtr_dimension_reads package)
    profile (mtr_tree package) (mtr_compile package) ge locals temps memory); [|exact GUARD].
  exists after,final; eapply multi_tensor_region_source_execution; exact SOURCE.
Qed.

(** Accepted generated setup establishes the actual source/model connection.
    There is no entry NonAlias or numeric/layout/box callback in this endpoint. *)
Theorem multi_tensor_package_source_model ge locals temps memory after final :
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  decision_run (Entry ge locals temps memory) (multi_tensor_package_setup_guard package) true ->
  let counts := memory_recursive_counts (memory_nest_bounds nest) temps in
  let values := memory_recursive_parameters scalars temps in
  exists sizes,
    L.loop_semantics (memory_scalar_rectangle 0 (length counts) (length values) (map mt_instruction items))
      (map Z.of_nat counts++values)
      (RuntimeState (multi_tensor_locations temps sizes) memory) (RuntimeState (multi_tensor_locations temps sizes) final) /\
    after = memory_nest_exit nest counts temps.
Proof.
  intros SOURCE GUARD counts values.
  destruct (multi_tensor_package_setup_accept SOURCE GUARD)
    as [sizes (LENGTH & COUNTS & BOUNDS & INITIAL & SCALARS & SIGNED & OBSERVE & BACKEND & BOX & WITHIN)].
  pose proof (@tensor_backend_guard_accepts (Entry ge locals temps memory) dimensions sizes OBSERVE BACKEND) as LAYOUT.
  destruct (@tensor_observe_dimensions_sound dimensions temps sizes OBSERVE) as [DIMENSIONS _].
  exists sizes; eapply multi_tensor_source_region_decode with (scalars:=scalars) (pointers:=multi_tensor_body_pointers items);
    [exact (mtr_body package)|exact (mtr_shapes package)|exact (mtr_fresh package)|exact (mtr_unique package)|
     exact (mtr_protected package)|exact LENGTH|exact COUNTS|exact BOUNDS|exact INITIAL|exact LAYOUT|exact DIMENSIONS|
     exact SCALARS|apply multi_tensor_body_pointers_check|exact BOX|].
  eapply multi_tensor_region_source_execution; exact SOURCE.
Qed.
End EXECUTION.

Print Assumptions tensor_dimension_suffix_member.
Print Assumptions multi_tensor_body_pointers_check.
Print Assumptions multi_tensor_package_suffix_protected.
Print Assumptions multi_tensor_package_setup_run.
Print Assumptions multi_tensor_package_setup_accept.
Print Assumptions multi_tensor_package_source_model.
