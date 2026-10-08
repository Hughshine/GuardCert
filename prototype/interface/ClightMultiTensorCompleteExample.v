From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition ClightPureExpr ClightCountedLoop ClightTempFrame ClightNoWrap
  ClightRedundantSet ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryRecursiveGuard GuardMemoryRecursiveDomain
  GuardMemoryDynamicTensorBackend GuardMemoryDynamicTensorLayout GuardMemoryMultiTensorSourceRegion.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightTensorBackendGuard ClightTensorSourceGuard ClightTensorBoxGuard
  ClightTensorCompleteGuard ClightMultiTensorCompleteGuard ClightMultiTensorExample ClightMultiTensorSourceExample
  ClightMultiTensorPermissionExample ClightMultiTensorCandidates ClightMultiTensorPairScanExample ClightMultiTensorCompleteCandidates.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition multi_tensor_demo_setup_layout := tensor_coordinate_layout multi_tensor_demo_dimensions
  multi_tensor_nest_demo_nest [2%positive;5%positive].
Definition multi_tensor_demo_setup_profile :=
  [(1,33);(1,33);(1,6);(1,1000);(Int.min_signed,Int.max_signed+1);(1,33);(1,1000)].
Definition multi_tensor_demo_setup_accesses := multi_tensor_body_accesses multi_tensor_nest_demo_items.
Definition multi_tensor_demo_setup_compile accesses := compile_tensor_box_guard multi_tensor_demo_setup_layout
  multi_tensor_demo_setup_profile (memory_nest_bounds multi_tensor_nest_demo_nest) [2%positive;5%positive]
  multi_tensor_demo_dimensions accesses.
Definition multi_tensor_demo_setup_tree := match multi_tensor_demo_setup_compile multi_tensor_demo_setup_accesses with
  | Some tree => tree | None => Decision false end.
Definition multi_tensor_demo_setup_guard := tensor_complete_tree multi_tensor_demo_dimensions multi_tensor_nest_demo_nest
  [2%positive;5%positive] 32 multi_tensor_demo_setup_profile multi_tensor_demo_setup_tree.

Example multi_tensor_demo_setup_compiled :
  multi_tensor_demo_setup_compile multi_tensor_demo_setup_accesses = Some multi_tensor_demo_setup_tree.
Proof. vm_compute; reflexivity. Qed.
Example multi_tensor_demo_setup_overflow_refused : multi_tensor_demo_setup_compile
  [[([2147483647;0;0;0;0],0);([0;1;0;0;0],0);([0;0;1;0;0],0)]] = None.
Proof. vm_compute; reflexivity. Qed.

Definition multi_tensor_demo_setup_temps columns components stride := PTree.set 6%positive (Vint Int.zero)
  (PTree.set 1%positive (Vint (Int.repr 3)) (PTree.set 3%positive (Vint (Int.repr columns))
    (PTree.set 4%positive (Vint (Int.repr components)) (PTree.set 2%positive (Vint (Int.repr stride))
      (PTree.set 5%positive (Vint (Int.repr 7)) (PTree.empty val)))))).

Lemma multi_tensor_demo_box_run ge locals memory columns components stride
    (COLUMNS : 0 < Int.signed (Int.repr columns)) (COMPONENTS : 0 < Int.signed (Int.repr components)) :
  decision_run (Entry ge locals (multi_tensor_demo_setup_temps columns components stride) memory)
    (tensor_box_checked_tree multi_tensor_demo_setup_profile multi_tensor_demo_setup_layout multi_tensor_demo_setup_tree)
    (tensor_box_checked_flag multi_tensor_demo_setup_profile multi_tensor_demo_setup_layout
      [1%positive;3%positive;4%positive] [2%positive;5%positive] multi_tensor_demo_dimensions multi_tensor_demo_setup_accesses
      (Entry ge locals (multi_tensor_demo_setup_temps columns components stride) memory)).
Proof.
  apply tensor_box_checked_exact with (axes:=[1%positive;3%positive;4%positive]) (scalars:=[2%positive;5%positive])
    (dimensions:=multi_tensor_demo_dimensions) (accesses:=multi_tensor_demo_setup_accesses);
    [exact multi_tensor_demo_setup_compiled| | |reflexivity].
  - repeat constructor; unfold register_domain,multi_tensor_demo_setup_temps; eexists; reflexivity.
  - change (Forall (fun identifier => 0 < tensor_box_word_valuation (multi_tensor_demo_setup_temps columns components stride) identifier)
      [1%positive;3%positive;4%positive]).
    constructor; [vm_compute; reflexivity|constructor; [exact COLUMNS|constructor; [exact COMPONENTS|constructor]]].
Qed.

Theorem multi_tensor_demo_box_accepts ge locals memory :
  decision_run (Entry ge locals (multi_tensor_demo_setup_temps 2 5 31) memory)
    (tensor_box_checked_tree multi_tensor_demo_setup_profile multi_tensor_demo_setup_layout multi_tensor_demo_setup_tree) true.
Proof. pose proof (@multi_tensor_demo_box_run ge locals memory 2 5 31 ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity)) as RUN; vm_compute in RUN; exact RUN. Qed.
Theorem multi_tensor_demo_box_columns_refused ge locals memory :
  decision_run (Entry ge locals (multi_tensor_demo_setup_temps 32 5 31) memory)
    (tensor_box_checked_tree multi_tensor_demo_setup_profile multi_tensor_demo_setup_layout multi_tensor_demo_setup_tree) false.
Proof. pose proof (@multi_tensor_demo_box_run ge locals memory 32 5 31 ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity)) as RUN; vm_compute in RUN; exact RUN. Qed.
Theorem multi_tensor_demo_box_components_refused ge locals memory :
  decision_run (Entry ge locals (multi_tensor_demo_setup_temps 2 6 31) memory)
    (tensor_box_checked_tree multi_tensor_demo_setup_profile multi_tensor_demo_setup_layout multi_tensor_demo_setup_tree) false.
Proof. pose proof (@multi_tensor_demo_box_run ge locals memory 2 6 31 ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity)) as RUN; vm_compute in RUN; exact RUN. Qed.
Theorem multi_tensor_demo_profile_refused ge locals memory :
  decision_run (Entry ge locals (multi_tensor_demo_setup_temps 2 5 1001) memory)
    (tensor_box_checked_tree multi_tensor_demo_setup_profile multi_tensor_demo_setup_layout multi_tensor_demo_setup_tree) false.
Proof. pose proof (@multi_tensor_demo_box_run ge locals memory 2 5 1001 ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity)) as RUN; vm_compute in RUN; exact RUN. Qed.

Definition multi_tensor_demo_empty_setup := PTree.set 6%positive (Vint Int.zero)
  (PTree.set 1%positive (Vint Int.zero) (PTree.empty val)).
Example multi_tensor_demo_empty_has_no_child_data :
  multi_tensor_demo_empty_setup!3%positive = None /\ multi_tensor_demo_empty_setup!2%positive = None /\
  multi_tensor_demo_empty_setup!5%positive = None /\ multi_tensor_demo_empty_setup!9%positive = None.
Proof. repeat split; reflexivity. Qed.
Theorem multi_tensor_demo_empty_setup_refused ge locals memory :
  decision_run (Entry ge locals multi_tensor_demo_empty_setup memory) multi_tensor_demo_setup_guard false.
Proof.
  unfold multi_tensor_demo_setup_guard,tensor_complete_tree; apply decision_bind_run with (b:=false); [|constructor].
  unfold tensor_source_layout_guard; apply decision_bind_run with (b:=true).
  - apply register_tree_run; exists Int.zero; reflexivity.
  - change (decision_run (Entry ge locals multi_tensor_demo_empty_setup memory)
      (decision_bind (register_range_tree 1%positive 32)
        (memory_recursive_bounds_tree 32 [3%positive;4%positive] (tensor_backend_guard multi_tensor_demo_dimensions))
        (Decision false)) false).
    apply decision_bind_run with (b:=false); [apply register_range_tree_run; exists Int.zero; reflexivity|constructor].
Qed.

Definition check_multi_tensor_demo_full_versioned live pool proposal :=
  BIND code <- check_multi_tensor_generated 3 32 2 multi_tensor_nest_demo_instructions multi_tensor_demo_dimensions
    multi_tensor_demo_pointers multi_tensor_demo_layout live pool proposal -;
  pure (option_map (multi_tensor_demo_full_versioned 32 multi_tensor_demo_setup_profile multi_tensor_demo_setup_tree) code).

Definition multi_tensor_demo_setup_property entry :=
  memory_nest_initial multi_tensor_nest_demo_nest (entry_temps entry) /\
  Forall (fun bound => register_range bound 32 entry) (memory_nest_bounds multi_tensor_nest_demo_nest) /\
  exists sizes, tensor_observe_dimensions multi_tensor_demo_dimensions (entry_temps entry) = Some sizes /\
    tensor_layout_flag sizes = true /\
    multi_tensor_body_box multi_tensor_nest_demo_items
      (memory_recursive_counts (memory_nest_bounds multi_tensor_nest_demo_nest) (entry_temps entry))
      (memory_recursive_parameters [2%positive;5%positive] (entry_temps entry)) sizes = true.

Definition multi_tensor_demo_setup_condition fe O (observe : fragment_observation -> O -> Prop) :
  readonly_condition (readonly_clight_host fe observe) (tensor_original_defined multi_tensor_nest_demo_nest fe)
    multi_tensor_demo_setup_property multi_tensor_demo_setup_guard.
Proof.
  assert (CAP : signed_range 32) by (unfold signed_range; vm_compute; intuition congruence).
  eapply readonly_condition_entails.
  - exact (@multi_tensor_complete_condition multi_tensor_demo_dimensions multi_tensor_nest_demo_nest
      [2%positive;5%positive] multi_tensor_nest_demo_items fe 32 CAP multi_tensor_nest_demo_body_checked
      multi_tensor_demo_guard_nonempty multi_tensor_nest_demo_shapes multi_tensor_nest_demo_fresh
      multi_tensor_demo_guard_protected multi_tensor_demo_used_scalar_check multi_tensor_demo_guard_dimension_reads
      multi_tensor_demo_setup_profile multi_tensor_demo_setup_tree multi_tensor_demo_setup_compiled O observe).
  - intros entry DEFINED ACCEPT.
    eapply (@multi_tensor_complete_guard_sound multi_tensor_demo_dimensions multi_tensor_nest_demo_nest
      [2%positive;5%positive] multi_tensor_nest_demo_items fe 32 CAP multi_tensor_nest_demo_body_checked
      multi_tensor_demo_guard_nonempty multi_tensor_nest_demo_shapes multi_tensor_nest_demo_fresh
      multi_tensor_demo_guard_protected multi_tensor_demo_used_scalar_check multi_tensor_demo_guard_dimension_reads
      multi_tensor_demo_setup_profile multi_tensor_demo_setup_tree multi_tensor_demo_setup_compiled entry DEFINED).
    apply (@multi_tensor_complete_guard_exact multi_tensor_demo_dimensions multi_tensor_nest_demo_nest
      [2%positive;5%positive] multi_tensor_nest_demo_items fe 32 CAP multi_tensor_nest_demo_body_checked
      multi_tensor_demo_guard_nonempty multi_tensor_nest_demo_shapes multi_tensor_nest_demo_fresh
      multi_tensor_demo_guard_protected multi_tensor_demo_used_scalar_check multi_tensor_demo_guard_dimension_reads
      multi_tensor_demo_setup_profile multi_tensor_demo_setup_tree multi_tensor_demo_setup_compiled entry DEFINED).
    symmetry; exact ACCEPT.
Defined.

Theorem check_multi_tensor_demo_full_versioned_execution fe ge locals temps memory source_after final live pool proposal target :
  (forall identifier, In identifier live -> In identifier multi_tensor_demo_pair_public) ->
  exec_stmt fe ge locals temps memory (memory_nest_source multi_tensor_nest_demo_nest) E0 source_after final Out_normal ->
  mayReturn (check_multi_tensor_demo_full_versioned live pool proposal) (Some target) ->
  exists after, exec_stmt fe ge locals temps memory target E0 after final Out_normal /\ temp_agree live source_after after.
Proof.
  intros LIVE SOURCE RUN; unfold check_multi_tensor_demo_full_versioned in RUN.
  bind_imp_destruct RUN checked_option CHECK; apply mayReturn_pure in RUN.
  destruct checked_option as [code|]; [|discriminate]; inversion RUN; subst target.
  eapply multi_tensor_demo_full_versioned_execution;
    [unfold signed_range; vm_compute; intuition congruence|exact multi_tensor_demo_setup_compiled|exact LIVE|exact SOURCE|exact CHECK].
Qed.

Print Assumptions multi_tensor_demo_setup_compiled.
Print Assumptions multi_tensor_demo_setup_overflow_refused.
Print Assumptions multi_tensor_demo_box_run.
Print Assumptions multi_tensor_demo_box_accepts.
Print Assumptions multi_tensor_demo_box_columns_refused.
Print Assumptions multi_tensor_demo_box_components_refused.
Print Assumptions multi_tensor_demo_profile_refused.
Print Assumptions multi_tensor_demo_empty_has_no_child_data.
Print Assumptions multi_tensor_demo_empty_setup_refused.
Print Assumptions multi_tensor_demo_setup_condition.
Print Assumptions check_multi_tensor_demo_full_versioned_execution.
