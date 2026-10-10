From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCountedLoop ClightRegionProgress.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleSourceTreeData
  GuardMemoryDoubleSourceTreeModelData GuardMemoryDoubleSourceLoopModel GuardMemoryDoubleSourceTreeExit
  GuardMemoryDoubleSourceTreeState GuardMemoryDoubleSourceTreeSource.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition tree_sibling_counter_case := DoubleTreeSequence
  (DoubleTreeRange true 201%positive (Int.repr 1) (DoubleTreeBound 101%positive (Some (Int.repr 2))) DoubleTreeSkip)
  (DoubleTreeRange true 201%positive (Int.repr 2) (DoubleTreeBound 101%positive (Some (Int.repr 3))) DoubleTreeSkip).
Example tree_shared_N_parameters : double_source_tree_parameters tree_sibling_counter_case=[101%positive].
Proof. vm_compute; reflexivity. Qed.
Example tree_parameter_at_depth_two :
  SL.eval_expr (rev [3;8]++[13;17])
    (double_tree_bound_model [101%positive;102%positive] 2 (DoubleTreeBound 101%positive (Some (Int.repr 3))))=10.
Proof. vm_compute; reflexivity. Qed.
Example tree_later_sibling_counter_wins temps :
  (double_source_tree_exit (fun _=>7%Z) tree_sibling_counter_case temps) ! 201%positive=Some (Vlong (Int64.repr 4)).
Proof.
  unfold tree_sibling_counter_case; rewrite double_source_tree_exit_sequence.
  change ((PTree.set 201%positive (Vlong (Int64.repr 4))
    (double_source_tree_exit (fun _=>7%Z)
      (DoubleTreeRange true 201%positive (Int.repr 1) (DoubleTreeBound 101%positive (Some (Int.repr 2))) DoubleTreeSkip) temps))
    ! 201%positive=Some (Vlong (Int64.repr 4))).
  apply PTree.gss.
Qed.

Definition tree_empty_outer_case := DoubleTreeRange true 201%positive Int.zero (DoubleTreeBound 101%positive None)
  (DoubleTreeRange true 202%positive (Int.repr 1) (DoubleTreeBound 102%positive None) DoubleTreeSkip).
Definition tree_empty_header_values child_value (identifier : ident) := if peq identifier 101%positive then 0 else child_value.
Example tree_empty_outer_skips_child_observation child_value :
  double_source_tree_active_headers (tree_empty_header_values child_value) tree_empty_outer_case=[101%positive].
Proof. vm_compute; reflexivity. Qed.
Example tree_empty_outer_keeps_child_temporary child_value temps :
  (double_source_tree_exit (tree_empty_header_values child_value) tree_empty_outer_case temps) ! 202%positive=temps ! 202%positive.
Proof.
  change ((PTree.set 201%positive (Vlong Int64.zero) temps) ! 202%positive=temps ! 202%positive).
  apply PTree.gso; discriminate.
Qed.

(** Actual raw Clight execution needs the outer header's load only. There is no
    load receipt, binding, signed range or source execution assumption for M. *)
Theorem tree_empty_outer_actual_execution p fe ge locals temps memory header_block (child_value : Z) :
  preserving_globals (globalenv p) ge -> double_source_tree_checked p [] tree_empty_outer_case ->
  double_global_binding ge locals 101%positive header_block ->
  Mem.load Mint64 memory header_block 0=Some (Vlong Int64.zero) ->
  exec_stmt fe ge locals temps memory (double_source_tree_code tree_empty_outer_case) E0
    (PTree.set 201%positive (Vlong Int64.zero) temps) memory Out_normal.
Proof.
  intros GLOBAL CHECK BIND LOAD.
  set (layouts := PTree.empty (list Z)).
  assert (LAYOUT : double_source_tree_shared_layout tree_empty_outer_case layouts).
  { intros instruction MEMBER; contradiction. }
  assert (SCOPE : double_source_tree_scope tree_empty_outer_case locals).
  { intros instruction MEMBER; contradiction. }
  assert (EXCLUSIONS : double_source_tree_header_exclusions tree_empty_outer_case [101%positive]).
  { intros instruction header MEMBER OBSERVED; contradiction. }
  assert (ACTIVE : incl (double_source_tree_active_headers (tree_empty_header_values child_value) tree_empty_outer_case) [101%positive]).
  { rewrite tree_empty_outer_skips_child_observation; apply incl_refl. }
  assert (FACTS : double_source_tree_model_facts tree_empty_outer_case [] (tree_empty_header_values child_value) (fun _=>0) ge layouts).
  { split.
    - change (Int64.min_signed<=0<=Int64.max_signed); pose proof Int64.min_signed_neg; pose proof Int64.max_signed_pos; lia.
    - intros value RANGE; change (0<=value<0) in RANGE; lia. }
  assert (ENTRY : double_source_tree_entry ge locals [101%positive] (tree_empty_header_values child_value) [] (fun _=>0) temps memory).
  { split; [intros key MEMBER; contradiction|].
    intros header [SAME|[]]; subst header; exists header_block; split; [exact BIND|exact LOAD]. }
  apply (proj2 (@double_source_tree_execution_memory p fe ge locals layouts [101%positive] (tree_empty_header_values child_value)
    GLOBAL tree_empty_outer_case [] (fun _=>0) temps memory (PTree.set 201%positive (Vlong Int64.zero) temps) memory
    CHECK LAYOUT SCOPE EXCLUSIONS ACTIVE FACTS ENTRY)).
  split.
  - constructor.
  - reflexivity.
Qed.

Print Assumptions tree_shared_N_parameters.
Print Assumptions tree_parameter_at_depth_two.
Print Assumptions tree_later_sibling_counter_wins.
Print Assumptions tree_empty_outer_skips_child_observation.
Print Assumptions tree_empty_outer_keeps_child_temporary.
Print Assumptions tree_empty_outer_actual_execution.
