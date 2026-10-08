From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightNoWrap
  ClightStraightLine ClightRectangularGuard ClightRectangularStore ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryScalarLoops GuardMemoryScalarChecker GuardMemoryPointerBackend GuardMemoryArrayBackend GuardMemoryDynamicTensorLayout
  GuardMemoryDynamicTensorBackend GuardMemoryRecursiveSource GuardMemoryRecursiveRestore
  GuardMemoryMultiTensorBackend GuardMemoryMultiTensorSequence GuardMemoryMultiTensorFrame
  GuardMemoryMultiTensorSourceRegion.
From GuardInterface Require Import ClightTensorBackendGuard ClightTensorGeneratedCandidates
  ClightMultiTensorExample ClightMultiTensorCandidates ClightMultiTensorSourceCandidates.
Import ListNotations CoreAlarmed.
Local Open Scope Z_scope.

(** These are complete source loops, not a proposed Loop schedule:
      for (i=0; i<n; i++)
        for (j=0; j<m; j++)
          for (k=0; k<c; k++) {
            a[((i*ld)+j)*5+k] = b[((i*ld)+j)*5+k] + alpha;
            b[((i*ld)+j)*5+k] = a[((i*ld)+j)*5+k] + alpha;
          }
    The outer i=0 setup lies immediately before this counted region. *)
Definition multi_tensor_nest_demo_inner := MemorySourceAxis 8%positive 4%positive multi_tensor_demo_body
  (MemorySourceLeaf multi_tensor_demo_body).
Definition multi_tensor_nest_demo_middle := MemorySourceAxis 7%positive 3%positive
  (Ssequence (rectangle_reset 8%positive) (memory_nest_source multi_tensor_nest_demo_inner)) multi_tensor_nest_demo_inner.
Definition multi_tensor_nest_demo_nest := MemorySourceAxis 6%positive 1%positive
  (Ssequence (rectangle_reset 7%positive) (memory_nest_source multi_tensor_nest_demo_middle)) multi_tensor_nest_demo_middle.
Definition multi_tensor_nest_demo_items := match multi_tensor_demo_describe multi_tensor_demo_body with
  | Some items => items | None => [] end.
Definition multi_tensor_nest_demo_instructions := map mt_instruction multi_tensor_nest_demo_items.

Example multi_tensor_nest_demo_body_checked :
  flatten_region (memory_nest_leaf multi_tensor_nest_demo_nest) = map mt_statement multi_tensor_nest_demo_items.
Proof. vm_compute; reflexivity. Qed.
Example multi_tensor_nest_demo_shapes : memory_nest_shapes multi_tensor_nest_demo_nest.
Proof. repeat split; reflexivity. Qed.
Example multi_tensor_nest_demo_fresh : memory_nest_fresh multi_tensor_nest_demo_nest.
Proof.
  split; cbn.
  - repeat constructor; cbn; intuition congruence.
  - intros identifier MEMBER BAD; intuition congruence.
Qed.
Example multi_tensor_nest_demo_unique : NoDup (memory_nest_iterators multi_tensor_nest_demo_nest ++ [2%positive;5%positive]).
Proof. repeat constructor; cbn; intuition congruence. Qed.
Example multi_tensor_nest_demo_protected : forall identifier,
  In identifier (memory_nest_iterators multi_tensor_nest_demo_nest) ->
  ~ In identifier (multi_tensor_demo_pointers ++ tensor_dimension_registers multi_tensor_demo_dimensions ++ [2%positive;5%positive]).
Proof. intros identifier MEMBER BAD; cbn in MEMBER,BAD; intuition congruence. Qed.
Example multi_tensor_nest_demo_pointers_checked :
  multi_tensor_pointer_check multi_tensor_demo_pointers multi_tensor_nest_demo_instructions = true.
Proof. vm_compute; reflexivity. Qed.
Example multi_tensor_nest_demo_missing_pointer_refused :
  multi_tensor_pointer_check [9%positive] multi_tensor_nest_demo_instructions = false.
Proof. vm_compute; reflexivity. Qed.
Example multi_tensor_nest_demo_box_accepted :
  multi_tensor_body_box multi_tensor_nest_demo_items [3%nat;2%nat;5%nat] [31;7] [3;31;5] = true.
Proof. vm_compute; reflexivity. Qed.
Example multi_tensor_nest_demo_wide_columns_refused :
  multi_tensor_body_box multi_tensor_nest_demo_items [3%nat;32%nat;5%nat] [31;7] [3;31;5] = false.
Proof. vm_compute; reflexivity. Qed.

(** The source model needs only agreement for arrays 9 and 10. A different
    pointer binding elsewhere may disappear during a counter reset. Global
    equality of the raw registry would unnecessarily reject this situation. *)
Definition multi_tensor_nest_demo_entry := PTree.set 42%positive (Vptr 1%positive Ptrofs.zero)
  (PTree.empty val).
Definition multi_tensor_nest_demo_point := PTree.set 42%positive (Vint Int.zero) multi_tensor_nest_demo_entry.
Example multi_tensor_nest_demo_local_pointer_frame :
  temp_agree multi_tensor_demo_pointers multi_tensor_nest_demo_entry multi_tensor_nest_demo_point.
Proof.
  intros identifier MEMBER; unfold multi_tensor_nest_demo_point; rewrite PTree.gso; [reflexivity|].
  cbn in MEMBER; intuition congruence.
Qed.
Example multi_tensor_nest_demo_unrelated_registry_changes :
  multi_tensor_locations multi_tensor_nest_demo_entry [3;31;5] {|arr_id:=42%positive;arr_index:=[0;0;0]|} <>
  multi_tensor_locations multi_tensor_nest_demo_point [3;31;5] {|arr_id:=42%positive;arr_index:=[0;0;0]|}.
Proof. vm_compute; discriminate. Qed.

Theorem multi_tensor_nest_demo_source_execution fe ge locals counts scalar_values sizes temps memory after final :
  length counts = 3%nat -> Forall (fun count => count <> O /\ signed_range (Z.of_nat count)) counts ->
  memory_nest_bindings [1%positive;3%positive;4%positive] (map Z.of_nat counts) temps -> temps!6%positive = Some (Vint Int.zero) ->
  tensor_layout_flag sizes = true -> tensor_dimension_view multi_tensor_demo_dimensions sizes temps ->
  memory_nest_bindings [2%positive;5%positive] scalar_values temps ->
  multi_tensor_body_box multi_tensor_nest_demo_items counts scalar_values sizes = true ->
  exec_stmt fe ge locals temps memory (memory_nest_source multi_tensor_nest_demo_nest) E0 after final Out_normal ->
  L.loop_semantics (memory_scalar_rectangle 0 (length counts) (length scalar_values) multi_tensor_nest_demo_instructions)
    (map Z.of_nat counts ++ scalar_values)
    (RuntimeState (multi_tensor_locations temps sizes) memory) (RuntimeState (multi_tensor_locations temps sizes) final) /\
  after = memory_nest_exit multi_tensor_nest_demo_nest counts temps.
Proof.
  intros LENGTH COUNTS BOUNDS INITIAL LAYOUT DIMENSIONS SCALARS BOX SOURCE.
  exact (@multi_tensor_source_region_decode multi_tensor_demo_dimensions multi_tensor_nest_demo_nest
    [2%positive;5%positive] multi_tensor_demo_pointers multi_tensor_nest_demo_items fe ge locals
    counts scalar_values sizes temps memory after final multi_tensor_nest_demo_body_checked
    multi_tensor_nest_demo_shapes multi_tensor_nest_demo_fresh multi_tensor_nest_demo_unique
    multi_tensor_nest_demo_protected LENGTH COUNTS BOUNDS INITIAL LAYOUT DIMENSIONS SCALARS
    multi_tensor_nest_demo_pointers_checked BOX SOURCE).
Qed.

Theorem multi_tensor_nest_demo_generated_restored fe ge locals counts scalar_values sizes temps memory after final
    cap live pool proposal code :
  length counts = 3%nat -> Forall (fun count => count <> O /\ signed_range (Z.of_nat count)) counts ->
  memory_nest_bindings [1%positive;3%positive;4%positive] (map Z.of_nat counts) temps -> temps!6%positive = Some (Vint Int.zero) ->
  memory_nest_bindings [2%positive;5%positive] scalar_values temps -> Forall signed_range scalar_values ->
  tensor_observe_dimensions multi_tensor_demo_dimensions temps = Some sizes ->
  decision_run (Entry ge locals temps memory) (tensor_backend_guard multi_tensor_demo_dimensions) true ->
  multi_tensor_body_box multi_tensor_nest_demo_items counts scalar_values sizes = true ->
  MemoryNested.A.env_within (memory_scalar_static_bounds (length counts) cap (length scalar_values))
    (map Z.of_nat counts ++ scalar_values) ->
  multi_tensor_separated_source (length counts) (length scalar_values) multi_tensor_nest_demo_instructions
    (map Z.of_nat counts ++ scalar_values) temps sizes ->
  exec_stmt fe ge locals temps memory (memory_nest_source multi_tensor_nest_demo_nest) E0 after final Out_normal ->
  mayReturn (check_multi_tensor_generated (length counts) cap (length scalar_values) multi_tensor_nest_demo_instructions
    multi_tensor_demo_dimensions multi_tensor_demo_pointers multi_tensor_demo_layout live pool proposal) (Some code) ->
  exists restored,
    exec_stmt fe ge locals temps memory (Ssequence code (memory_recursive_restore multi_tensor_nest_demo_nest))
      E0 restored final Out_normal /\ temp_agree live after restored.
Proof.
  intros LENGTH COUNTS BOUNDS INITIAL SCALARS SIGNED OBSERVE GUARD BOX WITHIN SEPARATED SOURCE CHECK.
  eapply multi_tensor_original_generated_restored with
    (items := multi_tensor_nest_demo_items) (counts := counts) (scalar_values := scalar_values) (sizes := sizes)
    (pointers := multi_tensor_demo_pointers) (scalars := [2%positive;5%positive]);
    eauto using multi_tensor_nest_demo_body_checked, multi_tensor_nest_demo_shapes, multi_tensor_nest_demo_fresh,
      multi_tensor_nest_demo_unique, multi_tensor_nest_demo_protected, multi_tensor_nest_demo_pointers_checked.
Qed.

Print Assumptions multi_tensor_nest_demo_body_checked.
Print Assumptions multi_tensor_nest_demo_shapes.
Print Assumptions multi_tensor_nest_demo_fresh.
Print Assumptions multi_tensor_nest_demo_unique.
Print Assumptions multi_tensor_nest_demo_protected.
Print Assumptions multi_tensor_nest_demo_pointers_checked.
Print Assumptions multi_tensor_nest_demo_missing_pointer_refused.
Print Assumptions multi_tensor_nest_demo_box_accepted.
Print Assumptions multi_tensor_nest_demo_wide_columns_refused.
Print Assumptions multi_tensor_nest_demo_local_pointer_frame.
Print Assumptions multi_tensor_nest_demo_unrelated_registry_changes.
Print Assumptions multi_tensor_nest_demo_source_execution.
Print Assumptions multi_tensor_nest_demo_generated_restored.
