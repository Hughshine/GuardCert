From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes Cop ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightTempFrame ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryMultiPointerCells
  GuardMemoryFiniteAliasCondition GuardMemoryFiniteFootprint GuardMemoryFootprintCapabilities
  GuardMemoryNaryAffineExpressions GuardMemoryBooleanScan GuardMemoryAffinePairScan.
From GuardMemory Require Import GuardMemoryAffineEndpointCells GuardMemoryAffineEndpointScan.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_pair_choice_statement x y flag bound first second first_expression second_expression first_term second_term :=
  if memory_affine_pair_fast first_term second_term then
    memory_affine_endpoint_pair_statement x y flag bound first second first_expression second_expression
  else memory_affine_range_pair_statement x y flag bound first second first_expression second_expression.
Definition memory_affine_pair_choice_check locations count first second first_term second_term :=
  if memory_affine_pair_fast first_term second_term then
    memory_affine_endpoint_pair_check locations count first second first_term second_term
  else memory_affine_range_pair_check locations count first second first_term second_term.

Theorem memory_affine_pair_choice_execution first_expression second_expression first_term second_term original_iterator
  fe ge locals original current memory extent first second x y flag bound live count accepted :
  memory_encode_nary_index [original_iterator] first_expression = Some first_term ->
  memory_encode_nary_index [original_iterator] second_expression = Some second_term ->
  first <> second -> extent <= Int.max_signed+1 -> 0 <= count -> signed_range count ->
  NoDup [x;y;flag;bound] -> ~ In x (first::second::live) -> ~ In y (first::second::live) ->
  ~ In flag (first::second::live) ->
  temp_agree (first::second::live) original current ->
  current ! bound = Some (Vint (Int.repr count)) -> current ! flag = Some (memory_boolean_word accepted) ->
  (forall index, 0 <= index < count ->
    memory_cell_capable (memory_multi_pointer_locations original extent) memory (point_cell first (memory_nary_index_value first_term [index])) /\
    memory_cell_capable (memory_multi_pointer_locations original extent) memory (point_cell second (memory_nary_index_value second_term [index]))) ->
  exists after,
    exec_stmt fe ge locals current memory (memory_affine_pair_choice_statement x y flag bound first second first_expression second_expression first_term second_term)
      E0 after memory Out_normal /\
    temp_agree (bound::first::second::live) current after /\
    after ! flag = Some (memory_boolean_word
      (accepted && memory_affine_pair_choice_check (memory_multi_pointer_locations original extent) count first second first_term second_term)).
Proof.
  intros FIRST SECOND DISTINCT EXTENT POS RANGE UNIQUE XFRESH YFRESH FFRESH POINTERS BOUND FLAG CAPS.
  unfold memory_affine_pair_choice_statement,memory_affine_pair_choice_check.
  destruct (memory_affine_pair_fast first_term second_term);
    [eapply memory_affine_endpoint_pair_execution|eapply memory_affine_range_pair_execution]; eassumption.
Qed.
Print Assumptions memory_affine_pair_choice_execution.

Theorem memory_affine_pair_choice_complete temps extent memory count first second first_term second_term :
  first <> second -> 0 <= count ->
  (forall index, 0 <= index < count ->
    memory_cell_capable (memory_multi_pointer_locations temps extent) memory
      (point_cell first (memory_nary_index_value first_term [index])) /\
    memory_cell_capable (memory_multi_pointer_locations temps extent) memory
      (point_cell second (memory_nary_index_value second_term [index]))) ->
  memory_affine_pair_choice_check (memory_multi_pointer_locations temps extent) count first second first_term second_term = true ->
  memory_affine_range_pair_check (memory_multi_pointer_locations temps extent) count first second first_term second_term = true.
Proof.
  intros DISTINCT COUNT CAPS CHECK; unfold memory_affine_pair_choice_check in CHECK.
  destruct (memory_affine_pair_fast first_term second_term) eqn:FAST;
    [eapply memory_affine_pair_fast_complete; eassumption|exact CHECK].
Qed.

Lemma memory_affine_point_pair_frame original current extent first second i j :
  temp_agree [first;second] original current ->
  memory_cell_pair_address_check (memory_multi_pointer_locations current extent) (point_cell first i) (point_cell second j) =
  memory_cell_pair_address_check (memory_multi_pointer_locations original extent) (point_cell first i) (point_cell second j).
Proof.
  intro FRAME; unfold memory_cell_pair_address_check; destruct memory_cell_identity_dec; [reflexivity|].
  unfold memory_multi_pointer_locations; cbn [arr_id point_cell].
  rewrite (FRAME first ltac:(cbn; auto)),(FRAME second ltac:(cbn; auto)); reflexivity.
Qed.
Theorem memory_affine_pair_choice_frame original current extent count first second first_term second_term :
  temp_agree [first;second] original current ->
  memory_affine_pair_choice_check (memory_multi_pointer_locations current extent) count first second first_term second_term =
  memory_affine_pair_choice_check (memory_multi_pointer_locations original extent) count first second first_term second_term.
Proof.
  intro FRAME; unfold memory_affine_pair_choice_check; destruct (memory_affine_pair_fast first_term second_term).
  - unfold memory_affine_endpoint_pair_check; apply memory_boolean_scan_ext; intro index.
    f_equal; apply memory_affine_point_pair_frame; exact FRAME.
  - unfold memory_affine_range_pair_check; apply memory_boolean_scan_ext; intro first_index;
      apply memory_boolean_scan_ext; intro second_index; apply memory_affine_point_pair_frame; exact FRAME.
Qed.
Print Assumptions memory_affine_pair_choice_complete.
Print Assumptions memory_affine_pair_choice_frame.
