From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes Cop ClightBigstep.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightPureExpr ClightRectangularStore ClightNoWrap
  ClightCountedLoop ClightTempFrame CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRuntimeReceipts
  GuardMemoryFiniteFootprint GuardMemoryFiniteAliasCondition GuardMemoryPointerCellComparison
  GuardMemoryBufferOffsets GuardMemoryPointerAccess GuardMemoryArrayBackend
  GuardMemoryFlatArrayBackend GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorAccess
  GuardMemoryDynamicTensorBackend GuardMemoryMultiTensorBackend
  GuardMemoryMultiTensorAddressReceipts GuardMemoryRecursiveSource GuardMemoryMultiTensorPairScan.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Static access templates are evaluated over private source-domain cursors
    followed by stable scalar parameters. Access coordinates need not equal
    the cursor coordinates, and their rank need not equal the loop rank. *)
Definition multi_tensor_affine_index dimensions identifiers (access : AccessFunction) :=
  match tensor_index_expression (map tensor_dimension_code dimensions)
    (map (flat_affine_expression
      (map (fun identifier => Etempvar identifier type_int32s) identifiers)) (snd access)) with
  | Some code => code | None => rect_constant 0 end.
Definition multi_tensor_affine_address dimensions identifiers (access : AccessFunction) :=
  Ebinop Oadd (Etempvar (fst access) (Tpointer type_int32s noattr))
    (multi_tensor_affine_index dimensions identifiers access) (Tpointer type_int32s noattr).

Lemma multi_tensor_flat_linear_pure codes coefficients :
  Forall pure_scalar codes -> pure_scalar (flat_linear_expression codes coefficients).
Proof.
  intro PURE; revert coefficients; induction PURE; intros coefficients; destruct coefficients;
    cbn [flat_linear_expression]; unfold operand_sum,operand_product,rect_constant;
    repeat match goal with |- context [if ?test then _ else _] => destruct test end;
    repeat constructor; auto.
Qed.
Lemma multi_tensor_flat_affine_pure codes term :
  Forall pure_scalar codes -> pure_scalar (flat_affine_expression codes term).
Proof.
  intro PURE; unfold flat_affine_expression,operand_sum; constructor.
  - apply multi_tensor_flat_linear_pure; exact PURE.
  - unfold rect_constant; destruct (snd term <? 0); repeat constructor.
Qed.
Lemma multi_tensor_operands_values ge locals temps memory codes values :
  Forall2 (tensor_operand ge locals temps memory) codes values ->
  Forall2 (MemoryBody.operand_view ge locals temps memory) codes values.
Proof. intro WORDS; induction WORDS; constructor; [split; [exact (proj1 H)|exact (proj2 (proj2 H))]|exact IHWORDS]. Qed.
Lemma multi_tensor_affine_operands ge locals temps memory codes values coordinates :
  Forall2 (tensor_operand ge locals temps memory) codes values ->
  Forall2 (tensor_operand ge locals temps memory)
    (map (flat_affine_expression codes) coordinates) (affine_product coordinates values).
Proof.
  intro WORDS; induction coordinates; cbn [map affine_product]; constructor; [|exact IHcoordinates].
  split; [apply flat_affine_type|split].
  - apply multi_tensor_flat_affine_pure; eapply tensor_operands_pure; exact WORDS.
  - apply flat_affine_evaluation; apply multi_tensor_operands_values; exact WORDS.
Qed.

Theorem multi_tensor_affine_address_receipt dimensions sizes original temps memory
    identifiers values access ge locals :
  tensor_layout_flag sizes = true -> tensor_dimension_view dimensions sizes temps ->
  temp_agree [fst access] original temps -> memory_nest_bindings identifiers values temps ->
  memory_cell_access (multi_tensor_locations original sizes) memory (exact_cell access values) Readable ->
  memory_cell_address_binding (fun _ => multi_tensor_affine_address dimensions identifiers access)
    (multi_tensor_locations original sizes) (Entry ge locals temps memory) (exact_cell access values).
Proof.
  intros LAYOUT DIMENSIONS FRAME BINDINGS [location [RESOLVE ACCESS]].
  destruct (@multi_tensor_location_inverse original sizes _ location RESOLVE)
    as [block [base [index [POINTER [INDEX LOCATION]]]]]; subst location.
  destruct access as [array coordinates].
  change (original!array = Some (Vptr block base)) in POINTER.
  change (tensor_index sizes (affine_product coordinates values) = Some index) in INDEX.
  set (codes := map (fun identifier => Etempvar identifier type_int32s) identifiers).
  pose proof (@multi_tensor_cursor_operands ge locals temps memory identifiers values BINDINGS) as WORDS.
  pose proof (@multi_tensor_affine_operands ge locals temps memory codes values coordinates WORDS) as COORDS.
  assert (LENGTH : length (map tensor_dimension_code dimensions) =
      length (map (flat_affine_expression codes) coordinates)).
  { rewrite !length_map; pose proof (Forall2_length DIMENSIONS);
      pose proof (@tensor_index_rank sizes _ _ INDEX); unfold affine_product in *; rewrite length_map in *; lia. }
  destruct (@tensor_index_expression_exists (map tensor_dimension_code dimensions)
    (map (flat_affine_expression codes) coordinates) LENGTH) as [code CODE].
  pose proof (@tensor_dimension_view_evaluation ge locals temps memory dimensions sizes DIMENSIONS) as DIMS.
  assert (TYPE : typeof code = type_int32s) by (eapply tensor_index_expression_type; exact CODE).
  assert (PURE : pure_scalar code).
  { eapply tensor_index_expression_pure; [eapply tensor_operands_pure; exact DIMS|
      eapply tensor_operands_pure; exact COORDS|exact CODE]. }
  assert (VALUE : eval_expr ge locals temps memory code (Vint (Int.repr index))).
  { exact (@tensor_index_expression_evaluation ge locals temps memory
      (map tensor_dimension_code dimensions) (map (flat_affine_expression codes) coordinates)
      sizes (affine_product coordinates values) code index DIMS COORDS CODE INDEX). }
  assert (RANGE : signed_range index).
  { pose proof (@tensor_index_bounds sizes _ _ INDEX); pose proof (@tensor_layout_flag_sound sizes LAYOUT);
      unfold signed_range; pose proof Int.min_signed_neg; lia. }
  exists (MemoryLocation Mint32 block (memory_pointer_buffer_offset base index)),
    (Ptrofs.add base (Ptrofs.repr (4 * index))).
  split; [exact RESOLVE|split; [reflexivity|split]].
  - symmetry; apply memory_pointer_buffer_address.
  - unfold multi_tensor_affine_address,multi_tensor_affine_index; cbn [fst snd]; fold codes; rewrite CODE.
    split; [constructor; [constructor|exact PURE]|split; [reflexivity|split]].
    + eapply eval_Ebinop; [constructor; rewrite FRAME by (cbn; auto); exact POINTER|exact VALUE|].
      cbn [typeof]; rewrite TYPE; apply memory_pointer_add; exact RANGE.
    + rewrite memory_pointer_buffer_address; cbn [entry_memory location_block location_offset].
      destruct ACCESS as [PERMISSIONS ALIGN]; split; [|exact ALIGN].
      apply Mem.valid_pointer_nonempty_perm; eapply Mem.perm_implies.
      * apply PERMISSIONS; change (memory_pointer_buffer_offset base index <= memory_pointer_buffer_offset base index <
          memory_pointer_buffer_offset base index + 4); lia.
      * constructor.
Qed.

Definition multi_tensor_affine_pair_test dimensions left right (first second : AccessFunction) :=
  memory_pointer_cells_test (multi_tensor_affine_address dimensions left first)
    (multi_tensor_affine_address dimensions right second).

Lemma multi_tensor_affine_pair_test_evaluation dimensions sizes original temps memory
    left right first second a b ge locals :
  fst first <> fst second -> tensor_layout_flag sizes = true -> tensor_dimension_view dimensions sizes temps ->
  temp_agree [fst first;fst second] original temps ->
  memory_nest_bindings left a temps -> memory_nest_bindings right b temps ->
  memory_cell_access (multi_tensor_locations original sizes) memory (exact_cell first a) Readable ->
  memory_cell_access (multi_tensor_locations original sizes) memory (exact_cell second b) Readable ->
  expression_test (multi_tensor_affine_pair_test dimensions left right first second) (Entry ge locals temps memory)
    (memory_cell_pair_address_check (multi_tensor_locations original sizes) (exact_cell first a) (exact_cell second b)).
Proof.
  intros DISTINCT LAYOUT DIMENSIONS FRAME LEFT RIGHT FIRST SECOND.
  assert (LEFT_FRAME : temp_agree [fst first] original temps).
  { eapply temp_agree_weaken; [|exact FRAME]; cbn; tauto. }
  assert (RIGHT_FRAME : temp_agree [fst second] original temps).
  { eapply temp_agree_weaken; [|exact FRAME]; cbn; tauto. }
  destruct (@multi_tensor_affine_address_receipt dimensions sizes original temps memory left a first ge locals
    LAYOUT DIMENSIONS LEFT_FRAME LEFT FIRST)
    as [loc1 [ofs1 [RES1 [CHUNK1 [OFFSET1 [PURE1 [TYPE1 [VALUE1 [VALID1 ALIGN1]]]]]]]]].
  destruct (@multi_tensor_affine_address_receipt dimensions sizes original temps memory right b second ge locals
    LAYOUT DIMENSIONS RIGHT_FRAME RIGHT SECOND)
    as [loc2 [ofs2 [RES2 [CHUNK2 [OFFSET2 [PURE2 [TYPE2 [VALUE2 [VALID2 ALIGN2]]]]]]]]].
  unfold memory_cell_pair_address_check; destruct memory_cell_identity_dec as [SAME|DIFFERENT].
  - apply (f_equal arr_id) in SAME; destruct first,second; cbn in SAME,DISTINCT; contradiction.
  - rewrite RES1,RES2,OFFSET1,OFFSET2,<-memory_pointer_eq_unsigned.
    unfold multi_tensor_affine_pair_test; cbn in VALUE1,VALUE2,VALID1,VALID2.
    eapply memory_pointer_cells_test_evaluation;
      [exact TYPE1|exact TYPE2|exact VALUE1|exact VALUE2|exact VALID1|exact VALID2].
Qed.

Print Assumptions multi_tensor_flat_linear_pure.
Print Assumptions multi_tensor_flat_affine_pure.
Print Assumptions multi_tensor_operands_values.
Print Assumptions multi_tensor_affine_operands.
Print Assumptions multi_tensor_affine_address_receipt.
Print Assumptions multi_tensor_affine_pair_test_evaluation.
