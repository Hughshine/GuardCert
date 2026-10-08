From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes Cop ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightPureExpr ClightRectangularStore ClightNoWrap
  ClightCountedLoop ClightTempFrame CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRuntimeReceipts
  GuardMemoryFiniteFootprint GuardMemoryFiniteAliasCondition GuardMemoryPointerCellComparison
  GuardMemoryBufferOffsets GuardMemoryPointerAccess GuardMemoryDynamicTensorLayout
  GuardMemoryDynamicTensorAccess GuardMemoryDynamicTensorBackend GuardMemoryMultiTensorBackend
  GuardMemoryMultiTensorAddressReceipts GuardMemoryRecursiveSource GuardMemoryBooleanScan
  GuardMemoryBooleanPairRectangle.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition multi_tensor_cursor_index dimensions counters :=
  match tensor_index_expression (map tensor_dimension_code dimensions)
    (map (fun identifier => Etempvar identifier type_int32s) counters) with
  | Some code => code | None => rect_constant 0 end.
Definition multi_tensor_cursor_address dimensions array counters := Ebinop Oadd
  (Etempvar array (Tpointer type_int32s noattr)) (multi_tensor_cursor_index dimensions counters)
  (Tpointer type_int32s noattr).
Definition multi_tensor_coordinate_cell array coordinates : MemCell :=
  {| arr_id := array; arr_index := coordinates |}.

Lemma multi_tensor_cursor_operands ge locals temps memory counters coordinates :
  memory_nest_bindings counters coordinates temps ->
  Forall2 (tensor_operand ge locals temps memory)
    (map (fun identifier => Etempvar identifier type_int32s) counters) coordinates.
Proof.
  intro WORDS; induction WORDS; cbn [map]; constructor; [|exact IHWORDS].
  split; [reflexivity|split; constructor; exact H].
Qed.

Theorem multi_tensor_cursor_address_receipt dimensions sizes original temps memory
    array counters coordinates ge locals :
  tensor_layout_flag sizes = true -> tensor_dimension_view dimensions sizes temps ->
  temp_agree [array] original temps -> memory_nest_bindings counters coordinates temps ->
  memory_cell_access (multi_tensor_locations original sizes) memory
    (multi_tensor_coordinate_cell array coordinates) Readable ->
  memory_cell_address_binding (fun _ => multi_tensor_cursor_address dimensions array counters)
    (multi_tensor_locations original sizes) (Entry ge locals temps memory)
    (multi_tensor_coordinate_cell array coordinates).
Proof.
  intros LAYOUT DIMENSIONS FRAME BINDINGS [location [RESOLVE ACCESS]].
  destruct (@multi_tensor_location_inverse original sizes _ location RESOLVE)
    as [block [base [index [POINTER [INDEX LOCATION]]]]]; subst location.
  cbn [multi_tensor_coordinate_cell arr_id arr_index] in POINTER,INDEX.
  assert (LENGTH : length (map tensor_dimension_code dimensions) =
      length (map (fun identifier => Etempvar identifier type_int32s) counters)).
  { rewrite !length_map; transitivity (length sizes); [apply (Forall2_length DIMENSIONS)|].
    rewrite (@tensor_index_rank sizes coordinates index INDEX).
    symmetry; apply (Forall2_length BINDINGS). }
  destruct (@tensor_index_expression_exists (map tensor_dimension_code dimensions)
    (map (fun identifier => Etempvar identifier type_int32s) counters) LENGTH) as [code CODE].
  pose proof (@tensor_dimension_view_evaluation ge locals temps memory dimensions sizes DIMENSIONS) as DIMS.
  pose proof (@multi_tensor_cursor_operands ge locals temps memory counters coordinates BINDINGS) as COORDS.
  assert (TYPE : typeof code = type_int32s) by (eapply tensor_index_expression_type; exact CODE).
  assert (PURE : pure_scalar code).
  { eapply tensor_index_expression_pure; [eapply tensor_operands_pure; exact DIMS|
      eapply tensor_operands_pure; exact COORDS|exact CODE]. }
  assert (VALUE : eval_expr ge locals temps memory code (Vint (Int.repr index))).
  { exact (@tensor_index_expression_evaluation ge locals temps memory (map tensor_dimension_code dimensions)
      (map (fun identifier => Etempvar identifier type_int32s) counters) sizes coordinates code index
      DIMS COORDS CODE INDEX). }
  assert (RANGE : signed_range index).
  { pose proof (@tensor_index_bounds sizes coordinates index INDEX);
      pose proof (@tensor_layout_flag_sound sizes LAYOUT); unfold signed_range;
      pose proof Int.min_signed_neg; lia. }
  exists (MemoryLocation Mint32 block (memory_pointer_buffer_offset base index)),
    (Ptrofs.add base (Ptrofs.repr (4 * index))).
  split; [exact RESOLVE|split; [reflexivity|split]].
  - symmetry; apply memory_pointer_buffer_address.
  - unfold multi_tensor_cursor_address,multi_tensor_cursor_index; rewrite CODE.
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

Definition multi_tensor_pair_test dimensions left right first second := memory_pointer_cells_test
  (multi_tensor_cursor_address dimensions first left) (multi_tensor_cursor_address dimensions second right).
Definition multi_tensor_pair_scan dimensions left right bounds flag first second :=
  memory_boolean_pair_rectangle_statement left right bounds
    (memory_boolean_test_body flag (multi_tensor_pair_test dimensions left right first second)).
Definition multi_tensor_pair_check locations counts first second := memory_boolean_pair_rectangle_result
  (fun a b => memory_cell_pair_address_check locations
    (multi_tensor_coordinate_cell first a) (multi_tensor_coordinate_cell second b)) counts.

Lemma multi_tensor_pair_test_evaluation dimensions sizes original temps memory
    left right first second a b ge locals :
  first <> second -> tensor_layout_flag sizes = true -> tensor_dimension_view dimensions sizes temps ->
  temp_agree [first;second] original temps ->
  memory_nest_bindings left a temps -> memory_nest_bindings right b temps ->
  memory_cell_access (multi_tensor_locations original sizes) memory (multi_tensor_coordinate_cell first a) Readable ->
  memory_cell_access (multi_tensor_locations original sizes) memory (multi_tensor_coordinate_cell second b) Readable ->
  expression_test (multi_tensor_pair_test dimensions left right first second) (Entry ge locals temps memory)
    (memory_cell_pair_address_check (multi_tensor_locations original sizes)
      (multi_tensor_coordinate_cell first a) (multi_tensor_coordinate_cell second b)).
Proof.
  intros DISTINCT LAYOUT DIMENSIONS FRAME LEFT RIGHT FIRST SECOND.
  assert (LEFT_FRAME : temp_agree [first] original temps).
  { eapply temp_agree_weaken; [|exact FRAME]; cbn; tauto. }
  assert (RIGHT_FRAME : temp_agree [second] original temps).
  { eapply temp_agree_weaken; [|exact FRAME]; cbn; tauto. }
  destruct (@multi_tensor_cursor_address_receipt dimensions sizes original temps memory first left a ge locals
    LAYOUT DIMENSIONS LEFT_FRAME LEFT FIRST)
    as [loc1 [ofs1 [RES1 [CHUNK1 [OFFSET1 [PURE1 [TYPE1 [VALUE1 [VALID1 ALIGN1]]]]]]]]].
  destruct (@multi_tensor_cursor_address_receipt dimensions sizes original temps memory second right b ge locals
    LAYOUT DIMENSIONS RIGHT_FRAME RIGHT SECOND)
    as [loc2 [ofs2 [RES2 [CHUNK2 [OFFSET2 [PURE2 [TYPE2 [VALUE2 [VALID2 ALIGN2]]]]]]]]].
  unfold memory_cell_pair_address_check; destruct memory_cell_identity_dec as [SAME|DIFFERENT].
  - apply (f_equal arr_id) in SAME; cbn in SAME; contradiction.
  - rewrite RES1,RES2,OFFSET1,OFFSET2,<-memory_pointer_eq_unsigned.
    unfold multi_tensor_pair_test; cbn in VALUE1,VALUE2,VALID1,VALID2.
    eapply memory_pointer_cells_test_evaluation;
      [exact TYPE1|exact TYPE2|exact VALUE1|exact VALUE2|exact VALID1|exact VALID2].
Qed.

Theorem multi_tensor_pair_scan_execution dimensions sizes original current memory
    left right bounds counts flag first second live fe ge locals accepted :
  first <> second -> tensor_layout_flag sizes = true -> tensor_dimension_view dimensions sizes original ->
  NoDup (left++right) ->
  (forall identifier, In identifier (left++right) ->
    ~ In identifier (bounds++first::second::tensor_dimension_registers dimensions++live) /\ identifier <> flag) ->
  ~ In flag (bounds++first::second::tensor_dimension_registers dimensions++live) ->
  Forall (fun count => 0 <= count /\ signed_range count) counts ->
  length left = length counts -> length right = length counts ->
  memory_nest_bindings bounds counts original ->
  (forall coordinates, Forall2 (fun coordinate count => 0 <= coordinate < count) coordinates counts ->
    memory_cell_access (multi_tensor_locations original sizes) memory
      (multi_tensor_coordinate_cell first coordinates) Readable /\
    memory_cell_access (multi_tensor_locations original sizes) memory
      (multi_tensor_coordinate_cell second coordinates) Readable) ->
  temp_agree (bounds++first::second::tensor_dimension_registers dimensions++live) original current ->
  current!flag = Some (memory_boolean_word accepted) ->
  exists after,
    exec_stmt fe ge locals current memory
      (multi_tensor_pair_scan dimensions left right bounds flag first second) E0 after memory Out_normal /\
    temp_agree (bounds++first::second::tensor_dimension_registers dimensions++live) current after /\
    after!flag = Some (memory_boolean_word
      (accepted && multi_tensor_pair_check (multi_tensor_locations original sizes) counts first second)).
Proof.
  intros DISTINCT LAYOUT DIMENSIONS UNIQUE FRESH FLAG_FRESH RANGES LEFT_LENGTH RIGHT_LENGTH
    WORDS RECEIPTS FRAME FLAG.
  eapply memory_boolean_pair_rectangle_execution; eauto.
  intros a b temps good A B LEFT RIGHT PUBLIC GOOD.
  apply memory_boolean_test_body_execution; [|exact GOOD|].
  - intro BAD; repeat rewrite in_app_iff in BAD; destruct BAD as [BAD|[BAD|BAD]].
    + destruct (FRESH flag ltac:(apply in_or_app; left; exact BAD)) as [_ FALSE]; apply FALSE; reflexivity.
    + destruct (FRESH flag ltac:(apply in_or_app; right; exact BAD)) as [_ FALSE]; apply FALSE; reflexivity.
    + apply FLAG_FRESH; apply in_app_iff; exact BAD.
  - eapply multi_tensor_pair_test_evaluation; [exact DISTINCT|exact LAYOUT| | |exact LEFT|exact RIGHT|
      exact (proj1 (RECEIPTS a A))|exact (proj2 (RECEIPTS b B))].
    + eapply tensor_dimension_view_frame; [|exact DIMENSIONS].
      eapply temp_agree_weaken; [|exact PUBLIC]; intros identifier MEMBER;
        repeat rewrite in_app_iff in *; cbn in *; repeat rewrite in_app_iff in *; tauto.
    + eapply temp_agree_weaken; [|exact PUBLIC]; cbn; intros identifier MEMBER;
        repeat rewrite in_app_iff in *; cbn in *; repeat rewrite in_app_iff in *; tauto.
Qed.

Print Assumptions multi_tensor_cursor_operands.
Print Assumptions multi_tensor_cursor_address_receipt.
Print Assumptions multi_tensor_pair_test_evaluation.
Print Assumptions multi_tensor_pair_scan_execution.
