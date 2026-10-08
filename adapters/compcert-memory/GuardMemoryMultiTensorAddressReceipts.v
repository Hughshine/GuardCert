From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightPureExpr ClightRectangularStore ClightNoWrap
  ClightCountedLoop ClightTempFrame ClightStraightLine CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryRuntimeReceipts GuardMemoryLoopTrace GuardMemoryFiniteFootprint GuardMemoryFiniteAliasCondition
  GuardMemoryBufferOffsets GuardMemoryPointerAccess GuardMemoryDynamicTensorLayout
  GuardMemoryDynamicTensorAccess GuardMemoryDynamicTensorBackend GuardMemoryMultiTensorBackend
  GuardMemoryMultiTensorSequence GuardMemoryMultiTensorFrame GuardMemoryMultiTensorSourceRegion
  GuardMemoryRecursiveSource GuardMemoryScalarLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma tensor_index_rank sizes coordinates offset :
  tensor_index sizes coordinates = Some offset -> length sizes = length coordinates.
Proof.
  revert coordinates offset; induction sizes as [|size sizes IH]; intros [|coordinate coordinates] offset INDEX;
    cbn [tensor_index] in INDEX; try discriminate; [reflexivity|].
  destruct ((0 <=? coordinate) && (coordinate <? size)); [|discriminate].
  destruct (tensor_index sizes coordinates) as [suffix|] eqn:TAIL; [|discriminate].
  cbn [length]; f_equal; eapply IH; exact TAIL.
Qed.
Lemma tensor_index_expression_exists dimensions coordinates : length dimensions = length coordinates ->
  exists code, tensor_index_expression dimensions coordinates = Some code.
Proof.
  revert coordinates; induction dimensions as [|dimension dimensions IH]; intros [|coordinate coordinates] LENGTH;
    cbn [length] in LENGTH; try discriminate.
  - eexists; reflexivity.
  - destruct (IH coordinates ltac:(lia)) as [code CODE]; cbn [tensor_index_expression]; rewrite CODE; eexists; reflexivity.
Qed.

Definition multi_tensor_cell_index dimensions cell :=
  match tensor_index_expression (map tensor_dimension_code dimensions) (map rect_constant (arr_index cell)) with
  | Some index => index | None => rect_constant 0 end.
Definition multi_tensor_cell_address dimensions cell := Ebinop Oadd
  (Etempvar (arr_id cell) (Tpointer type_int32s noattr)) (multi_tensor_cell_index dimensions cell)
  (Tpointer type_int32s noattr).

Lemma multi_tensor_constant_operands ge locals temps memory coordinates :
  Forall2 (tensor_operand ge locals temps memory) (map rect_constant coordinates) coordinates.
Proof.
  induction coordinates as [|coordinate coordinates IH]; cbn [map]; constructor; [|exact IH].
  split; [apply rect_constant_type|split; [|apply rect_constant_evaluation]].
  exact (GuardMemoryAffineSourceExpressions.memory_source_affine_pure
    (GuardMemoryAffineSourceExpressions.MemorySourceConstant coordinate)).
Qed.

(** Source permissions license pure address comparisons. They do not license
    an entry arithmetic computation using a value initialized by a later store. *)
Theorem multi_tensor_cell_address_receipt dimensions sizes temps memory cell ge locals :
  tensor_layout_flag sizes = true -> tensor_dimension_view dimensions sizes temps ->
  memory_cell_access (multi_tensor_locations temps sizes) memory cell Readable ->
  memory_cell_address_binding (multi_tensor_cell_address dimensions) (multi_tensor_locations temps sizes)
    (Entry ge locals temps memory) cell.
Proof.
  intros LAYOUT DIMENSIONS [location [RESOLVE ACCESS]].
  destruct (@multi_tensor_location_inverse temps sizes cell location RESOLVE)
    as [block [base [index [POINTER [INDEX LOCATION]]]]]; subst location.
  assert (LENGTH : length (map tensor_dimension_code dimensions) = length (map rect_constant (arr_index cell))).
  { rewrite !length_map; pose proof (Forall2_length DIMENSIONS); pose proof (@tensor_index_rank sizes _ _ INDEX); lia. }
  destruct (@tensor_index_expression_exists (map tensor_dimension_code dimensions)
    (map rect_constant (arr_index cell)) LENGTH) as [code CODE].
  pose proof (@tensor_dimension_view_evaluation ge locals temps memory dimensions sizes DIMENSIONS) as WORDS.
  pose proof (@multi_tensor_constant_operands ge locals temps memory (arr_index cell)) as COORDINATES.
  assert (TYPE : typeof code = type_int32s) by (eapply tensor_index_expression_type; exact CODE).
  assert (PURE : pure_scalar code).
  { eapply tensor_index_expression_pure; [eapply tensor_operands_pure; exact WORDS|
      eapply tensor_operands_pure; exact COORDINATES|exact CODE]. }
  assert (VALUE : eval_expr ge locals temps memory code (Vint (Int.repr index))).
  { exact (@tensor_index_expression_evaluation ge locals temps memory (map tensor_dimension_code dimensions)
      (map rect_constant (arr_index cell)) sizes (arr_index cell) code index WORDS COORDINATES CODE INDEX). }
  assert (RANGE : signed_range index).
  { pose proof (@tensor_index_bounds sizes _ _ INDEX); pose proof (@tensor_layout_flag_sound sizes LAYOUT).
    unfold signed_range; pose proof Int.min_signed_neg; lia. }
  exists (MemoryLocation Mint32 block (memory_pointer_buffer_offset base index)),
    (Ptrofs.add base (Ptrofs.repr (4 * index))).
  split; [exact RESOLVE|split; [reflexivity|split]].
  - symmetry; apply memory_pointer_buffer_address.
  - unfold multi_tensor_cell_address,multi_tensor_cell_index; rewrite CODE; split; [constructor; [constructor|exact PURE]|].
    split; [reflexivity|split].
    + eapply eval_Ebinop; [constructor; exact POINTER|exact VALUE|].
      cbn [typeof]; rewrite TYPE; apply memory_pointer_add; exact RANGE.
    + rewrite memory_pointer_buffer_address; cbn [entry_memory location_block location_offset].
      destruct ACCESS as [PERMISSIONS ALIGN]; split; [|exact ALIGN].
      apply Mem.valid_pointer_nonempty_perm; eapply Mem.perm_implies.
      * apply PERMISSIONS; change (memory_pointer_buffer_offset base index <= memory_pointer_buffer_offset base index <
          memory_pointer_buffer_offset base index + 4); lia.
      * constructor.
Qed.

Theorem multi_tensor_loop_entry_address_receipts dimensions sizes temps memory final source parameters ge locals :
  tensor_layout_flag sizes = true -> tensor_dimension_view dimensions sizes temps ->
  L.loop_semantics source parameters (RuntimeState (multi_tensor_locations temps sizes) memory)
    (RuntimeState (multi_tensor_locations temps sizes) final) ->
  Forall (memory_cell_address_binding (multi_tensor_cell_address dimensions) (multi_tensor_locations temps sizes)
    (Entry ge locals temps memory)) (memory_events_footprint (memory_loop_trace source parameters)).
Proof.
  intros LAYOUT DIMENSIONS SOURCE; pose proof (@memory_loop_entry_footprint_readable source parameters _ _ SOURCE) as RECEIPTS.
  eapply Forall_impl; [|exact RECEIPTS]; intros cell RECEIPT; eapply multi_tensor_cell_address_receipt; eassumption.
Qed.

(** This connects actual source execution to the existing address-test library.
    The footprint list is an entry-indexed proof/specification witness. A static
    compiler must still realize its runtime coverage with bounded scans or a
    proved symbolic envelope; it cannot specialize emitted code to unknown
    entry values by assuming this witness was computed at compile time. *)
Theorem multi_tensor_source_entry_address_receipts dimensions nest scalars pointers
    (items : list (multi_tensor_source_statement dimensions (memory_nest_iterators nest ++ scalars)))
    fe ge locals counts scalar_values sizes temps memory after final :
  flatten_region (memory_nest_leaf nest) = map mt_statement items ->
  memory_nest_shapes nest -> memory_nest_fresh nest -> NoDup (memory_nest_iterators nest ++ scalars) ->
  (forall identifier, In identifier (memory_nest_iterators nest) ->
    ~ In identifier (pointers ++ tensor_dimension_registers dimensions ++ scalars)) ->
  length counts = length (memory_nest_iterators nest) ->
  Forall (fun count => count <> O /\ signed_range (Z.of_nat count)) counts ->
  memory_nest_bindings (memory_nest_bounds nest) (map Z.of_nat counts) temps -> memory_nest_initial nest temps ->
  tensor_layout_flag sizes = true -> tensor_dimension_view dimensions sizes temps ->
  memory_nest_bindings scalars scalar_values temps ->
  multi_tensor_pointer_check pointers (map mt_instruction items) = true ->
  multi_tensor_body_box items counts scalar_values sizes = true ->
  exec_stmt fe ge locals temps memory (memory_nest_source nest) E0 after final Out_normal ->
  Forall (memory_cell_address_binding (multi_tensor_cell_address dimensions) (multi_tensor_locations temps sizes)
    (Entry ge locals temps memory))
    (memory_events_footprint (memory_loop_trace
      (memory_scalar_rectangle 0 (length counts) (length scalar_values) (map mt_instruction items))
      (map Z.of_nat counts ++ scalar_values))).
Proof.
  intros BODY SHAPES FRESH UNIQUE PROTECTED LENGTH COUNTS BOUNDS INITIAL LAYOUT DIMENSIONS SCALARS POINTERS BOX SOURCE.
  destruct (@multi_tensor_source_region_decode dimensions nest scalars pointers items fe ge locals
    counts scalar_values sizes temps memory after final BODY SHAPES FRESH UNIQUE PROTECTED LENGTH COUNTS BOUNDS INITIAL
    LAYOUT DIMENSIONS SCALARS POINTERS BOX SOURCE) as [MODEL _].
  eapply multi_tensor_loop_entry_address_receipts; eassumption.
Qed.

Print Assumptions tensor_index_rank.
Print Assumptions tensor_index_expression_exists.
Print Assumptions multi_tensor_constant_operands.
Print Assumptions multi_tensor_cell_address_receipt.
Print Assumptions multi_tensor_loop_entry_address_receipts.
Print Assumptions multi_tensor_source_entry_address_receipts.
