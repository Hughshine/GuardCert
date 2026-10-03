From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightIndexedArray ClightRectangularStore ClightRectangularRegion CompCertStoreSchedule
  RectangularSchedule CompCertMemoryActions ClightCondition ClightTempFrame PolCertNestedClight.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles
  GuardMemoryPolyhedral GuardMemoryLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Module MemoryNested := PolCertNestedClightFor GuardMemoryInstr GuardMemoryIRs.Loop.
Module MemoryBody := MemoryNested.B.

(** Operand expressions may contain affine arithmetic and checked division.
    The instruction backend consumes their proved evaluations. *)
Definition operand_product code factor :=
  Ebinop Omul code (rect_constant factor) type_int32s.
Definition operand_sum first second := Ebinop Oadd first second type_int32s.
Definition array_index_expression d row column :=
  operand_sum (operand_product row (rectangle_stride d)) column.
Definition array_payload_expression d row column :=
  operand_sum (operand_sum (operand_product row (rectangle_coefficient d)) column)
    (rect_constant (rectangle_bias d)).
Definition array_write_statement d array row column :=
  Sassign (indexed_array_lvalue d array (array_index_expression d row column))
    (array_payload_expression d row column).

Lemma operand_product_evaluation ge locals temps memory code factor value :
  typeof code = type_int32s ->
  eval_expr ge locals temps memory code (Vint (Int.repr value)) ->
  eval_expr ge locals temps memory (operand_product code factor) (Vint (Int.repr (value * factor))).
Proof.
  intros TYPE VALUE; eapply eval_Ebinop; [exact VALUE|apply rect_constant_evaluation|].
  rewrite TYPE, rect_constant_type.
  change (Some (Vint (Int.mul (Int.repr value) (Int.repr factor))) =
    Some (Vint (Int.repr (value * factor)))).
  rewrite rect_integer_multiply; reflexivity.
Qed.
Lemma operand_sum_evaluation ge locals temps memory first second x y :
  typeof first = type_int32s -> typeof second = type_int32s ->
  eval_expr ge locals temps memory first (Vint (Int.repr x)) ->
  eval_expr ge locals temps memory second (Vint (Int.repr y)) ->
  eval_expr ge locals temps memory (operand_sum first second) (Vint (Int.repr (x + y))).
Proof.
  intros FIRST SECOND X Y; eapply eval_Ebinop; [exact X|exact Y|].
  rewrite FIRST,SECOND.
  change (Some (Vint (Int.add (Int.repr x) (Int.repr y))) = Some (Vint (Int.repr (x + y)))).
  rewrite rect_integer_add; reflexivity.
Qed.
Lemma array_index_evaluation d ge locals temps memory row column i j :
  typeof row = type_int32s -> typeof column = type_int32s ->
  eval_expr ge locals temps memory row (Vint (Int.repr i)) ->
  eval_expr ge locals temps memory column (Vint (Int.repr j)) ->
  eval_expr ge locals temps memory (array_index_expression d row column)
    (Vint (Int.repr (i * rectangle_stride d + j))).
Proof. intros; apply operand_sum_evaluation; [reflexivity|assumption|apply operand_product_evaluation; assumption|assumption]. Qed.
Lemma array_payload_evaluation d ge locals temps memory row column i j :
  typeof row = type_int32s -> typeof column = type_int32s ->
  eval_expr ge locals temps memory row (Vint (Int.repr i)) ->
  eval_expr ge locals temps memory column (Vint (Int.repr j)) ->
  eval_expr ge locals temps memory (array_payload_expression d row column)
    (Vint (Int.repr (i * rectangle_coefficient d + j + rectangle_bias d))).
Proof.
  intros TYPE_ROW TYPE_COLUMN ROW COLUMN; apply operand_sum_evaluation;
    [reflexivity|apply rect_constant_type| |apply rect_constant_evaluation].
  apply operand_sum_evaluation; [reflexivity|exact TYPE_COLUMN| |exact COLUMN].
  apply operand_product_evaluation; assumption.
Qed.

Lemma array_write_execution d fe ge locals temps memory array block row column i j final :
  rect_array_binding d ge locals array block ->
  typeof row = type_int32s -> typeof column = type_int32s ->
  eval_expr ge locals temps memory row (Vint (Int.repr i)) ->
  eval_expr ge locals temps memory column (Vint (Int.repr j)) ->
  0 <= i * rectangle_stride d + j < rectangle_extent d ->
  Mem.store Mint32 memory block (4 * (i * rectangle_stride d + j))
    (Vint (Int.repr (i * rectangle_coefficient d + j + rectangle_bias d))) = Some final ->
  @rectangle_layout_valid d ->
  exec_stmt fe ge locals temps memory (array_write_statement d array row column) E0 temps final Out_normal.
Proof.
  intros ARRAY TYPE_ROW TYPE_COLUMN ROW COLUMN INDEX STORE LAYOUT.
  eapply exec_Sassign with (loc := block) (ofs := Ptrofs.repr (4 * (i * rectangle_stride d + j)))
    (bf := Full) (v := Vint (Int.repr (i * rectangle_coefficient d + j + rectangle_bias d)))
    (v2 := Vint (Int.repr (i * rectangle_coefficient d + j + rectangle_bias d))).
  - eapply indexed_array_lvalue_evaluation with (d := d); [exact LAYOUT|reflexivity|exact ARRAY| |exact INDEX].
    apply array_index_evaluation; assumption.
  - apply array_payload_evaluation; assumption.
  - reflexivity.
  - apply assign_loc_value with (chunk := Mint32); [reflexivity|].
    cbn [Mem.storev]; rewrite Ptrofs.unsigned_repr by
      (apply (@rect_small_offset_bound d LAYOUT); unfold rectangle_layout_valid in LAYOUT; lia).
    destruct (zle (4 * (i * rectangle_stride d + j) + size_chunk Mint32) Ptrofs.modulus); [exact STORE|].
    exfalso; pose proof (@rect_small_offset_bound d LAYOUT
      (4 * (i * rectangle_stride d + j) + 4) ltac:(lia)) as END.
    unfold Ptrofs.max_unsigned in END; change (size_chunk Mint32) with 4 in *; lia.
Qed.

Lemma flat_array_location_inverse array block extent index location :
  flat_array_locations array block extent (point_cell array index) = Some location ->
  0 <= index < extent /\ location = MemoryLocation Mint32 block (4 * index).
Proof.
  unfold flat_array_locations,point_cell; cbn [arr_id arr_index]; rewrite Pos.eqb_refl.
  destruct ((0 <=? index) && (index <? extent)) eqn:BOUND; try discriminate.
  intro SAME; inversion SAME; subst; split; [|reflexivity].
  apply andb_true_iff in BOUND as [LOWER UPPER]; rewrite Z.leb_le in LOWER; rewrite Z.ltb_lt in UPPER; lia.
Qed.

Section BACKEND.
Variable d : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid d.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable array logical_array : ident.
Variable block : Values.block.
Hypothesis ARRAY : rect_array_binding d ge locals array block.
Definition array_memory_view state memory :=
  state = RuntimeState (flat_array_locations logical_array block (rectangle_extent d)) memory.
Definition lower_array_write instruction codes :=
  if GuardMemoryInstr.eqb instruction (rect_memory_write d logical_array) then
    match codes with [row;column] => Some (array_write_statement d array row column) | _ => None end
  else None.

Definition array_write_backend : MemoryBody.instruction_backend fe ge locals array_memory_view.
Proof.
  refine {| MemoryBody.lower_instruction := lower_array_write |}.
  intros instruction codes values code temps memory source target writes reads COMPILE OPERANDS RUN VIEW.
  unfold lower_array_write in COMPILE.
  destruct (GuardMemoryInstr.eqb instruction (rect_memory_write d logical_array)) eqn:INSTRUCTION; try discriminate.
  apply GuardMemoryInstr.eqb_eq in INSTRUCTION; subst instruction.
  destruct codes as [|row [|column [|extra rest]]]; try discriminate COMPILE.
  inversion COMPILE; subst code.
  inversion OPERANDS as [|rc i rs is ROW REST]; subst.
  inversion REST as [|cc j cs js COLUMN NIL]; subst.
  inversion NIL; subst.
  destruct ROW as [TYPE_ROW ROW]; destruct COLUMN as [TYPE_COLUMN COLUMN].
  unfold array_memory_view in VIEW; subst source.
  destruct RUN as [WRITES [READS RUN]]; subst writes reads.
  assert (POINT : memory_point (rect_memory_write d logical_array) i j
    (RuntimeState (flat_array_locations logical_array block (rectangle_extent d)) memory) target).
  { unfold memory_point, GuardMemoryInstr.instr_semantics; repeat split; assumption || reflexivity. }
  destruct target as [locations final].
  pose proof (@memory_point_locations (rect_memory_write d logical_array) i j _ _ POINT) as LOCATIONS.
  cbn in LOCATIONS; subst locations.
  destruct RUN as [write [loaded [WRITE [READ [_ ACTION]]]]].
  change (flat_array_locations logical_array block (rectangle_extent d)
    (exact_cell (rect_write_access d logical_array) [i;j]) = Some write) in WRITE.
  rewrite rect_write_cell in WRITE.
  destruct (@flat_array_location_inverse logical_array block (rectangle_extent d)
    (i * rectangle_stride d + j) write WRITE) as [BOUND _].
  assert (STORE : store_action_run (rectangle_action block (rectangle_stride d) (rect_payload d) (i,j)) memory final).
  { apply (proj1 (@rect_memory_write_execution d logical_array block i j memory final BOUND)); exact POINT. }
  exists final; split; [reflexivity|].
  eapply array_write_execution; eauto.
Defined.

Definition compile_memory_array_loop layout bounds live pool loop :=
  MemoryNested.checked_compile_nested_raw lower_array_write layout bounds live pool loop.

Theorem compile_memory_array_loop_correct layout bounds live pool loop code parameters temps source target memory :
  compile_memory_array_loop layout bounds live pool loop = Some code ->
  MemoryNested.A.typed_view layout parameters temps ->
  decision_run (Entry ge locals temps memory) (MemoryNested.G.range_guard layout bounds) true ->
  GuardMemoryIRs.Loop.loop_semantics loop parameters source target -> array_memory_view source memory ->
  exists target_temps target_memory, array_memory_view target target_memory /\
    temp_agree (layout ++ live) temps target_temps /\
    exec_stmt fe ge locals temps memory code E0 target_temps target_memory Out_normal.
Proof.
  intros COMPILE VIEW GUARD RUN MEMORY.
  eapply MemoryNested.checked_compile_nested_correct with (backend := array_write_backend); eauto.
Qed.

Theorem compile_memory_array_loop_within_correct layout bounds live pool loop code parameters temps source target memory :
  compile_memory_array_loop layout bounds live pool loop = Some code ->
  MemoryNested.A.typed_view layout parameters temps -> MemoryNested.A.env_within bounds parameters ->
  GuardMemoryIRs.Loop.loop_semantics loop parameters source target -> array_memory_view source memory ->
  exists target_temps target_memory, array_memory_view target target_memory /\
    temp_agree (layout ++ live) temps target_temps /\
    exec_stmt fe ge locals temps memory code E0 target_temps target_memory Out_normal.
Proof.
  unfold compile_memory_array_loop, MemoryNested.checked_compile_nested_raw.
  intros COMPILE VIEW WITHIN RUN MEMORY.
  destruct (MemoryNested.scratch_check pool (layout ++ live)) eqn:FRESH; try discriminate.
  eapply MemoryNested.compile_nested_correct with (backend := array_write_backend); eauto.
  apply MemoryNested.scratch_check_sound; exact FRESH.
Qed.
End BACKEND.

Print Assumptions array_write_backend.
Print Assumptions MemoryNested.compile_nested_correct.
Print Assumptions compile_memory_array_loop_correct.
