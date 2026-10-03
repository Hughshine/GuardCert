From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightPureExpr ClightRectangularStore CompCertMemoryActions RectangularMemorySchedule.
Import ListNotations.
From Guard Require Import ClightRectangularUpdate.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_cross_update d write_array read_array iterator inner :=
  Sassign (rect_lvalue d write_array iterator inner)
    (Ebinop Oadd (rect_lvalue d read_array iterator inner) (rect_value d iterator inner) type_int32s).
Definition memory_cross_action d write_block read_block i j :=
  MemoryAction [MemoryLocation Mint32 read_block (4*(i*rectangle_stride d+j))]
    (MemoryLocation Mint32 write_block (4*(i*rectangle_stride d+j))) (rect_update_compute d i j).
Section UPDATE.
Variable d : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid d.
Lemma memory_cross_update_evaluation fe ge locals le memory write_array read_array iterator inner write_block read_block i j memory' :
  rect_array_binding d ge locals write_array write_block ->
  rect_array_binding d ge locals read_array read_block ->
  le ! iterator = Some (Vint (Int.repr i)) -> le ! inner = Some (Vint (Int.repr j)) ->
  0 <= i * rectangle_stride d + j < rectangle_extent d ->
  memory_action_run (memory_cross_action d write_block read_block i j) memory memory' ->
  exec_stmt fe ge locals le memory (memory_cross_update d write_array read_array iterator inner) E0 le memory' Out_normal.
Proof.
  intros WRITE_ARRAY READ_ARRAY I J INDEX [inputs [value [LOAD [COMPUTE STORE]]]].
  unfold memory_cross_action in LOAD, COMPUTE, STORE; cbn in LOAD, COMPUTE, STORE.
  unfold location_load, rectangle_location in LOAD; cbn in LOAD.
  unfold rect_update_compute in COMPUTE.
  change (match Mem.load Mint32 memory read_block (4 * (i * rectangle_stride d + j)) with
    | Some old => Some [old] | None => None end = Some inputs) in LOAD.
  destruct (Mem.load Mint32 memory read_block (4 * (i * rectangle_stride d + j))) as [old|] eqn:LOADED;
    try discriminate LOAD.
  inversion LOAD; subst inputs; destruct old; try discriminate COMPUTE.
  inversion COMPUTE; subst value.
  eapply exec_Sassign with (loc := write_block) (ofs := Ptrofs.repr (4 * (i * rectangle_stride d + j)))
    (bf := Full) (v := Vint (Int.add i0 (Int.repr (i * rectangle_coefficient d + j + rectangle_bias d))))
    (v2 := Vint (Int.add i0 (Int.repr (i * rectangle_coefficient d + j + rectangle_bias d)))).
  - apply (@rect_lvalue_evaluation d VALID); eauto.
  - eapply eval_Ebinop with (v1 := Vint i0)
      (v2 := Vint (Int.repr (i * rectangle_coefficient d + j + rectangle_bias d)));
      [eapply rect_load_evaluation; eauto|apply rect_value_evaluation; eauto|reflexivity].
  - reflexivity.
  - apply assign_loc_value with (chunk := Mint32); [reflexivity|].
    cbn [Mem.storev]; rewrite Ptrofs.unsigned_repr by
      (apply (@rect_small_offset_bound d VALID); unfold rectangle_layout_valid in VALID; lia).
    destruct (zle (4 * (i * rectangle_stride d + j) + size_chunk Mint32) Ptrofs.modulus); [exact STORE|].
    exfalso; pose proof (@rect_small_offset_bound d VALID (4 * (i * rectangle_stride d + j) + 4) ltac:(lia)) as END.
    unfold Ptrofs.max_unsigned in END; change (size_chunk Mint32) with 4 in *; lia.
Qed.
Lemma memory_cross_update_inverse fe ge locals le memory write_array read_array iterator inner i j trace le' memory' outcome :
  le ! iterator = Some (Vint (Int.repr i)) -> le ! inner = Some (Vint (Int.repr j)) ->
  0 <= i * rectangle_stride d + j < rectangle_extent d ->
  exec_stmt fe ge locals le memory (memory_cross_update d write_array read_array iterator inner) trace le' memory' outcome ->
  exists write_block read_block, rect_array_binding d ge locals write_array write_block /\
    rect_array_binding d ge locals read_array read_block /\ trace = E0 /\ le' = le /\ outcome = Out_normal /\
    memory_action_run (memory_cross_action d write_block read_block i j) memory memory'.
Proof.
  intros I J INDEX RUN; inversion RUN; subst.
  match goal with LVALUE : eval_lvalue _ _ ?current _ (rect_lvalue _ _ _ _) _ _ _ |- _ =>
    destruct (@rect_lvalue_inverse d VALID ge locals current memory write_array iterator inner i j _ _ _
      I J INDEX LVALUE) as [ARRAY [OFFSET FIELD]]; subst
  end.
  match goal with VALUE : eval_expr _ _ _ _ (Ebinop Oadd _ _ _) _ |- _ => inversion VALUE; subst end;
    try match goal with BAD : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion BAD end.
  match goal with PAYLOAD : eval_expr _ _ ?current _ (rect_value _ _ _) ?value |- _ =>
    pose proof (@pure_scalar_determinate _ (rect_value_pure d iterator inner) ge locals current memory
      value (Vint (Int.repr (i * rectangle_coefficient d + j + rectangle_bias d))) PAYLOAD
      (@rect_value_evaluation d ge locals current memory iterator inner i j I J)) as SAME; subst value
  end.
  match goal with READ : eval_expr _ _ ?current _ (rect_lvalue _ _ _ _) ?value |- _ =>
    destruct (@rect_load_inverse d VALID ge locals current memory read_array iterator inner i j value I J INDEX READ)
      as [read_block [READ_BIND LOAD]]
  end.
  match goal with ADD : sem_binary_operation _ _ ?old _ _ _ _ = Some _ |- _ =>
    destruct old; try discriminate ADD; inversion ADD; subst
  end.
  match goal with CAST : sem_cast _ _ _ _ = Some _ |- _ => inversion CAST; subst end.
  match goal with ASSIGN : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion ASSIGN; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  match goal with STORE : Mem.storev _ _ _ _ = Some _ |- _ =>
    cbn [Mem.storev] in STORE; rewrite Ptrofs.unsigned_repr in STORE by
      (apply (@rect_small_offset_bound d VALID); lia);
    destruct (zle (4 * (i * rectangle_stride d + j) + size_chunk Mint32) Ptrofs.modulus); try discriminate STORE
  end.
  exists loc,read_block; repeat split; auto.
  unfold memory_action_run; exists [Vint i0]; eexists; split.
  - change (match Mem.load Mint32 memory read_block (4 * (i * rectangle_stride d + j)) with
      | Some value => Some [value] | None => None end = Some [Vint i0]).
    rewrite LOAD; reflexivity.
  - split; [reflexivity|eassumption].
Qed.
End UPDATE.
Print Assumptions memory_cross_update_evaluation.
Print Assumptions memory_cross_update_inverse.
