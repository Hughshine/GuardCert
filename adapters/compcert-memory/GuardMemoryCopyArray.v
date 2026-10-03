From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightPureExpr ClightRectangularStore ClightRectangularUpdate CompCertMemoryActions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_copy_compute inputs :=
  match inputs with [Vint value] => Some (Vint value) | _ => None end.
Definition memory_copy_action d write_block read_block i j :=
  MemoryAction [MemoryLocation Mint32 read_block (4*(i*rectangle_stride d+j))]
    (MemoryLocation Mint32 write_block (4*(i*rectangle_stride d+j))) memory_copy_compute.
Definition memory_copy_statement d write_array read_array iterator inner :=
  Sassign (rect_lvalue d write_array iterator inner) (rect_lvalue d read_array iterator inner).
Section COPY.
Variable d : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid d.
Lemma memory_copy_statement_evaluation fe ge locals le memory write_array read_array iterator inner write_block read_block i j memory' :
  rect_array_binding d ge locals write_array write_block ->
  rect_array_binding d ge locals read_array read_block ->
  le ! iterator = Some (Vint (Int.repr i)) -> le ! inner = Some (Vint (Int.repr j)) ->
  0 <= i*rectangle_stride d+j < rectangle_extent d ->
  memory_action_run (memory_copy_action d write_block read_block i j) memory memory' ->
  exec_stmt fe ge locals le memory (memory_copy_statement d write_array read_array iterator inner) E0 le memory' Out_normal.
Proof.
  intros WRITE_ARRAY READ_ARRAY I J INDEX [inputs [value [LOAD [COMPUTE STORE]]]].
  unfold memory_copy_action in LOAD,COMPUTE,STORE; cbn in LOAD,COMPUTE,STORE.
  change (match Mem.load Mint32 memory read_block (4*(i*rectangle_stride d+j)) with
    | Some old => Some [old] | None => None end = Some inputs) in LOAD.
  destruct (Mem.load Mint32 memory read_block (4*(i*rectangle_stride d+j))) as [old|] eqn:LOADED;
    try discriminate LOAD.
  inversion LOAD; subst inputs; destruct old; try discriminate COMPUTE; inversion COMPUTE; subst value.
  eapply exec_Sassign with (loc := write_block) (ofs := Ptrofs.repr (4*(i*rectangle_stride d+j)))
    (bf := Full) (v := Vint i0) (v2 := Vint i0).
  - apply (@rect_lvalue_evaluation d VALID); eauto.
  - eapply rect_load_evaluation; eauto.
  - reflexivity.
  - apply assign_loc_value with (chunk := Mint32); [reflexivity|].
    cbn [Mem.storev]; rewrite Ptrofs.unsigned_repr by
      (apply (@rect_small_offset_bound d VALID); lia).
    destruct (zle (4*(i*rectangle_stride d+j)+size_chunk Mint32) Ptrofs.modulus); [exact STORE|].
    exfalso; pose proof (@rect_small_offset_bound d VALID (4*(i*rectangle_stride d+j)+4) ltac:(lia)) as END.
    unfold Ptrofs.max_unsigned in END; change (size_chunk Mint32) with 4 in *; lia.
Qed.
Lemma memory_copy_statement_inverse fe ge locals le memory write_array read_array iterator inner i j trace le' memory' outcome :
  le ! iterator = Some (Vint (Int.repr i)) -> le ! inner = Some (Vint (Int.repr j)) ->
  0 <= i*rectangle_stride d+j < rectangle_extent d ->
  exec_stmt fe ge locals le memory (memory_copy_statement d write_array read_array iterator inner) trace le' memory' outcome ->
  exists write_block read_block, rect_array_binding d ge locals write_array write_block /\
    rect_array_binding d ge locals read_array read_block /\ trace = E0 /\ le' = le /\ outcome = Out_normal /\
    memory_action_run (memory_copy_action d write_block read_block i j) memory memory'.
Proof.
  intros I J INDEX RUN; inversion RUN; subst.
  match goal with LVALUE : eval_lvalue _ _ ?current _ (rect_lvalue _ _ _ _) _ _ _ |- _ =>
    destruct (@rect_lvalue_inverse d VALID ge locals current memory write_array iterator inner i j _ _ _
      I J INDEX LVALUE) as [ARRAY [OFFSET FIELD]]; subst end.
  match goal with READ : eval_expr _ _ ?current _ (rect_lvalue _ _ _ _) ?value |- _ =>
    destruct (@rect_load_inverse d VALID ge locals current memory read_array iterator inner i j value I J INDEX READ)
      as [read_block [READ_BIND LOAD]] end.
  match goal with CAST : sem_cast ?old _ _ _ = Some _ |- _ =>
    destruct old; try discriminate CAST; inversion CAST; subst end.
  match goal with ASSIGN : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion ASSIGN; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  match goal with STORE : Mem.storev _ _ _ _ = Some _ |- _ =>
    cbn [Mem.storev] in STORE; rewrite Ptrofs.unsigned_repr in STORE by
      (apply (@rect_small_offset_bound d VALID); lia);
    destruct (zle (4*(i*rectangle_stride d+j)+size_chunk Mint32) Ptrofs.modulus); try discriminate STORE end.
  exists loc,read_block; repeat split; auto.
  unfold memory_action_run; exists [Vint i0]; exists (Vint i0); split.
  - change (match Mem.load Mint32 memory read_block (4*(i*rectangle_stride d+j)) with
      | Some value => Some [value] | None => None end = Some [Vint i0]).
    rewrite LOAD; reflexivity.
  - split; [reflexivity|eassumption].
Qed.
End COPY.
Print Assumptions memory_copy_statement_evaluation.
Print Assumptions memory_copy_statement_inverse.
