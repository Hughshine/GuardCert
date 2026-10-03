From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightPureExpr ClightRectangularStore ClightRectangularUpdate CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryCopyArray.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_layout_copy_action write_shape read_shape write_block read_block i j :=
  MemoryAction [MemoryLocation Mint32 read_block (4*(i*rectangle_stride read_shape+j))]
    (MemoryLocation Mint32 write_block (4*(i*rectangle_stride write_shape+j))) memory_copy_compute.
Definition memory_layout_copy_statement write_shape read_shape write_array read_array iterator inner :=
  Sassign (rect_lvalue write_shape write_array iterator inner) (rect_lvalue read_shape read_array iterator inner).
Section COPY.
Variable write_shape read_shape : rectangle_shape.
Hypothesis WVALID : rectangle_layout_valid write_shape.
Hypothesis RVALID : rectangle_layout_valid read_shape.
Lemma memory_layout_copy_statement_evaluation fe ge locals le memory write_array read_array iterator inner write_block read_block i j memory' :
  rect_array_binding write_shape ge locals write_array write_block ->
  rect_array_binding read_shape ge locals read_array read_block ->
  le ! iterator = Some (Vint (Int.repr i)) -> le ! inner = Some (Vint (Int.repr j)) ->
  0 <= i*rectangle_stride write_shape+j < rectangle_extent write_shape ->
  0 <= i*rectangle_stride read_shape+j < rectangle_extent read_shape ->
  memory_action_run (memory_layout_copy_action write_shape read_shape write_block read_block i j) memory memory' ->
  exec_stmt fe ge locals le memory (memory_layout_copy_statement write_shape read_shape write_array read_array iterator inner) E0 le memory' Out_normal.
Proof.
  intros WRITE_ARRAY READ_ARRAY I J WINDEX RINDEX [inputs [value [LOAD [COMPUTE STORE]]]].
  unfold memory_layout_copy_action in LOAD,COMPUTE,STORE; cbn in LOAD,COMPUTE,STORE.
  change (match Mem.load Mint32 memory read_block (4*(i*rectangle_stride read_shape+j)) with
    | Some old => Some [old] | None => None end = Some inputs) in LOAD.
  destruct (Mem.load Mint32 memory read_block (4*(i*rectangle_stride read_shape+j))) as [old|] eqn:LOADED;
    try discriminate LOAD.
  inversion LOAD; subst inputs; destruct old; try discriminate COMPUTE; inversion COMPUTE; subst value.
  eapply exec_Sassign with (loc := write_block) (ofs := Ptrofs.repr (4*(i*rectangle_stride write_shape+j)))
    (bf := Full) (v := Vint i0) (v2 := Vint i0).
  - apply (@rect_lvalue_evaluation write_shape WVALID); eauto.
  - eapply (@rect_load_evaluation read_shape RVALID); eauto.
  - reflexivity.
  - apply assign_loc_value with (chunk := Mint32); [reflexivity|].
    cbn [Mem.storev]; rewrite Ptrofs.unsigned_repr by
      (apply (@rect_small_offset_bound write_shape WVALID); lia).
    destruct (zle (4*(i*rectangle_stride write_shape+j)+size_chunk Mint32) Ptrofs.modulus); [exact STORE|].
    exfalso; pose proof (@rect_small_offset_bound write_shape WVALID (4*(i*rectangle_stride write_shape+j)+4) ltac:(lia)) as END.
    unfold Ptrofs.max_unsigned in END; change (size_chunk Mint32) with 4 in *; lia.
Qed.
Lemma memory_layout_copy_statement_inverse fe ge locals le memory write_array read_array iterator inner i j trace le' memory' outcome :
  le ! iterator = Some (Vint (Int.repr i)) -> le ! inner = Some (Vint (Int.repr j)) ->
  0 <= i*rectangle_stride write_shape+j < rectangle_extent write_shape ->
  0 <= i*rectangle_stride read_shape+j < rectangle_extent read_shape ->
  exec_stmt fe ge locals le memory (memory_layout_copy_statement write_shape read_shape write_array read_array iterator inner) trace le' memory' outcome ->
  exists write_block read_block, rect_array_binding write_shape ge locals write_array write_block /\
    rect_array_binding read_shape ge locals read_array read_block /\ trace = E0 /\ le' = le /\ outcome = Out_normal /\
    memory_action_run (memory_layout_copy_action write_shape read_shape write_block read_block i j) memory memory'.
Proof.
  intros I J WINDEX RINDEX RUN; inversion RUN; subst.
  match goal with LVALUE : eval_lvalue _ _ ?current _ (rect_lvalue write_shape _ _ _) _ _ _ |- _ =>
    destruct (@rect_lvalue_inverse write_shape WVALID ge locals current memory write_array iterator inner i j _ _ _
      I J WINDEX LVALUE) as [ARRAY [OFFSET FIELD]]; subst end.
  match goal with READ : eval_expr _ _ ?current _ (rect_lvalue read_shape _ _ _) ?value |- _ =>
    destruct (@rect_load_inverse read_shape RVALID ge locals current memory read_array iterator inner i j value I J RINDEX READ)
      as [read_block [READ_BIND LOAD]] end.
  match goal with CAST : sem_cast ?old _ _ _ = Some _ |- _ =>
    destruct old; try discriminate CAST; inversion CAST; subst end.
  match goal with ASSIGN : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion ASSIGN; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  match goal with STORE : Mem.storev _ _ _ _ = Some _ |- _ =>
    cbn [Mem.storev] in STORE; rewrite Ptrofs.unsigned_repr in STORE by
      (apply (@rect_small_offset_bound write_shape WVALID); lia);
    destruct (zle (4*(i*rectangle_stride write_shape+j)+size_chunk Mint32) Ptrofs.modulus); try discriminate STORE end.
  exists loc,read_block; repeat split; auto.
  unfold memory_action_run; exists [Vint i0]; exists (Vint i0); split.
  - change (match Mem.load Mint32 memory read_block (4*(i*rectangle_stride read_shape+j)) with
      | Some value => Some [value] | None => None end = Some [Vint i0]).
    rewrite LOAD; reflexivity.
  - split; [reflexivity|eassumption].
Qed.
End COPY.
Print Assumptions memory_layout_copy_statement_evaluation.
Print Assumptions memory_layout_copy_statement_inverse.
