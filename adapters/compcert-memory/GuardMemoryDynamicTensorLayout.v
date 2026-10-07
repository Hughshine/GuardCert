From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST Values.
From polcert.src Require Import PolyBase.
From polcert.lib Require Import Linalg.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryBufferOffsets.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Dimensions are values at the guarded entry, not fixed affine coefficients.
    Logical cells retain their coordinate vectors. The physical map may have
    dynamic strides, including padding outside the accessed iteration domain. *)
Fixpoint tensor_volume (dimensions : list Z) : Z :=
  match dimensions with [] => 1 | dimension::rest => dimension*tensor_volume rest end.
Fixpoint tensor_index dimensions coordinates : option Z :=
  match dimensions,coordinates with
  | [],[] => Some 0
  | dimension::rest,coordinate::tail =>
      if (0 <=? coordinate) && (coordinate <? dimension) then
        match tensor_index rest tail with
        | Some offset => Some(coordinate*tensor_volume rest+offset)
        | None => None end
      else None
  | _,_ => None end.

Theorem tensor_index_bounds dimensions coordinates offset :
  tensor_index dimensions coordinates=Some offset ->
  0 <= offset < tensor_volume dimensions.
Proof.
  revert coordinates offset; induction dimensions as [|dimension rest IH];
    intros [|coordinate tail] offset INDEX; cbn in INDEX; try discriminate.
  - inversion INDEX; cbn; lia.
  - destruct((0 <=? coordinate)&&(coordinate <? dimension)) eqn:RANGE; [|discriminate].
    apply andb_true_iff in RANGE as [LOW HIGH]; apply Z.leb_le in LOW; apply Z.ltb_lt in HIGH.
    destruct(tensor_index rest tail) as [suffix|] eqn:SUFFIX; [|discriminate].
    inversion INDEX; subst offset; pose proof(IH _ _ SUFFIX); cbn [tensor_volume]; nia.
Qed.

Theorem tensor_index_positive_dimensions dimensions coordinates offset :
  tensor_index dimensions coordinates=Some offset -> Forall(fun dimension=>0<dimension)dimensions.
Proof.
  revert coordinates offset; induction dimensions as [|dimension rest IH];
    intros [|coordinate tail] offset INDEX; cbn in INDEX; try discriminate; [constructor|].
  destruct((0 <=? coordinate)&&(coordinate <? dimension)) eqn:RANGE; [|discriminate].
  apply andb_true_iff in RANGE as [LOW HIGH]; apply Z.leb_le in LOW; apply Z.ltb_lt in HIGH.
  destruct(tensor_index rest tail) as [suffix|] eqn:SUFFIX; [|discriminate].
  constructor; [lia|eapply IH; exact SUFFIX].
Qed.

Theorem tensor_index_injective dimensions first second offset :
  tensor_index dimensions first=Some offset -> tensor_index dimensions second=Some offset -> first=second.
Proof.
  revert first second offset; induction dimensions as [|dimension rest IH];
    intros [|a first] [|b second] offset FIRST SECOND; cbn in FIRST,SECOND; try discriminate; [reflexivity|].
  destruct((0 <=? a)&&(a <? dimension)); [|discriminate FIRST].
  destruct((0 <=? b)&&(b <? dimension)); [|discriminate SECOND].
  destruct(tensor_index rest first) as [x|] eqn:X; [|discriminate FIRST].
  destruct(tensor_index rest second) as [y|] eqn:Y; [|discriminate SECOND].
  pose proof(@tensor_index_bounds rest first x X) as RX;
  pose proof(@tensor_index_bounds rest second y Y) as RY.
  assert(HEAD:a=b) by (inversion FIRST; inversion SECOND; nia).
  subst b; assert(TAIL:x=y) by (inversion FIRST; inversion SECOND; lia); subst y.
  f_equal; eapply IH; eassumption.
Qed.

Definition tensor_volume_cap := Z.min Int.max_signed (Ptrofs.modulus/4).
Definition tensor_layout_flag dimensions :=
  forallb(fun dimension=>0 <? dimension)dimensions && (tensor_volume dimensions <=? tensor_volume_cap).

Theorem tensor_layout_flag_sound dimensions : tensor_layout_flag dimensions=true ->
  Forall(fun dimension=>0<dimension)dimensions /\
  tensor_volume dimensions<=Int.max_signed /\ 4*tensor_volume dimensions<=Ptrofs.modulus.
Proof.
  unfold tensor_layout_flag,tensor_volume_cap; rewrite andb_true_iff,Z.leb_le.
  intros [POSITIVE VOLUME]; split.
  - apply Forall_forall; intros dimension MEMBER; apply forallb_forall with(x:=dimension) in POSITIVE;
      [apply Z.ltb_lt; exact POSITIVE|exact MEMBER].
  - pose proof(Z.le_min_l Int.max_signed(Ptrofs.modulus/4)).
    pose proof(Z.le_min_r Int.max_signed(Ptrofs.modulus/4)).
    pose proof(Z.div_mod Ptrofs.modulus 4 ltac:(lia)).
    pose proof(Z.mod_pos_bound Ptrofs.modulus 4 ltac:(lia)); split; lia.
Qed.

Definition tensor_pointer_locations array block base dimensions (cell:MemCell) :=
  if Pos.eqb(arr_id cell)array then
    match tensor_index dimensions(arr_index cell) with
    | Some offset => Some(MemoryLocation Mint32 block(memory_pointer_buffer_offset base offset))
    | None => None end
  else None.

Theorem tensor_pointer_locations_nonalias array block base dimensions :
  4*tensor_volume dimensions<=Ptrofs.modulus ->
  locations_nonalias(tensor_pointer_locations array block base dimensions).
Proof.
  intros SPAN [first_id first] [second_id second] first_location second_location FIRST SECOND DIFFERENT.
  unfold tensor_pointer_locations in FIRST,SECOND; cbn [arr_id arr_index] in FIRST,SECOND.
  destruct(Pos.eqb first_id array) eqn:ID; [|discriminate FIRST].
  destruct(Pos.eqb second_id array) eqn:OTHER; [|discriminate SECOND].
  apply Pos.eqb_eq in ID,OTHER; subst first_id second_id.
  destruct(tensor_index dimensions first) as [x|] eqn:X; [|discriminate FIRST].
  destruct(tensor_index dimensions second) as [y|] eqn:Y; [|discriminate SECOND].
  inversion FIRST; inversion SECOND; subst first_location second_location.
  assert(DISTINCT:x<>y).
  { intro SAME; subst y;
    pose proof(@tensor_index_injective dimensions first second x X Y) as SAME; subst second.
    unfold cell_neq in DIFFERENT; cbn in DIFFERENT; destruct DIFFERENT as [BAD|BAD];
      [congruence|apply BAD,veq_refl]. }
  right; change(memory_pointer_buffer_offset base x+4<=memory_pointer_buffer_offset base y \/
    memory_pointer_buffer_offset base y+4<=memory_pointer_buffer_offset base x).
  apply memory_buffer_cell_separation with(extent:=tensor_volume dimensions).
  - pose proof Ptrofs.modulus_pos; lia.
  - apply memory_pointer_modulus_cells.
  - exact SPAN.
  - eapply tensor_index_bounds; exact X.
  - eapply tensor_index_bounds; exact Y.
  - exact DISTINCT.
Qed.

Print Assumptions tensor_index_bounds.
Print Assumptions tensor_index_positive_dimensions.
Print Assumptions tensor_index_injective.
Print Assumptions tensor_layout_flag_sound.
Print Assumptions tensor_pointer_locations_nonalias.
