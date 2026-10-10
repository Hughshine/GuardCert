From Stdlib Require Import List Bool ZArith Lia.
From polcert.polygen Require Import PolIRs.
From Guard Require Import PolCertCandidateRepresentation.
Import ListNotations.
Set Implicit Arguments.

(** Concatenation concerns static instruction ordinals, not execution order.
    The isomorphisms retain timestamps and individual memory actions. *)
Module PolCertPointSequenceAppendFor (IRs : POLIRS).
Module C := PolCertCandidateRepresentationFor IRs.
Module PL := IRs.PolyLang.
Definition point_set_ordinal ordinal (point : PL.InstrPoint) : PL.InstrPoint :=
  {| PL.ILSema.ip_nth:=ordinal; PL.ILSema.ip_index:=PL.ILSema.ip_index point;
     PL.ILSema.ip_transformation:=PL.ILSema.ip_transformation point;
     PL.ILSema.ip_time_stamp:=PL.ILSema.ip_time_stamp point;
     PL.ILSema.ip_instruction:=PL.ILSema.ip_instruction point;
     PL.ILSema.ip_depth:=PL.ILSema.ip_depth point |}.
Definition point_shift offset point := point_set_ordinal (offset+PL.ILSema.ip_nth point) point.
Definition point_unshift offset point := point_set_ordinal (PL.ILSema.ip_nth point-offset) point.
Lemma point_ordinal_self point : point_set_ordinal (PL.ILSema.ip_nth point) point=point.
Proof. destruct point; reflexivity. Qed.
Lemma point_unshift_shift offset point : point_unshift offset (point_shift offset point)=point.
Proof.
  unfold point_unshift,point_shift.
  change (point_set_ordinal ((offset+PL.ILSema.ip_nth point)-offset) point=point).
  replace ((offset+PL.ILSema.ip_nth point)-offset)%nat with (PL.ILSema.ip_nth point) by lia.
  apply point_ordinal_self.
Qed.
Lemma point_shift_unshift offset point : (offset<=PL.ILSema.ip_nth point)%nat ->
  point_shift offset (point_unshift offset point)=point.
Proof.
  intro ORDER; unfold point_shift,point_unshift.
  change (point_set_ordinal (offset+(PL.ILSema.ip_nth point-offset)) point=point).
  replace (offset+(PL.ILSema.ip_nth point-offset))%nat with (PL.ILSema.ip_nth point) by lia.
  apply point_ordinal_self.
Qed.
Lemma point_ordinal_execution ordinal point initial final :
  PL.instr_point_sema (point_set_ordinal ordinal point) initial final <-> PL.instr_point_sema point initial final.
Proof.
  split; intro RUN; inversion RUN as [writes reads EXEC];
    apply PL.ILSema.ip_sema_intro with (wcs:=writes) (rcs:=reads); exact EXEC.
Qed.
Lemma point_ordinal_belongs ordinal point instruction :
  PL.belongs_to (point_set_ordinal ordinal point) instruction <-> PL.belongs_to point instruction.
Proof. unfold PL.belongs_to; reflexivity. Qed.
Lemma valid_ordinal_bound parameters instructions point :
  C.memory_sequence_valid_point parameters instructions point ->
  (PL.ILSema.ip_nth point<length instructions)%nat.
Proof.
  intros [instruction [NTH _]]; apply nth_error_Some; rewrite NTH; discriminate.
Qed.
Lemma valid_append_left parameters left right point :
  (PL.ILSema.ip_nth point<length left)%nat ->
  (C.memory_sequence_valid_point parameters (left++right) point <->
   C.memory_sequence_valid_point parameters left point).
Proof. intro ORDER; unfold C.memory_sequence_valid_point; rewrite nth_error_app1 by exact ORDER; reflexivity. Qed.
Lemma valid_append_right parameters left right point :
  (length left<=PL.ILSema.ip_nth point)%nat ->
  (C.memory_sequence_valid_point parameters (left++right) point <->
   C.memory_sequence_valid_point parameters right (point_unshift (length left) point)).
Proof.
  intro ORDER; unfold C.memory_sequence_valid_point; rewrite nth_error_app2 by exact ORDER.
  unfold point_unshift; cbn [point_set_ordinal PL.ILSema.ip_nth PL.ILSema.ip_index].
  unfold PL.belongs_to; reflexivity.
Qed.
Lemma valid_append_shift parameters left right point :
  C.memory_sequence_valid_point parameters right point ->
  C.memory_sequence_valid_point parameters (left++right) (point_shift (length left) point).
Proof.
  intro VALID; apply valid_append_right; [unfold point_shift; cbn; lia|].
  rewrite point_unshift_shift; exact VALID.
Qed.
Definition append_point_map left_width right_width left_map right_map point :=
  if Nat.ltb (PL.ILSema.ip_nth point) left_width then left_map point
  else point_shift right_width (right_map (point_unshift left_width point)).
Lemma append_map_left source_width target_width left_map right_map point :
  (PL.ILSema.ip_nth point<source_width)%nat ->
  append_point_map source_width target_width left_map right_map point=left_map point.
Proof. intro ORDER; unfold append_point_map; rewrite (proj2 (Nat.ltb_lt _ _) ORDER); reflexivity. Qed.
Lemma append_map_right source_width target_width left_map right_map point :
  (source_width<=PL.ILSema.ip_nth point)%nat ->
  append_point_map source_width target_width left_map right_map point=
    point_shift target_width (right_map (point_unshift source_width point)).
Proof. intro ORDER; unfold append_point_map; rewrite (proj2 (Nat.ltb_ge _ _) ORDER); reflexivity. Qed.
Lemma append_map_valid parameters source_left source_right target_left target_right
  (left_iso : C.memory_point_isomorphism parameters source_left target_left)
  (right_iso : C.memory_point_isomorphism parameters source_right target_right) point :
  C.memory_sequence_valid_point parameters (source_left++source_right) point ->
  C.memory_sequence_valid_point parameters (target_left++target_right)
    (append_point_map (length source_left) (length target_left)
      (C.point_forward left_iso) (C.point_forward right_iso) point).
Proof.
  intro VALID; destruct (Nat.lt_ge_cases (PL.ILSema.ip_nth point) (length source_left)) as [LEFT|RIGHT].
  - rewrite (@append_map_left (length source_left) (length target_left)
      (C.point_forward left_iso) (C.point_forward right_iso) point LEFT).
    pose proof (proj1 (@valid_append_left parameters source_left source_right point LEFT) VALID) as OLD.
    pose proof (@C.point_forward_valid parameters source_left target_left left_iso point OLD) as NEW.
    apply valid_append_left; [exact (@valid_ordinal_bound parameters target_left _ NEW)|exact NEW].
  - rewrite append_map_right by exact RIGHT; apply valid_append_shift.
    apply C.point_forward_valid; apply valid_append_right in VALID; assumption.
Qed.
Lemma append_map_inverse parameters source_left source_right target_left target_right
  (left_iso : C.memory_point_isomorphism parameters source_left target_left)
  (right_iso : C.memory_point_isomorphism parameters source_right target_right) point :
  C.memory_sequence_valid_point parameters (source_left++source_right) point ->
  append_point_map (length target_left) (length source_left) (C.point_backward left_iso) (C.point_backward right_iso)
    (append_point_map (length source_left) (length target_left) (C.point_forward left_iso) (C.point_forward right_iso) point)=point.
Proof.
  intro VALID; destruct (Nat.lt_ge_cases (PL.ILSema.ip_nth point) (length source_left)) as [LEFT|RIGHT].
  - rewrite (@append_map_left (length source_left) (length target_left)
      (C.point_forward left_iso) (C.point_forward right_iso) point LEFT).
    assert (OLD : C.memory_sequence_valid_point parameters source_left point).
    { apply valid_append_left in VALID; assumption. }
    rewrite append_map_left by (apply (@valid_ordinal_bound parameters target_left); apply C.point_forward_valid; exact OLD).
    apply C.point_forward_inverse; exact OLD.
  - rewrite (@append_map_right (length source_left) (length target_left)
      (C.point_forward left_iso) (C.point_forward right_iso) point RIGHT).
    rewrite append_map_right by (unfold point_shift; cbn; lia).
    rewrite point_unshift_shift,C.point_forward_inverse.
    + apply point_shift_unshift; exact RIGHT.
    + apply valid_append_right in VALID; assumption.
Qed.
Lemma append_map_time parameters source_left source_right target_left target_right
  (left_iso : C.memory_point_isomorphism parameters source_left target_left)
  (right_iso : C.memory_point_isomorphism parameters source_right target_right) point :
  C.memory_sequence_valid_point parameters (source_left++source_right) point ->
  PL.ILSema.ip_time_stamp (append_point_map (length source_left) (length target_left)
    (C.point_forward left_iso) (C.point_forward right_iso) point)=PL.ILSema.ip_time_stamp point.
Proof.
  intro VALID; destruct (Nat.lt_ge_cases (PL.ILSema.ip_nth point) (length source_left)) as [LEFT|RIGHT].
  - rewrite append_map_left by exact LEFT; apply C.point_forward_time; apply valid_append_left in VALID; assumption.
  - rewrite append_map_right by exact RIGHT; unfold point_shift; cbn.
    rewrite C.point_forward_time; [reflexivity|apply valid_append_right in VALID; assumption].
Qed.
Lemma append_map_execution parameters source_left source_right target_left target_right
  (left_iso : C.memory_point_isomorphism parameters source_left target_left)
  (right_iso : C.memory_point_isomorphism parameters source_right target_right) point initial final :
  C.memory_sequence_valid_point parameters (source_left++source_right) point ->
  PL.instr_point_sema point initial final ->
  PL.instr_point_sema (append_point_map (length source_left) (length target_left)
    (C.point_forward left_iso) (C.point_forward right_iso) point) initial final.
Proof.
  intros VALID RUN; destruct (Nat.lt_ge_cases (PL.ILSema.ip_nth point) (length source_left)) as [LEFT|RIGHT].
  - rewrite append_map_left by exact LEFT; apply C.point_forward_execution; [apply valid_append_left in VALID; assumption|exact RUN].
  - rewrite append_map_right by exact RIGHT.
    unfold point_shift; apply point_ordinal_execution.
    apply C.point_forward_execution; [apply valid_append_right in VALID; assumption|].
    unfold point_unshift; apply point_ordinal_execution; exact RUN.
Qed.
Definition append_isomorphism parameters source_left source_right target_left target_right
  (left_iso : C.memory_point_isomorphism parameters source_left target_left)
  (right_iso : C.memory_point_isomorphism parameters source_right target_right) :
  C.memory_point_isomorphism parameters (source_left++source_right) (target_left++target_right).
Proof.
  refine {| C.point_forward:=append_point_map (length source_left) (length target_left)
      (C.point_forward left_iso) (C.point_forward right_iso);
    C.point_backward:=append_point_map (length target_left) (length source_left)
      (C.point_backward left_iso) (C.point_backward right_iso) |}.
  - exact (@append_map_valid parameters source_left source_right target_left target_right left_iso right_iso).
  - exact (@append_map_valid parameters target_left target_right source_left source_right
      (C.memory_point_isomorphism_reverse left_iso) (C.memory_point_isomorphism_reverse right_iso)).
  - exact (@append_map_inverse parameters source_left source_right target_left target_right left_iso right_iso).
  - exact (@append_map_inverse parameters target_left target_right source_left source_right
      (C.memory_point_isomorphism_reverse left_iso) (C.memory_point_isomorphism_reverse right_iso)).
  - exact (@append_map_time parameters source_left source_right target_left target_right left_iso right_iso).
  - exact (@append_map_time parameters target_left target_right source_left source_right
      (C.memory_point_isomorphism_reverse left_iso) (C.memory_point_isomorphism_reverse right_iso)).
  - exact (@append_map_execution parameters source_left source_right target_left target_right left_iso right_iso).
  - exact (@append_map_execution parameters target_left target_right source_left source_right
      (C.memory_point_isomorphism_reverse left_iso) (C.memory_point_isomorphism_reverse right_iso)).
Defined.
End PolCertPointSequenceAppendFor.
