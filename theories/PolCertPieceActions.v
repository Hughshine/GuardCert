From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg ImpureAlarmConfig.
From polcert.src Require Import PointWitness.
From polcert.polygen Require Import PolIRs.
From Vpl Require Import Impure.
From Guard Require Import PolCertPieceAffineMaps PolCertPieceCoordinates PolCertPieceFamily.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** Domain-restricted typed actions and parameter prefixes. These checks are
    additional to the coordinate/family checks; they do not check final order. *)
Module PolCertPieceActionsFor (IRs : POLIRS).
Module F := PolCertPieceFamilyFor IRs.
Module C := F.D.C.
Module PL := IRs.PolyLang.
Definition piece_identity_shape (pi : PL.PolyInstr) :=
  match PL.pi_point_witness pi with
  | PSWIdentity depth=>Nat.eqb depth (PL.pi_depth pi)
  | _=>false end.
Lemma piece_identity_shape_sound pi : piece_identity_shape pi=true ->
  PL.pi_point_witness pi=PSWIdentity (PL.pi_depth pi).
Proof.
  unfold piece_identity_shape; destruct (PL.pi_point_witness pi); try discriminate.
  intro SHAPE; apply Nat.eqb_eq in SHAPE; subst; reflexivity.
Qed.
Definition check_piece_actions parameter_count (source candidate : PL.PolyInstr) piece :=
  let candidate_width := length (piece_project piece) in
  if piece_identity_shape source && piece_identity_shape candidate &&
    IRs.Instr.eqb (PL.pi_instr source) (PL.pi_instr candidate) &&
    Nat.eqb candidate_width (parameter_count+PL.pi_depth candidate) &&
    Nat.eqb (length (piece_embed piece)) (parameter_count+PL.pi_depth source) &&
    piece_map_width candidate_width (piece_embed piece)
  then
    BIND prefix <- C.memory_check_domain_inclusion (piece_domain piece)
      (piece_equal_maps (firstn parameter_count (piece_embed piece))
        (firstn parameter_count (piece_identity candidate_width))) -;
    if prefix then C.memory_check_domain_inclusion (piece_domain piece)
      (piece_equal_maps (PL.pi_transformation candidate)
        (matrix_product (PL.pi_transformation source) (piece_embed piece)))
    else pure false
  else pure false.

Record piece_action_certificate parameter_count source candidate piece := PieceActionCertificate {
  action_source_identity : PL.pi_point_witness source=PSWIdentity (PL.pi_depth source);
  action_candidate_identity : PL.pi_point_witness candidate=PSWIdentity (PL.pi_depth candidate);
  action_same_instruction : PL.pi_instr source=PL.pi_instr candidate;
  action_candidate_dimension : length (piece_project piece)=(parameter_count+PL.pi_depth candidate)%nat;
  action_source_dimension : length (piece_embed piece)=(parameter_count+PL.pi_depth source)%nat;
  action_embed_width : exact_listzzs_cols (length (piece_project piece)) (piece_embed piece);
  action_parameter_prefix : forall index, length index=length (piece_project piece) ->
    in_poly index (piece_domain piece)=true ->
    firstn parameter_count (affine_product (piece_embed piece) index)=firstn parameter_count index;
  action_arguments : forall index, in_poly index (piece_domain piece)=true ->
    affine_product (PL.pi_transformation candidate) index =
    affine_product (PL.pi_transformation source) (affine_product (piece_embed piece) index)
}.
Theorem check_piece_actions_sound parameter_count source candidate piece :
  mayReturn (check_piece_actions parameter_count source candidate piece) true ->
  piece_action_certificate parameter_count source candidate piece.
Proof.
  unfold check_piece_actions.
  destruct (piece_identity_shape source && piece_identity_shape candidate &&
    IRs.Instr.eqb (PL.pi_instr source) (PL.pi_instr candidate) &&
    Nat.eqb (length (piece_project piece)) (parameter_count+PL.pi_depth candidate) &&
    Nat.eqb (length (piece_embed piece)) (parameter_count+PL.pi_depth source) &&
    piece_map_width (length (piece_project piece)) (piece_embed piece)) eqn:SHAPE;
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  repeat rewrite andb_true_iff in SHAPE.
  destruct SHAPE as [[[[[SOURCE CANDIDATE] INSTRUCTION] CANDIDATE_DIM] SOURCE_DIM] WIDTH].
  apply piece_identity_shape_sound in SOURCE,CANDIDATE.
  apply IRs.Instr.eqb_eq in INSTRUCTION; apply Nat.eqb_eq in CANDIDATE_DIM,SOURCE_DIM.
  apply piece_map_width_sound in WIDTH.
  intro CHECK; bind_imp_destruct CHECK prefix PREFIX; destruct prefix;
    [|apply mayReturn_pure in CHECK; discriminate].
  constructor; try assumption.
  - intros index LENGTH DOMAIN.
    pose proof (@C.memory_check_domain_inclusion_correct (piece_domain piece)
      (piece_equal_maps (firstn parameter_count (piece_embed piece))
        (firstn parameter_count (piece_identity (length (piece_project piece))))) PREFIX index DOMAIN) as EQUAL.
    apply piece_equal_maps_correct in EQUAL.
    unfold affine_product in EQUAL; rewrite <- !firstn_map in EQUAL.
    change (firstn parameter_count (affine_product (piece_embed piece) index)=
      firstn parameter_count (affine_product (piece_identity (length (piece_project piece))) index)) in EQUAL.
    rewrite piece_identity_correct in EQUAL by exact LENGTH; exact EQUAL.
  - intros index DOMAIN.
    pose proof (@C.memory_check_domain_inclusion_correct (piece_domain piece)
      (piece_equal_maps (PL.pi_transformation candidate)
        (matrix_product (PL.pi_transformation source) (piece_embed piece))) CHECK index DOMAIN) as EQUAL.
    apply piece_equal_maps_correct in EQUAL.
    rewrite (@matrix_product_assoc (PL.pi_transformation source) (piece_embed piece) index
      (length (piece_project piece)) WIDTH) in EQUAL; exact EQUAL.
Qed.

Definition piece_retimed_instruction (source candidate : PL.PolyInstr) piece : PL.PolyInstr :=
  {| PL.pi_depth:=PL.pi_depth candidate; PL.pi_instr:=PL.pi_instr candidate;
     PL.pi_poly:=PL.pi_poly candidate;
     PL.pi_schedule:=matrix_product (PL.pi_schedule source) (piece_embed piece);
     PL.pi_point_witness:=PL.pi_point_witness candidate;
     PL.pi_transformation:=PL.pi_transformation candidate;
     PL.pi_access_transformation:=PL.pi_access_transformation candidate;
     PL.pi_waccess:=PL.pi_waccess candidate; PL.pi_raccess:=PL.pi_raccess candidate |}.
Lemma piece_retimed_timestamp parameter_count source candidate piece index
  (certificate : piece_action_certificate parameter_count source candidate piece) :
  affine_product (PL.pi_schedule (piece_retimed_instruction source candidate piece)) index =
  affine_product (PL.pi_schedule source) (affine_product (piece_embed piece) index).
Proof.
  cbn [piece_retimed_instruction PL.pi_schedule]; apply matrix_product_assoc with
    (k2:=length (piece_project piece)); exact (action_embed_width certificate).
Qed.
Definition piece_canonical_point ordinal (instruction : PL.PolyInstr) index : PL.InstrPoint :=
  {| PL.ILSema.ip_nth:=ordinal; PL.ILSema.ip_index:=index;
     PL.ILSema.ip_transformation:=PL.pi_transformation instruction;
     PL.ILSema.ip_time_stamp:=affine_product (PL.pi_schedule instruction) index;
     PL.ILSema.ip_instruction:=PL.pi_instr instruction; PL.ILSema.ip_depth:=PL.pi_depth instruction |}.
Lemma piece_canonical_belongs ordinal instruction index :
  PL.pi_point_witness instruction=PSWIdentity (PL.pi_depth instruction) ->
  in_poly index (PL.pi_poly instruction)=true ->
  PL.belongs_to (piece_canonical_point ordinal instruction index) instruction.
Proof.
  intros IDENTITY DOMAIN; unfold PL.belongs_to.
  cbn [piece_canonical_point PL.ILSema.ip_index PL.ILSema.ip_transformation
    PL.ILSema.ip_time_stamp PL.ILSema.ip_instruction PL.ILSema.ip_depth].
  rewrite C.memory_identity_current_transform by exact IDENTITY; repeat split; auto.
Qed.
Theorem piece_canonical_action_iff parameter_count source candidate piece source_id candidate_id index initial final
  (certificate : piece_action_certificate parameter_count source candidate piece) :
  in_poly index (piece_domain piece)=true ->
  (PL.instr_point_sema (piece_canonical_point source_id source (affine_product (piece_embed piece) index)) initial final <->
   PL.instr_point_sema (piece_canonical_point candidate_id candidate index) initial final).
Proof.
  intro DOMAIN; split; intro RUN; inversion RUN as [writes reads EXEC];
    apply PL.ILSema.ip_sema_intro with (wcs:=writes) (rcs:=reads);
    cbn [piece_canonical_point PL.ILSema.ip_instruction PL.ILSema.ip_transformation PL.ILSema.ip_index] in *.
  - rewrite <- (@action_same_instruction parameter_count source candidate piece certificate),
      (@action_arguments parameter_count source candidate piece certificate index DOMAIN); exact EXEC.
  - rewrite (@action_same_instruction parameter_count source candidate piece certificate),
      <- (@action_arguments parameter_count source candidate piece certificate index DOMAIN); exact EXEC.
Qed.
End PolCertPieceActionsFor.
