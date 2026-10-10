From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PointWitness PolyBase.
From GuardMemory Require Import GuardMemoryDoublePolyhedral GuardMemoryDoubleCandidateProgress
  GuardMemoryAffinePointShift.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Module SP := DoubleAssignmentIRs.PolyLang.

Lemma double_shift_map_identity {A : Type} (f : A -> A) values :
  (forall value, f value = value) -> map f values = values.
Proof. intro SAME; induction values; cbn; [reflexivity|rewrite SAME,IHvalues; reflexivity]. Qed.

(** Per-statement constant shifts are representation witnesses. They retain
    actual IEEE instructions, execution, parameters and timestamps. Different
    statements may use different source-coordinate origins. *)
Definition double_shift_instruction position delta (pi : SP.PolyInstr) : SP.PolyInstr :=
  {| SP.pi_depth := SP.pi_depth pi; SP.pi_instr := SP.pi_instr pi;
     SP.pi_poly := map (affine_point_shift_constraint position delta) (SP.pi_poly pi);
     SP.pi_schedule := map (affine_point_shift_row position delta) (SP.pi_schedule pi);
     SP.pi_point_witness := SP.pi_point_witness pi;
     SP.pi_transformation := map (affine_point_shift_row position delta) (SP.pi_transformation pi);
     SP.pi_access_transformation := map (affine_point_shift_row position delta) (SP.pi_access_transformation pi);
     SP.pi_waccess := SP.pi_waccess pi; SP.pi_raccess := SP.pi_raccess pi |}.
Fixpoint double_shift_instructions_from position (deltas : nat -> Z) site instructions :=
  match instructions with
  | [] => []
  | pi::rest => double_shift_instruction position (deltas site) pi ::
      double_shift_instructions_from position deltas (S site) rest
  end.
Definition double_shift_instructions position deltas instructions :=
  double_shift_instructions_from position deltas 0 instructions.
Definition double_shift_point position deltas (point : SP.InstrPoint) : SP.InstrPoint :=
  let delta := deltas (SP.ILSema.ip_nth point) in
  {| SP.ILSema.ip_nth := SP.ILSema.ip_nth point;
     SP.ILSema.ip_index := affine_point_shift position delta (SP.ILSema.ip_index point);
     SP.ILSema.ip_transformation := map (affine_point_shift_row position delta) (SP.ILSema.ip_transformation point);
     SP.ILSema.ip_time_stamp := SP.ILSema.ip_time_stamp point;
     SP.ILSema.ip_instruction := SP.ILSema.ip_instruction point;
     SP.ILSema.ip_depth := SP.ILSema.ip_depth point |}.

Lemma double_shift_instruction_inverse position delta pi :
  double_shift_instruction position (-delta) (double_shift_instruction position delta pi) = pi.
Proof.
  destruct pi; unfold double_shift_instruction; cbn; f_equal;
    rewrite map_map; apply double_shift_map_identity; intro row;
    apply affine_point_shift_constraint_inverse || apply affine_point_shift_row_inverse.
Qed.
Lemma double_shift_instructions_inverse position deltas instructions :
  double_shift_instructions position (fun site => -deltas site)
    (double_shift_instructions position deltas instructions) = instructions.
Proof.
  unfold double_shift_instructions; generalize 0%nat; induction instructions; intro site;
    cbn; [reflexivity|rewrite double_shift_instruction_inverse,IHinstructions; reflexivity].
Qed.
Lemma double_shift_instructions_nth position deltas instructions : forall site index,
  nth_error (double_shift_instructions_from position deltas site instructions) index =
  match nth_error instructions index with
  | Some pi => Some (double_shift_instruction position (deltas (site+index)%nat) pi)
  | None => None end.
Proof.
  induction instructions; intros site [|index]; cbn; try reflexivity.
  - rewrite Nat.add_0_r; reflexivity.
  - rewrite IHinstructions, Nat.add_succ_r; reflexivity.
Qed.
Lemma double_shift_point_inverse position deltas point :
  double_shift_point position (fun site => -deltas site) (double_shift_point position deltas point) = point.
Proof.
  destruct point; unfold double_shift_point; cbn; f_equal.
  - apply affine_point_shift_inverse.
  - rewrite map_map; apply double_shift_map_identity; intro row; apply affine_point_shift_row_inverse.
Qed.
Lemma double_shift_instruction_representation position delta dimension pi :
  DoubleCandidate.memory_identity_representation dimension pi ->
  DoubleCandidate.memory_identity_representation dimension (double_shift_instruction position delta pi).
Proof.
  intros [IDENTITY [DOMAIN [SCHEDULE TRANSFORM]]]; split; [exact IDENTITY|].
  repeat split; apply Forall_map; eapply Forall_impl;
    [|exact DOMAIN| |exact SCHEDULE| |exact TRANSFORM]; intros row WIDTH; exact WIDTH.
Qed.
Lemma double_shift_instructions_representation position deltas dimension instructions :
  Forall (DoubleCandidate.memory_identity_representation dimension) instructions ->
  Forall (DoubleCandidate.memory_identity_representation dimension)
    (double_shift_instructions position deltas instructions).
Proof.
  intro REPRESENTATIONS; unfold double_shift_instructions; generalize 0%nat;
    induction REPRESENTATIONS; intro site; cbn; constructor;
    [apply double_shift_instruction_representation; exact H|apply IHREPRESENTATIONS].
Qed.
Lemma double_shift_valid_point position deltas parameters instructions point :
  (length parameters <= position)%nat ->
  Forall (DoubleCandidate.memory_identity_representation (length parameters)) instructions ->
  DoubleCandidate.memory_sequence_valid_point parameters instructions point ->
  DoubleCandidate.memory_sequence_valid_point parameters
    (double_shift_instructions position deltas instructions) (double_shift_point position deltas point).
Proof.
  intros PREFIX REPRESENTATIONS [pi [NTH [PARAMS [BELONG LENGTH]]]].
  pose proof (proj1 (Forall_forall _ _) REPRESENTATIONS pi ltac:(eapply nth_error_In; exact NTH))
    as [IDENTITY [DOMAIN [SCHEDULE TRANSFORM]]].
  exists (double_shift_instruction position (deltas (SP.ILSema.ip_nth point)) pi); split.
  - unfold double_shift_instructions; rewrite double_shift_instructions_nth;
      cbn [double_shift_point SP.ILSema.ip_nth]; rewrite NTH; reflexivity.
  - split.
    + cbn [double_shift_point SP.ILSema.ip_index]; rewrite affine_point_shift_prefix by exact PREFIX; exact PARAMS.
    + split.
      * unfold SP.belongs_to in BELONG |- *.
        destruct BELONG as [DOMAIN_HOLDS [TF [TIME [INSTRUCTION DEPTH]]]].
        cbn [double_shift_point double_shift_instruction SP.ILSema.ip_index SP.ILSema.ip_transformation
          SP.ILSema.ip_time_stamp SP.ILSema.ip_instruction SP.ILSema.ip_depth SP.pi_poly SP.pi_schedule SP.pi_instr SP.pi_depth].
        split.
        -- rewrite affine_point_shift_domain; [exact DOMAIN_HOLDS|rewrite LENGTH; exact DOMAIN].
        -- split.
           ++ rewrite DoubleCandidate.memory_identity_current_transform in TF by exact IDENTITY.
              rewrite DoubleCandidate.memory_identity_current_transform by exact IDENTITY; rewrite TF; reflexivity.
           ++ split.
              ** rewrite affine_point_shift_product; [exact TIME|rewrite LENGTH; exact SCHEDULE].
              ** split; assumption.
      * cbn [double_shift_point double_shift_instruction SP.ILSema.ip_index SP.pi_depth];
          rewrite affine_point_shift_length; exact LENGTH.
Qed.
Lemma double_shift_point_execution position deltas point initial final :
  Forall (fun row => length (fst row) = length (SP.ILSema.ip_index point)) (SP.ILSema.ip_transformation point) ->
  SP.instr_point_sema point initial final -> SP.instr_point_sema (double_shift_point position deltas point) initial final.
Proof.
  intros WIDTH RUN; inversion RUN as [writes reads EXEC].
  apply SP.ILSema.ip_sema_intro with (wcs:=writes) (rcs:=reads).
  cbn [double_shift_point SP.ILSema.ip_instruction SP.ILSema.ip_transformation SP.ILSema.ip_index].
  rewrite affine_point_shift_product by exact WIDTH; exact EXEC.
Qed.
Definition double_point_shift_isomorphism position deltas parameters instructions
  (PREFIX : (length parameters <= position)%nat)
  (REPRESENTATIONS : Forall (DoubleCandidate.memory_identity_representation (length parameters)) instructions) :
  DoubleCandidate.memory_point_isomorphism parameters instructions (double_shift_instructions position deltas instructions).
Proof.
  pose proof (@double_shift_instructions_representation position deltas (length parameters) instructions REPRESENTATIONS) as TARGET_REP.
  refine {| DoubleCandidate.point_forward := double_shift_point position deltas;
            DoubleCandidate.point_backward := double_shift_point position (fun site => -deltas site) |}.
  - intros point VALID; apply double_shift_valid_point; assumption.
  - intros point VALID.
    pose proof (@double_shift_valid_point position (fun site => -deltas site) parameters _ point PREFIX TARGET_REP VALID) as SOURCE.
    rewrite double_shift_instructions_inverse in SOURCE; exact SOURCE.
  - intros; apply double_shift_point_inverse.
  - intros point VALID.
    replace deltas with (fun site => - -(deltas site)) at 1 by
      (apply FunctionalExtensionality.functional_extensionality; intro site; lia).
    apply double_shift_point_inverse.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros point initial final VALID RUN; apply double_shift_point_execution; [|exact RUN].
    exact (@DoubleCandidate.memory_valid_point_transform_width parameters instructions point REPRESENTATIONS VALID).
  - intros point initial final VALID RUN; apply double_shift_point_execution; [|exact RUN].
    exact (@DoubleCandidate.memory_valid_point_transform_width parameters _ point TARGET_REP VALID).
Defined.
Theorem double_point_shift_execution position deltas parameters instructions context vars initial final :
  length context = length parameters -> (length parameters <= position)%nat ->
  Forall (DoubleCandidate.memory_identity_representation (length parameters)) instructions ->
  (SP.poly_instance_list_semantics parameters (instructions,context,vars) initial final <->
   SP.poly_instance_list_semantics parameters (double_shift_instructions position deltas instructions,context,vars) initial final).
Proof.
  intros LENGTH PREFIX REPRESENTATIONS; eapply DoubleCandidate.memory_point_isomorphism_execution;
    [apply double_point_shift_isomorphism; assumption|exact LENGTH].
Qed.

Print Assumptions double_shift_instruction_inverse.
Print Assumptions double_shift_instructions_inverse.
Print Assumptions double_shift_valid_point.
Print Assumptions double_point_shift_execution.
