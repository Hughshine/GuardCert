From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PointWitness.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryPolyhedral GuardMemoryPolyhedralRectangles
  GuardMemorySequencePolyhedral GuardMemoryPointIsomorphism.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_swap_coordinates {A} position (values : list A) :=
  match position,values with
  | O,first::second::rest => second::first::rest
  | S index,first::rest => first::memory_swap_coordinates index rest
  | _,_ => values end.
Lemma memory_swap_coordinates_length {A} position (values : list A) :
  length (memory_swap_coordinates position values) = length values.
Proof. revert values; induction position; intros [|first [|second rest]]; cbn; auto. Qed.
Lemma memory_swap_coordinates_inverse {A} position (values : list A) :
  memory_swap_coordinates position (memory_swap_coordinates position values) = values.
Proof. revert values; induction position; intros [|first [|second rest]]; cbn; congruence. Qed.
Lemma memory_swap_coordinates_prefix {A} position count (values : list A) :
  (count <= position)%nat -> firstn count (memory_swap_coordinates position values) = firstn count values.
Proof.
  revert count values; induction position; intros count values ORDER;
    destruct count; cbn; [reflexivity|lia|reflexivity|].
  destruct values; cbn; [reflexivity|]; f_equal; apply IHposition; lia.
Qed.
Lemma memory_swap_dot_product position first second : length first = length second ->
  dot_product (memory_swap_coordinates position first) (memory_swap_coordinates position second) = dot_product first second.
Proof.
  revert first second; induction position; intros first second LENGTH.
  - destruct first as [|a [|b rest]],second as [|c [|d tail]]; cbn in LENGTH |- *; try lia; try reflexivity; ring.
  - destruct first,second; cbn in LENGTH |- *; try lia; try reflexivity.
    rewrite IHposition by lia; reflexivity.
Qed.
Definition memory_swap_affine position (row : list Z * Z) := (memory_swap_coordinates position (fst row),snd row).
Definition memory_swap_affines position := map (memory_swap_affine position).
Lemma memory_swap_affines_inverse position rows :
  memory_swap_affines position (memory_swap_affines position rows) = rows.
Proof.
  induction rows as [|[coefficients bias] rows IH]; [reflexivity|].
  change ((memory_swap_coordinates position (memory_swap_coordinates position coefficients),bias)::
    memory_swap_affines position (memory_swap_affines position rows) = (coefficients,bias)::rows).
  rewrite memory_swap_coordinates_inverse,IH; reflexivity.
Qed.
Lemma memory_swap_affine_product position rows index :
  Forall (fun row => length (fst row) = length index) rows ->
  affine_product (memory_swap_affines position rows) (memory_swap_coordinates position index) = affine_product rows index.
Proof.
  intro WIDTH; induction WIDTH; [reflexivity|].
  destruct x as [coefficients bias].
  change ((dot_product (memory_swap_coordinates position coefficients) (memory_swap_coordinates position index)+bias)::
    affine_product (memory_swap_affines position l) (memory_swap_coordinates position index) =
    (dot_product coefficients index+bias)::affine_product l index).
  rewrite memory_swap_dot_product by exact H; rewrite IHWIDTH; reflexivity.
Qed.
Lemma memory_swap_domain position rows index :
  Forall (fun row => length (fst row) = length index) rows ->
  in_poly (memory_swap_coordinates position index) (memory_swap_affines position rows) = in_poly index rows.
Proof.
  intro WIDTH; induction WIDTH; [reflexivity|].
  destruct x as [coefficients bias].
  change ((dot_product (memory_swap_coordinates position index) (memory_swap_coordinates position coefficients) <=? bias) &&
    in_poly (memory_swap_coordinates position index) (memory_swap_affines position l) =
    (dot_product index coefficients <=? bias) && in_poly index l).
  rewrite memory_swap_dot_product by (symmetry; exact H); rewrite IHWIDTH; reflexivity.
Qed.
Definition memory_swap_instruction position (pi : PL.PolyInstr) : PL.PolyInstr :=
  {| PL.pi_depth := PL.pi_depth pi; PL.pi_instr := PL.pi_instr pi;
     PL.pi_poly := memory_swap_affines position (PL.pi_poly pi);
     PL.pi_schedule := memory_swap_affines position (PL.pi_schedule pi);
     PL.pi_point_witness := PL.pi_point_witness pi;
     PL.pi_transformation := memory_swap_affines position (PL.pi_transformation pi);
     PL.pi_access_transformation := memory_swap_affines position (PL.pi_access_transformation pi);
     PL.pi_waccess := PL.pi_waccess pi; PL.pi_raccess := PL.pi_raccess pi |}.
Definition memory_swap_instructions position := map (memory_swap_instruction position).
Definition memory_swap_point position (point : PL.InstrPoint) : PL.InstrPoint :=
  {| PL.ILSema.ip_nth := PL.ILSema.ip_nth point;
     PL.ILSema.ip_index := memory_swap_coordinates position (PL.ILSema.ip_index point);
     PL.ILSema.ip_transformation := memory_swap_affines position (PL.ILSema.ip_transformation point);
     PL.ILSema.ip_time_stamp := PL.ILSema.ip_time_stamp point;
     PL.ILSema.ip_instruction := PL.ILSema.ip_instruction point;
     PL.ILSema.ip_depth := PL.ILSema.ip_depth point |}.
Lemma memory_swap_instruction_inverse position pi :
  memory_swap_instruction position (memory_swap_instruction position pi) = pi.
Proof. destruct pi; unfold memory_swap_instruction; cbn; rewrite !memory_swap_affines_inverse; reflexivity. Qed.
Lemma memory_swap_instructions_inverse position instructions :
  memory_swap_instructions position (memory_swap_instructions position instructions) = instructions.
Proof. induction instructions; cbn [memory_swap_instructions map];
  [reflexivity|rewrite memory_swap_instruction_inverse,IHinstructions; reflexivity]. Qed.
Lemma memory_swap_point_inverse position point :
  memory_swap_point position (memory_swap_point position point) = point.
Proof. destruct point; unfold memory_swap_point; cbn; rewrite memory_swap_coordinates_inverse,memory_swap_affines_inverse; reflexivity. Qed.

Definition memory_identity_representation dimension pi :=
  PL.pi_point_witness pi = PSWIdentity (PL.pi_depth pi) /\
  Forall (fun row => length (fst row) = (dimension+PL.pi_depth pi)%nat) (PL.pi_poly pi) /\
  Forall (fun row => length (fst row) = (dimension+PL.pi_depth pi)%nat) (PL.pi_schedule pi) /\
  Forall (fun row => length (fst row) = (dimension+PL.pi_depth pi)%nat) (PL.pi_transformation pi).
Lemma memory_identity_current_transform pi index :
  PL.pi_point_witness pi = PSWIdentity (PL.pi_depth pi) ->
  PL.current_transformation_of pi index = PL.pi_transformation pi.
Proof. intro IDENTITY; unfold PL.current_transformation_of,PL.current_transformation_at;
  rewrite IDENTITY; reflexivity. Qed.

Lemma memory_swap_instruction_representation position dimension pi :
  memory_identity_representation dimension pi ->
  memory_identity_representation dimension (memory_swap_instruction position pi).
Proof.
  intros [IDENTITY [DOMAIN [SCHEDULE TRANSFORM]]]; split; [exact IDENTITY|].
  repeat split; unfold memory_swap_affines; apply Forall_map; eapply Forall_impl;
    [|exact DOMAIN| |exact SCHEDULE| |exact TRANSFORM];
    intros row WIDTH; cbn [memory_swap_affine fst]; rewrite memory_swap_coordinates_length; exact WIDTH.
Qed.

Lemma memory_swap_valid_point position parameters instructions point :
  (length parameters <= position)%nat ->
  Forall (memory_identity_representation (length parameters)) instructions ->
  memory_sequence_valid_point parameters instructions point ->
  memory_sequence_valid_point parameters (memory_swap_instructions position instructions) (memory_swap_point position point).
Proof.
  intros PREFIX REPRESENTATIONS [pi [NTH [PARAMS [BELONG LENGTH]]]].
  assert (REP := proj1 (Forall_forall _ _) REPRESENTATIONS pi ltac:(eapply nth_error_In; exact NTH)).
  destruct REP as [IDENTITY [DOMAIN [SCHEDULE TRANSFORM]]].
  exists (memory_swap_instruction position pi); split.
  - unfold memory_swap_instructions; rewrite nth_error_map; cbn [memory_swap_point PL.ILSema.ip_nth]; rewrite NTH; reflexivity.
  - split.
    + cbn [memory_swap_point PL.ILSema.ip_index]; rewrite memory_swap_coordinates_prefix by exact PREFIX; exact PARAMS.
    + split.
      * unfold PL.belongs_to in BELONG |- *.
        destruct BELONG as [IN [TF [TIME [INSTRUCTION DEPTH]]]].
        cbn [memory_swap_point memory_swap_instruction PL.ILSema.ip_index PL.ILSema.ip_transformation
          PL.ILSema.ip_time_stamp PL.ILSema.ip_instruction PL.ILSema.ip_depth PL.pi_poly PL.pi_schedule PL.pi_instr PL.pi_depth].
        split.
        -- rewrite memory_swap_domain; [exact IN|rewrite LENGTH; exact DOMAIN].
        -- split.
           ++ rewrite memory_identity_current_transform in TF by exact IDENTITY.
              rewrite memory_identity_current_transform by exact IDENTITY; rewrite TF; reflexivity.
           ++ split.
              ** rewrite memory_swap_affine_product; [exact TIME|rewrite LENGTH; exact SCHEDULE].
              ** split; assumption.
      * cbn [memory_swap_point memory_swap_instruction PL.ILSema.ip_index PL.pi_depth]; rewrite memory_swap_coordinates_length; exact LENGTH.
Qed.

Lemma memory_swap_point_execution position point initial final :
  Forall (fun row => length (fst row) = length (PL.ILSema.ip_index point)) (PL.ILSema.ip_transformation point) ->
  PL.instr_point_sema point initial final -> PL.instr_point_sema (memory_swap_point position point) initial final.
Proof.
  intros WIDTH RUN; inversion RUN as [writes reads EXEC].
  apply PL.ILSema.ip_sema_intro with (wcs := writes) (rcs := reads).
  cbn [memory_swap_point PL.ILSema.ip_instruction PL.ILSema.ip_transformation PL.ILSema.ip_index].
  rewrite memory_swap_affine_product by exact WIDTH; exact EXEC.
Qed.
Lemma memory_valid_point_transform_width parameters instructions point :
  Forall (memory_identity_representation (length parameters)) instructions ->
  memory_sequence_valid_point parameters instructions point ->
  Forall (fun row => length (fst row) = length (PL.ILSema.ip_index point)) (PL.ILSema.ip_transformation point).
Proof.
  intros REPRESENTATIONS [pi [NTH [PREFIX [BELONG LENGTH]]]].
  pose proof (proj1 (Forall_forall _ _) REPRESENTATIONS pi ltac:(eapply nth_error_In; exact NTH)) as [IDENTITY [_ [_ WIDTH]]].
  unfold PL.belongs_to in BELONG; destruct BELONG as [_ [TRANSFORM _]].
  rewrite TRANSFORM,memory_identity_current_transform by exact IDENTITY; rewrite LENGTH; exact WIDTH.
Qed.

Definition memory_coordinate_swap_isomorphism position parameters instructions
  (PREFIX : (length parameters <= position)%nat)
  (REPRESENTATIONS : Forall (memory_identity_representation (length parameters)) instructions) :
  memory_point_isomorphism parameters instructions (memory_swap_instructions position instructions).
Proof.
  assert (TARGET_REP : Forall (memory_identity_representation (length parameters)) (memory_swap_instructions position instructions)).
  { unfold memory_swap_instructions; apply Forall_map; eapply Forall_impl; [|exact REPRESENTATIONS].
    intros pi REP; apply memory_swap_instruction_representation; exact REP. }
  refine {| point_forward := memory_swap_point position; point_backward := memory_swap_point position |}.
  - intros point VALID; apply memory_swap_valid_point; assumption.
  - intros point VALID.
    pose proof (@memory_swap_valid_point position parameters _ point PREFIX TARGET_REP VALID) as SOURCE.
    rewrite memory_swap_instructions_inverse in SOURCE; exact SOURCE.
  - intros; apply memory_swap_point_inverse.
  - intros; apply memory_swap_point_inverse.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros point initial final VALID RUN; apply memory_swap_point_execution; [|exact RUN].
    exact (@memory_valid_point_transform_width parameters instructions point REPRESENTATIONS VALID).
  - intros point initial final VALID RUN; apply memory_swap_point_execution; [|exact RUN].
    exact (@memory_valid_point_transform_width parameters _ point TARGET_REP VALID).
Defined.
Theorem memory_coordinate_swap_execution position parameters instructions context vars initial final :
  (length parameters <= position)%nat ->
  Forall (memory_identity_representation (length parameters)) instructions ->
  (PL.poly_instance_list_semantics parameters (instructions,context,vars) initial final <->
   PL.poly_instance_list_semantics parameters (memory_swap_instructions position instructions,context,vars) initial final).
Proof. intros PREFIX REPRESENTATIONS; apply memory_point_isomorphism_execution;
  apply memory_coordinate_swap_isomorphism; assumption. Qed.
Print Assumptions memory_coordinate_swap_execution.
