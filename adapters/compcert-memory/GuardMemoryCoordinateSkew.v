From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PointWitness.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryPolyhedral GuardMemoryPolyhedralRectangles
  GuardMemorySequencePolyhedral GuardMemoryPointIsomorphism GuardMemoryCoordinateSwap GuardMemoryCoordinateShift.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_shift_coordinate_nth_other position delta values probe :
  probe <> position -> nth probe (memory_shift_coordinate position delta values) 0 = nth probe values 0.
Proof.
  revert probe values; induction position; intros probe values DISTINCT;
    destruct probe,values; cbn; try reflexivity; try lia.
  apply IHposition; congruence.
Qed.
Lemma memory_shift_dot_product_left position delta coefficients index :
  length coefficients = length index ->
  dot_product (memory_shift_coordinate position delta coefficients) index =
    dot_product coefficients index + delta*nth position index 0.
Proof.
  intro WIDTH; rewrite dot_product_commutative,memory_shift_dot_product by (symmetry; exact WIDTH).
  rewrite dot_product_commutative; reflexivity.
Qed.
Definition memory_skew_coordinates target source factor values :=
  if Nat.eqb target source then values else memory_shift_coordinate target (factor*nth source values 0) values.
Lemma memory_skew_coordinates_length target source factor values :
  length (memory_skew_coordinates target source factor values) = length values.
Proof. unfold memory_skew_coordinates; destruct Nat.eqb; [reflexivity|apply memory_shift_coordinate_length]. Qed.
Lemma memory_skew_coordinates_inverse target source factor values :
  memory_skew_coordinates target source (-factor) (memory_skew_coordinates target source factor values) = values.
Proof.
  unfold memory_skew_coordinates; destruct (Nat.eqb target source) eqn:SAME; [reflexivity|].
  apply Nat.eqb_neq in SAME.
  rewrite memory_shift_coordinate_nth_other by congruence.
  replace (-factor*nth source values 0) with (-(factor*nth source values 0)) by ring.
  apply memory_shift_coordinate_inverse.
Qed.
Lemma memory_skew_coordinates_prefix target source factor count values :
  (count <= target)%nat -> firstn count (memory_skew_coordinates target source factor values) = firstn count values.
Proof.
  intro PREFIX; unfold memory_skew_coordinates; destruct Nat.eqb; [reflexivity|].
  apply memory_shift_coordinate_prefix; exact PREFIX.
Qed.
Definition memory_skew_coefficients target source factor coefficients :=
  memory_skew_coordinates source target (-factor) coefficients.
Lemma memory_skew_coefficients_inverse target source factor coefficients :
  memory_skew_coefficients target source (-factor) (memory_skew_coefficients target source factor coefficients) = coefficients.
Proof. unfold memory_skew_coefficients; apply memory_skew_coordinates_inverse. Qed.
Lemma memory_skew_dot_product target source factor coefficients index :
  length coefficients = length index ->
  dot_product (memory_skew_coefficients target source factor coefficients)
    (memory_skew_coordinates target source factor index) = dot_product coefficients index.
Proof.
  intro WIDTH; unfold memory_skew_coefficients,memory_skew_coordinates.
  rewrite (Nat.eqb_sym source target); destruct (Nat.eqb target source) eqn:SAME; [reflexivity|].
  apply Nat.eqb_neq in SAME.
  rewrite memory_shift_dot_product_left by (rewrite memory_shift_coordinate_length; exact WIDTH).
  rewrite memory_shift_dot_product by exact WIDTH.
  rewrite memory_shift_coordinate_nth_other by congruence; ring.
Qed.
Definition memory_skew_affine target source factor (row : list Z * Z) :=
  (memory_skew_coefficients target source factor (fst row),snd row).
Definition memory_skew_affines target source factor := map (memory_skew_affine target source factor).
Lemma memory_skew_affines_inverse target source factor rows :
  memory_skew_affines target source (-factor) (memory_skew_affines target source factor rows) = rows.
Proof.
  induction rows as [|[coefficients bias] rows IH]; [reflexivity|].
  change ((memory_skew_coefficients target source (-factor) (memory_skew_coefficients target source factor coefficients),bias)::
    memory_skew_affines target source (-factor) (memory_skew_affines target source factor rows) = (coefficients,bias)::rows).
  rewrite memory_skew_coefficients_inverse,IH; reflexivity.
Qed.
Lemma memory_skew_affine_product target source factor rows index :
  Forall (fun row => length (fst row) = length index) rows ->
  affine_product (memory_skew_affines target source factor rows) (memory_skew_coordinates target source factor index) = affine_product rows index.
Proof.
  intro WIDTH; induction WIDTH; [reflexivity|].
  destruct x as [coefficients bias].
  change ((dot_product (memory_skew_coefficients target source factor coefficients)
    (memory_skew_coordinates target source factor index)+bias)::
    affine_product (memory_skew_affines target source factor l) (memory_skew_coordinates target source factor index) =
    (dot_product coefficients index+bias)::affine_product l index).
  rewrite memory_skew_dot_product by exact H; rewrite IHWIDTH; reflexivity.
Qed.
Lemma memory_skew_domain target source factor rows index :
  Forall (fun row => length (fst row) = length index) rows ->
  in_poly (memory_skew_coordinates target source factor index) (memory_skew_affines target source factor rows) = in_poly index rows.
Proof.
  intro WIDTH; induction WIDTH; [reflexivity|].
  destruct x as [coefficients bias].
  change ((dot_product (memory_skew_coordinates target source factor index)
    (memory_skew_coefficients target source factor coefficients) <=? bias) &&
    in_poly (memory_skew_coordinates target source factor index) (memory_skew_affines target source factor l) =
    (dot_product index coefficients <=? bias) && in_poly index l).
  rewrite (dot_product_commutative (memory_skew_coordinates target source factor index)
    (memory_skew_coefficients target source factor coefficients)),memory_skew_dot_product by exact H.
  rewrite (dot_product_commutative index coefficients),IHWIDTH; reflexivity.
Qed.
Definition memory_skew_instruction target source factor (pi : PL.PolyInstr) : PL.PolyInstr :=
  {| PL.pi_depth := PL.pi_depth pi; PL.pi_instr := PL.pi_instr pi;
     PL.pi_poly := memory_skew_affines target source factor (PL.pi_poly pi);
     PL.pi_schedule := memory_skew_affines target source factor (PL.pi_schedule pi);
     PL.pi_point_witness := PL.pi_point_witness pi;
     PL.pi_transformation := memory_skew_affines target source factor (PL.pi_transformation pi);
     PL.pi_access_transformation := memory_skew_affines target source factor (PL.pi_access_transformation pi);
     PL.pi_waccess := PL.pi_waccess pi; PL.pi_raccess := PL.pi_raccess pi |}.
Definition memory_skew_instructions target source factor := map (memory_skew_instruction target source factor).
Definition memory_skew_point target source factor (point : PL.InstrPoint) : PL.InstrPoint :=
  {| PL.ILSema.ip_nth := PL.ILSema.ip_nth point;
     PL.ILSema.ip_index := memory_skew_coordinates target source factor (PL.ILSema.ip_index point);
     PL.ILSema.ip_transformation := memory_skew_affines target source factor (PL.ILSema.ip_transformation point);
     PL.ILSema.ip_time_stamp := PL.ILSema.ip_time_stamp point;
     PL.ILSema.ip_instruction := PL.ILSema.ip_instruction point;
     PL.ILSema.ip_depth := PL.ILSema.ip_depth point |}.
Lemma memory_skew_instruction_inverse target source factor pi :
  memory_skew_instruction target source (-factor) (memory_skew_instruction target source factor pi) = pi.
Proof. destruct pi; unfold memory_skew_instruction; cbn; rewrite !memory_skew_affines_inverse; reflexivity. Qed.
Lemma memory_skew_instructions_inverse target source factor instructions :
  memory_skew_instructions target source (-factor) (memory_skew_instructions target source factor instructions) = instructions.
Proof. induction instructions; cbn [memory_skew_instructions map];
  [reflexivity|rewrite memory_skew_instruction_inverse,IHinstructions; reflexivity]. Qed.
Lemma memory_skew_point_inverse target source factor point :
  memory_skew_point target source (-factor) (memory_skew_point target source factor point) = point.
Proof. destruct point; unfold memory_skew_point; cbn; rewrite memory_skew_coordinates_inverse,memory_skew_affines_inverse; reflexivity. Qed.

Lemma memory_skew_instruction_representation target source factor dimension pi :
  memory_identity_representation dimension pi ->
  memory_identity_representation dimension (memory_skew_instruction target source factor pi).
Proof.
  intros [IDENTITY [DOMAIN [SCHEDULE TRANSFORM]]]; split; [exact IDENTITY|].
  repeat split; unfold memory_skew_affines; apply Forall_map; eapply Forall_impl;
    [|exact DOMAIN| |exact SCHEDULE| |exact TRANSFORM];
    intros row WIDTH; cbn [memory_skew_affine fst]; unfold memory_skew_coefficients; rewrite memory_skew_coordinates_length; exact WIDTH.
Qed.

Lemma memory_skew_valid_point target source factor parameters instructions point :
  (length parameters <= target)%nat ->
  Forall (memory_identity_representation (length parameters)) instructions ->
  memory_sequence_valid_point parameters instructions point ->
  memory_sequence_valid_point parameters (memory_skew_instructions target source factor instructions) (memory_skew_point target source factor point).
Proof.
  intros PREFIX REPRESENTATIONS [pi [NTH [PARAMS [BELONG LENGTH]]]].
  assert (REP := proj1 (Forall_forall _ _) REPRESENTATIONS pi ltac:(eapply nth_error_In; exact NTH)).
  destruct REP as [IDENTITY [DOMAIN [SCHEDULE TRANSFORM]]].
  exists (memory_skew_instruction target source factor pi); split.
  - unfold memory_skew_instructions; rewrite nth_error_map; cbn [memory_skew_point PL.ILSema.ip_nth]; rewrite NTH; reflexivity.
  - split.
    + cbn [memory_skew_point PL.ILSema.ip_index]; rewrite memory_skew_coordinates_prefix by exact PREFIX; exact PARAMS.
    + split.
      * unfold PL.belongs_to in BELONG |- *.
        destruct BELONG as [IN [TF [TIME [INSTRUCTION DEPTH]]]].
        cbn [memory_skew_point memory_skew_instruction PL.ILSema.ip_index PL.ILSema.ip_transformation
          PL.ILSema.ip_time_stamp PL.ILSema.ip_instruction PL.ILSema.ip_depth PL.pi_poly PL.pi_schedule PL.pi_instr PL.pi_depth].
        split.
        -- rewrite memory_skew_domain; [exact IN|rewrite LENGTH; exact DOMAIN].
        -- split.
           ++ rewrite memory_identity_current_transform in TF by exact IDENTITY.
              rewrite memory_identity_current_transform by exact IDENTITY; rewrite TF; reflexivity.
           ++ split.
              ** rewrite memory_skew_affine_product; [exact TIME|rewrite LENGTH; exact SCHEDULE].
              ** split; assumption.
      * cbn [memory_skew_point memory_skew_instruction PL.ILSema.ip_index PL.pi_depth]; rewrite memory_skew_coordinates_length; exact LENGTH.
Qed.

Lemma memory_skew_point_execution target source factor point initial final :
  Forall (fun row => length (fst row) = length (PL.ILSema.ip_index point)) (PL.ILSema.ip_transformation point) ->
  PL.instr_point_sema point initial final -> PL.instr_point_sema (memory_skew_point target source factor point) initial final.
Proof.
  intros WIDTH RUN; inversion RUN as [writes reads EXEC].
  apply PL.ILSema.ip_sema_intro with (wcs := writes) (rcs := reads).
  cbn [memory_skew_point PL.ILSema.ip_instruction PL.ILSema.ip_transformation PL.ILSema.ip_index].
  rewrite memory_skew_affine_product by exact WIDTH; exact EXEC.
Qed.
Definition memory_coordinate_skew_isomorphism target source factor parameters instructions
  (PREFIX : (length parameters <= target)%nat)
  (REPRESENTATIONS : Forall (memory_identity_representation (length parameters)) instructions) :
  memory_point_isomorphism parameters instructions (memory_skew_instructions target source factor instructions).
Proof.
  assert (TARGET_REP : Forall (memory_identity_representation (length parameters)) (memory_skew_instructions target source factor instructions)).
  { unfold memory_skew_instructions; apply Forall_map; eapply Forall_impl; [|exact REPRESENTATIONS].
    intros pi REP; apply memory_skew_instruction_representation; exact REP. }
  refine {| point_forward := memory_skew_point target source factor; point_backward := memory_skew_point target source (-factor) |}.
  - intros point VALID; apply memory_skew_valid_point; assumption.
  - intros point VALID.
    pose proof (@memory_skew_valid_point target source (-factor) parameters _ point PREFIX TARGET_REP VALID) as SOURCE.
    rewrite memory_skew_instructions_inverse in SOURCE; exact SOURCE.
  - intros; apply memory_skew_point_inverse.
  - intros point VALID; replace factor with (-(-factor)) at 1 by ring; apply memory_skew_point_inverse.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros point initial final VALID RUN; apply memory_skew_point_execution; [|exact RUN].
    exact (@memory_valid_point_transform_width parameters instructions point REPRESENTATIONS VALID).
  - intros point initial final VALID RUN; apply memory_skew_point_execution; [|exact RUN].
    exact (@memory_valid_point_transform_width parameters _ point TARGET_REP VALID).
Defined.
Theorem memory_coordinate_skew_execution target source factor parameters instructions context vars initial final :
  (length parameters <= target)%nat ->
  Forall (memory_identity_representation (length parameters)) instructions ->
  (PL.poly_instance_list_semantics parameters (instructions,context,vars) initial final <->
   PL.poly_instance_list_semantics parameters (memory_skew_instructions target source factor instructions,context,vars) initial final).
Proof. intros PREFIX REPRESENTATIONS; apply memory_point_isomorphism_execution;
  apply memory_coordinate_skew_isomorphism; assumption. Qed.
Print Assumptions memory_coordinate_skew_execution.
