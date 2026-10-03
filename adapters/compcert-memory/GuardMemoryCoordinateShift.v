From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PointWitness.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryPolyhedral GuardMemoryPolyhedralRectangles
  GuardMemorySequencePolyhedral GuardMemoryPointIsomorphism GuardMemoryCoordinateSwap.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_shift_coordinate position delta (values : list Z) :=
  match position,values with
  | O,first::rest => (first+delta)::rest
  | S index,first::rest => first::memory_shift_coordinate index delta rest
  | _,_ => values end.
Lemma memory_shift_coordinate_length position delta values :
  length (memory_shift_coordinate position delta values) = length values.
Proof. revert values; induction position; intros [|first rest]; cbn; auto. Qed.
Lemma memory_shift_coordinate_inverse position delta values :
  memory_shift_coordinate position (-delta) (memory_shift_coordinate position delta values) = values.
Proof.
  revert values; induction position; intros [|first rest]; cbn; try reflexivity.
  - f_equal; ring.
  - rewrite IHposition; reflexivity.
Qed.
Lemma memory_shift_coordinate_prefix position delta count values :
  (count <= position)%nat -> firstn count (memory_shift_coordinate position delta values) = firstn count values.
Proof.
  revert count values; induction position; intros count values ORDER;
    destruct count; cbn; [reflexivity|lia|reflexivity|].
  destruct values; cbn; [reflexivity|]; f_equal; apply IHposition; lia.
Qed.
Lemma memory_shift_dot_product position delta coefficients index :
  length coefficients = length index ->
  dot_product coefficients (memory_shift_coordinate position delta index) =
    dot_product coefficients index + delta*nth position coefficients 0.
Proof.
  revert coefficients index; induction position; intros coefficients index WIDTH;
    destruct coefficients as [|a coefficients],index as [|b index]; cbn in WIDTH |- *; try lia; try ring.
  rewrite IHposition by lia; ring.
Qed.
Definition memory_shift_affine position delta (row : list Z * Z) :=
  (fst row,snd row-delta*nth position (fst row) 0).
Definition memory_shift_affines position delta := map (memory_shift_affine position delta).
Definition memory_shift_domain position delta (row : list Z * Z) :=
  (fst row,snd row+delta*nth position (fst row) 0).
Definition memory_shift_domains position delta := map (memory_shift_domain position delta).
Lemma memory_shift_affines_inverse position delta rows :
  memory_shift_affines position (-delta) (memory_shift_affines position delta rows) = rows.
Proof.
  induction rows as [|[coefficients bias] rows IH]; cbn [memory_shift_affines memory_shift_affine map fst snd];
    [reflexivity|rewrite IH; unfold memory_shift_affine; cbn [fst snd];
      replace (bias-delta*nth position coefficients 0-(-delta)*nth position coefficients 0)
      with bias by ring; reflexivity].
Qed.
Lemma memory_shift_domains_inverse position delta rows :
  memory_shift_domains position (-delta) (memory_shift_domains position delta rows) = rows.
Proof.
  induction rows as [|[coefficients bias] rows IH]; cbn [memory_shift_domains memory_shift_domain map fst snd];
    [reflexivity|rewrite IH; unfold memory_shift_domain; cbn [fst snd];
      replace (bias+delta*nth position coefficients 0+(-delta)*nth position coefficients 0)
      with bias by ring; reflexivity].
Qed.
Lemma memory_shift_affine_product position delta rows index :
  Forall (fun row => length (fst row) = length index) rows ->
  affine_product (memory_shift_affines position delta rows) (memory_shift_coordinate position delta index) = affine_product rows index.
Proof.
  intro WIDTH; induction WIDTH; [reflexivity|].
  destruct x as [coefficients bias].
  change ((dot_product coefficients (memory_shift_coordinate position delta index)+
    (bias-delta*nth position coefficients 0))::
    affine_product (memory_shift_affines position delta l) (memory_shift_coordinate position delta index) =
    (dot_product coefficients index+bias)::affine_product l index).
  rewrite memory_shift_dot_product by exact H; rewrite IHWIDTH; f_equal; ring.
Qed.
Lemma memory_shift_domain_evaluation position delta rows index :
  Forall (fun row => length (fst row) = length index) rows ->
  in_poly (memory_shift_coordinate position delta index) (memory_shift_domains position delta rows) = in_poly index rows.
Proof.
  intro WIDTH; induction WIDTH; [reflexivity|].
  destruct x as [coefficients bias].
  change ((dot_product (memory_shift_coordinate position delta index) coefficients <=?
    bias+delta*nth position coefficients 0) &&
    in_poly (memory_shift_coordinate position delta index) (memory_shift_domains position delta l) =
    (dot_product index coefficients <=? bias) && in_poly index l).
  rewrite (dot_product_commutative (memory_shift_coordinate position delta index) coefficients),
    memory_shift_dot_product by exact H.
  rewrite (dot_product_commutative index coefficients),IHWIDTH.
  f_equal; apply Bool.eq_true_iff_eq; rewrite !Z.leb_le; lia.
Qed.
Definition memory_shift_instruction position delta (pi : PL.PolyInstr) : PL.PolyInstr :=
  {| PL.pi_depth := PL.pi_depth pi; PL.pi_instr := PL.pi_instr pi;
     PL.pi_poly := memory_shift_domains position delta (PL.pi_poly pi);
     PL.pi_schedule := memory_shift_affines position delta (PL.pi_schedule pi);
     PL.pi_point_witness := PL.pi_point_witness pi;
     PL.pi_transformation := memory_shift_affines position delta (PL.pi_transformation pi);
     PL.pi_access_transformation := memory_shift_affines position delta (PL.pi_access_transformation pi);
     PL.pi_waccess := PL.pi_waccess pi; PL.pi_raccess := PL.pi_raccess pi |}.
Definition memory_shift_instructions position delta := map (memory_shift_instruction position delta).
Definition memory_shift_point position delta (point : PL.InstrPoint) : PL.InstrPoint :=
  {| PL.ILSema.ip_nth := PL.ILSema.ip_nth point;
     PL.ILSema.ip_index := memory_shift_coordinate position delta (PL.ILSema.ip_index point);
     PL.ILSema.ip_transformation := memory_shift_affines position delta (PL.ILSema.ip_transformation point);
     PL.ILSema.ip_time_stamp := PL.ILSema.ip_time_stamp point;
     PL.ILSema.ip_instruction := PL.ILSema.ip_instruction point;
     PL.ILSema.ip_depth := PL.ILSema.ip_depth point |}.
Lemma memory_shift_instruction_inverse position delta pi :
  memory_shift_instruction position (-delta) (memory_shift_instruction position delta pi) = pi.
Proof. destruct pi; unfold memory_shift_instruction; cbn;
  rewrite memory_shift_affines_inverse,memory_shift_domains_inverse,!memory_shift_affines_inverse; reflexivity. Qed.
Lemma memory_shift_instructions_inverse position delta instructions :
  memory_shift_instructions position (-delta) (memory_shift_instructions position delta instructions) = instructions.
Proof. induction instructions; cbn [memory_shift_instructions map];
  [reflexivity|rewrite memory_shift_instruction_inverse,IHinstructions; reflexivity]. Qed.
Lemma memory_shift_point_inverse position delta point :
  memory_shift_point position (-delta) (memory_shift_point position delta point) = point.
Proof. destruct point; unfold memory_shift_point; cbn;
  rewrite memory_shift_coordinate_inverse,memory_shift_affines_inverse; reflexivity. Qed.
Lemma memory_shift_instruction_representation position delta dimension pi :
  memory_identity_representation dimension pi ->
  memory_identity_representation dimension (memory_shift_instruction position delta pi).
Proof.
  intros [IDENTITY [DOMAIN [SCHEDULE TRANSFORM]]]; split; [exact IDENTITY|].
  repeat split; unfold memory_shift_domains,memory_shift_affines; apply Forall_map; eapply Forall_impl;
    [|exact DOMAIN| |exact SCHEDULE| |exact TRANSFORM]; intros row WIDTH; exact WIDTH.
Qed.
Lemma memory_shift_valid_point position delta parameters instructions point :
  (length parameters <= position)%nat ->
  Forall (memory_identity_representation (length parameters)) instructions ->
  memory_sequence_valid_point parameters instructions point ->
  memory_sequence_valid_point parameters (memory_shift_instructions position delta instructions) (memory_shift_point position delta point).
Proof.
  intros PREFIX REPRESENTATIONS [pi [NTH [PARAMS [BELONG LENGTH]]]].
  assert (REP := proj1 (Forall_forall _ _) REPRESENTATIONS pi ltac:(eapply nth_error_In; exact NTH)).
  destruct REP as [IDENTITY [DOMAIN [SCHEDULE TRANSFORM]]].
  exists (memory_shift_instruction position delta pi); split.
  - unfold memory_shift_instructions; rewrite nth_error_map; cbn [memory_shift_point PL.ILSema.ip_nth]; rewrite NTH; reflexivity.
  - split.
    + cbn [memory_shift_point PL.ILSema.ip_index]; rewrite memory_shift_coordinate_prefix by exact PREFIX; exact PARAMS.
    + split.
      * unfold PL.belongs_to in BELONG |- *.
        destruct BELONG as [IN [TF [TIME [INSTRUCTION DEPTH]]]].
        cbn [memory_shift_point memory_shift_instruction PL.ILSema.ip_index PL.ILSema.ip_transformation
          PL.ILSema.ip_time_stamp PL.ILSema.ip_instruction PL.ILSema.ip_depth PL.pi_poly PL.pi_schedule PL.pi_instr PL.pi_depth].
        split.
        -- rewrite memory_shift_domain_evaluation; [exact IN|rewrite LENGTH; exact DOMAIN].
        -- split.
           ++ rewrite memory_identity_current_transform in TF by exact IDENTITY.
              rewrite memory_identity_current_transform by exact IDENTITY; rewrite TF; reflexivity.
           ++ split.
              ** rewrite memory_shift_affine_product; [exact TIME|rewrite LENGTH; exact SCHEDULE].
              ** split; assumption.
      * cbn [memory_shift_point memory_shift_instruction PL.ILSema.ip_index PL.pi_depth];
        rewrite memory_shift_coordinate_length; exact LENGTH.
Qed.
Lemma memory_shift_point_execution position delta point initial final :
  Forall (fun row => length (fst row) = length (PL.ILSema.ip_index point)) (PL.ILSema.ip_transformation point) ->
  PL.instr_point_sema point initial final -> PL.instr_point_sema (memory_shift_point position delta point) initial final.
Proof.
  intros WIDTH RUN; inversion RUN as [writes reads EXEC].
  apply PL.ILSema.ip_sema_intro with (wcs := writes) (rcs := reads).
  cbn [memory_shift_point PL.ILSema.ip_instruction PL.ILSema.ip_transformation PL.ILSema.ip_index].
  rewrite memory_shift_affine_product by exact WIDTH; exact EXEC.
Qed.
Definition memory_coordinate_shift_isomorphism position delta parameters instructions
  (PREFIX : (length parameters <= position)%nat)
  (REPRESENTATIONS : Forall (memory_identity_representation (length parameters)) instructions) :
  memory_point_isomorphism parameters instructions (memory_shift_instructions position delta instructions).
Proof.
  assert (TARGET_REP : Forall (memory_identity_representation (length parameters)) (memory_shift_instructions position delta instructions)).
  { unfold memory_shift_instructions; apply Forall_map; eapply Forall_impl; [|exact REPRESENTATIONS].
    intros pi REP; apply memory_shift_instruction_representation; exact REP. }
  refine {| point_forward := memory_shift_point position delta; point_backward := memory_shift_point position (-delta) |}.
  - intros point VALID; apply memory_shift_valid_point; assumption.
  - intros point VALID.
    pose proof (@memory_shift_valid_point position (-delta) parameters _ point PREFIX TARGET_REP VALID) as SOURCE.
    rewrite memory_shift_instructions_inverse in SOURCE; exact SOURCE.
  - intros; apply memory_shift_point_inverse.
  - intros point VALID; replace delta with (-(-delta)) at 1 by ring; apply memory_shift_point_inverse.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros point initial final VALID RUN; apply memory_shift_point_execution; [|exact RUN].
    exact (@memory_valid_point_transform_width parameters instructions point REPRESENTATIONS VALID).
  - intros point initial final VALID RUN; apply memory_shift_point_execution; [|exact RUN].
    exact (@memory_valid_point_transform_width parameters _ point TARGET_REP VALID).
Defined.
Theorem memory_coordinate_shift_execution position delta parameters instructions context vars initial final :
  (length parameters <= position)%nat ->
  Forall (memory_identity_representation (length parameters)) instructions ->
  (PL.poly_instance_list_semantics parameters (instructions,context,vars) initial final <->
   PL.poly_instance_list_semantics parameters (memory_shift_instructions position delta instructions,context,vars) initial final).
Proof. intros PREFIX REPRESENTATIONS; apply memory_point_isomorphism_execution;
  apply memory_coordinate_shift_isomorphism; assumption. Qed.
Print Assumptions memory_coordinate_shift_execution.
