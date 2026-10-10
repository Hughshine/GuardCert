From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg.
From polcert.polygen Require Import PolIRs.
From Guard Require Import PolCertCandidateRepresentation.
Import ListNotations.
Set Implicit Arguments.

(** Restrict a model to already established parameter facts. This is neither
    a runtime-check compiler nor a new assumption inference algorithm. *)
Lemma piece_dot_prefix count index coefficients :
  (length coefficients<=count)%nat -> dot_product index coefficients=dot_product (firstn count index) coefficients.
Proof.
  revert index coefficients; induction count; intros [|x xs] [|c cs] WIDTH; cbn in WIDTH |- *;
    try reflexivity; try lia; rewrite IHcount by lia; reflexivity.
Qed.
Lemma piece_domain_prefix count index guards :
  Forall (fun row=>length (fst row)<=count)%nat guards ->
  in_poly index guards=in_poly (firstn count index) guards.
Proof.
  intro WIDTH; induction WIDTH as [|[coefficients bias] guards WIDTH REST IH]; [reflexivity|].
  change ((dot_product index coefficients <=? bias)%Z && in_poly index guards =
    (dot_product (firstn count index) coefficients <=? bias)%Z && in_poly (firstn count index) guards).
  rewrite (@piece_dot_prefix count index coefficients WIDTH),IH; reflexivity.
Qed.
Definition piece_resize_guards width (guards : list (list Z*Z)) :=
  map (fun row=>(resize width (fst row),snd row)) guards.
Lemma piece_resize_guards_correct width guards index : length index=width ->
  in_poly index (piece_resize_guards width guards)=in_poly index guards.
Proof.
  intro LENGTH; induction guards as [|[coefficients bias] guards IH]; [reflexivity|].
  change ((dot_product index (resize width coefficients)<=?bias)%Z && in_poly index (piece_resize_guards width guards) =
    (dot_product index coefficients<=?bias)%Z && in_poly index guards).
  rewrite <- LENGTH at 1; rewrite dot_product_resize_right,IH; reflexivity.
Qed.

Module PolCertPieceParameterDomainsFor (IRs : POLIRS).
Module C := PolCertCandidateRepresentationFor IRs.
Module PL := IRs.PolyLang.
Definition piece_restrict_instruction count guards (instruction : PL.PolyInstr) :=
  C.memory_replace_domain
    (piece_resize_guards (count+PL.pi_depth instruction) guards ++ PL.pi_poly instruction) instruction.
Definition piece_restrict_program count guards := map (piece_restrict_instruction count guards).
Lemma piece_restricted_belongs parameters guards instruction point :
  Forall (fun row=>length (fst row)<=length parameters)%nat guards ->
  in_poly parameters guards=true ->
  firstn (length parameters) (PL.ILSema.ip_index point)=parameters ->
  length (PL.ILSema.ip_index point)=(length parameters+PL.pi_depth instruction)%nat ->
  (PL.belongs_to point (piece_restrict_instruction (length parameters) guards instruction) <-> PL.belongs_to point instruction).
Proof.
  intros WIDTH ACCEPT PREFIX LENGTH; unfold PL.belongs_to,piece_restrict_instruction.
  cbn [C.memory_replace_domain PL.pi_poly PL.pi_schedule PL.pi_point_witness PL.pi_transformation
    PL.pi_access_transformation PL.pi_instr PL.pi_depth].
  rewrite in_poly_app,piece_resize_guards_correct by exact LENGTH.
  rewrite (@piece_domain_prefix (length parameters) (PL.ILSema.ip_index point) guards WIDTH),PREFIX,ACCEPT; reflexivity.
Qed.
Theorem piece_restricted_valid parameters guards instructions point :
  Forall (fun row=>length (fst row)<=length parameters)%nat guards ->
  in_poly parameters guards=true ->
  (C.memory_sequence_valid_point parameters (piece_restrict_program (length parameters) guards instructions) point <->
   C.memory_sequence_valid_point parameters instructions point).
Proof.
  intros WIDTH ACCEPT; unfold C.memory_sequence_valid_point,piece_restrict_program; split.
  - intros [restricted [NTH [PREFIX [BELONG LENGTH]]]].
    rewrite nth_error_map in NTH.
    destruct (nth_error instructions (PL.ILSema.ip_nth point)) as [instruction|] eqn:ORIGINAL; [|discriminate].
    inversion NTH; subst restricted.
    exists instruction; split; [reflexivity|]; split; [exact PREFIX|]; split; [|exact LENGTH].
    apply (proj1 (@piece_restricted_belongs parameters guards instruction point WIDTH ACCEPT PREFIX LENGTH)); exact BELONG.
  - intros [instruction [NTH [PREFIX [BELONG LENGTH]]]].
    exists (piece_restrict_instruction (length parameters) guards instruction); split.
    + rewrite nth_error_map,NTH; reflexivity.
    + split; [exact PREFIX|]; split; [|exact LENGTH].
      apply (proj2 (@piece_restricted_belongs parameters guards instruction point WIDTH ACCEPT PREFIX LENGTH)); exact BELONG.
Qed.
Definition piece_restriction_isomorphism parameters guards instructions
  (WIDTH : Forall (fun row=>length (fst row)<=length parameters)%nat guards)
  (ACCEPT : in_poly parameters guards=true) :
  C.memory_point_isomorphism parameters instructions (piece_restrict_program (length parameters) guards instructions).
Proof.
  refine {| C.point_forward:=fun point=>point; C.point_backward:=fun point=>point |};
    intros; try reflexivity; try assumption;
    apply (@piece_restricted_valid parameters guards instructions point WIDTH ACCEPT); assumption.
Defined.
Theorem piece_restriction_execution parameters guards instructions context vars initial final :
  length context=length parameters ->
  Forall (fun row=>length (fst row)<=length parameters)%nat guards -> in_poly parameters guards=true ->
  (PL.poly_instance_list_semantics parameters (instructions,context,vars) initial final <->
   PL.poly_instance_list_semantics parameters (piece_restrict_program (length parameters) guards instructions,context,vars) initial final).
Proof.
  intros LENGTH WIDTH ACCEPT; eapply C.memory_point_isomorphism_execution; [|exact LENGTH].
  exact (@piece_restriction_isomorphism parameters guards instructions WIDTH ACCEPT).
Qed.
End PolCertPieceParameterDomainsFor.

Print Assumptions piece_dot_prefix.
Print Assumptions piece_domain_prefix.
Print Assumptions piece_resize_guards_correct.
