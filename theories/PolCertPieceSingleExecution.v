From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg ImpureAlarmConfig.
From polcert.src Require Import PointWitness.
From polcert.polygen Require Import PolIRs.
From Vpl Require Import Impure.
From Guard Require Import PolCertPieceCoordinates PolCertPieceFamily PolCertPieceActions PolCertPieceSelection.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** A checked one-to-many representation change. Pieces may have different
    depths. Their schedules are retimed to the source; dependency validation
    of the candidate's actual schedules is a separate obligation. *)
Module PolCertPieceSingleExecutionFor (IRs : POLIRS).
Module A := PolCertPieceActionsFor IRs.
Module S := PolCertPieceSelectionFor IRs.
Import A.
Definition piece_item := (PL.PolyInstr * piece_coordinates)%type.
Definition single_coordinates (items : list piece_item) := map snd items.
Definition single_target source (items : list piece_item) :=
  map (fun item=>A.piece_retimed_instruction source (fst item) (snd item)) items.
Definition piece_domain_dec (left right : list (list Z*Z)) : {left=right}+{left<>right}.
Proof. apply list_eq_dec; decide equality; [apply Z.eq_dec|apply list_eq_dec; apply Z.eq_dec]. Defined.
Fixpoint check_single_actions count source (items : list piece_item) := match items with
  | []=>pure true
  | (candidate,piece)::rest=>
    if piece_domain_dec (piece_domain piece) (PL.pi_poly candidate) then
      BIND action <- A.check_piece_actions count source candidate piece -;
      if action then check_single_actions count source rest else pure false
    else pure false end.
Definition check_single_family count source items witness :=
  if A.piece_identity_shape source then
    BIND actions <- check_single_actions count source items -;
    if actions then S.F.check_piece_family (count+PL.pi_depth source)
      (PL.pi_poly source) (single_coordinates items) witness else pure false
  else pure false.
Record single_certificate count source items := SingleCertificate {
  single_identity : PL.pi_point_witness source=PSWIdentity (PL.pi_depth source);
  single_actions : Forall (fun item=>piece_domain (snd item)=PL.pi_poly (fst item) /\
    A.piece_action_certificate count source (fst item) (snd item)) items;
  single_family : S.F.piece_family_certificate (count+PL.pi_depth source)
    (PL.pi_poly source) (single_coordinates items)
}.
Lemma check_single_actions_sound count source items :
  mayReturn (check_single_actions count source items) true ->
  Forall (fun item=>piece_domain (snd item)=PL.pi_poly (fst item) /\
    A.piece_action_certificate count source (fst item) (snd item)) items.
Proof.
  induction items as [|[candidate piece] rest IH]; cbn; intro CHECK; [constructor|].
  destruct (piece_domain_dec (piece_domain piece) (PL.pi_poly candidate)) as [DOMAIN|];
    [|apply mayReturn_pure in CHECK; discriminate].
  bind_imp_destruct CHECK action ACTION; destruct action;
    [|apply mayReturn_pure in CHECK; discriminate].
  constructor; [split; [exact DOMAIN|eapply A.check_piece_actions_sound; exact ACTION]|auto].
Qed.
Theorem check_single_family_sound count source items witness :
  mayReturn (check_single_family count source items witness) true -> single_certificate count source items.
Proof.
  unfold check_single_family; destruct (A.piece_identity_shape source) eqn:SHAPE;
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  intro CHECK; bind_imp_destruct CHECK actions ACTIONS; destruct actions;
    [|apply mayReturn_pure in CHECK; discriminate].
  constructor.
  - apply A.piece_identity_shape_sound; exact SHAPE.
  - eapply check_single_actions_sound; exact ACTIONS.
  - eapply S.F.check_piece_family_sound; exact CHECK.
Qed.
Lemma single_item_at count source items ordinal candidate piece
  (certificate : single_certificate count source items) :
  nth_error items ordinal=Some (candidate,piece) ->
  piece_domain piece=PL.pi_poly candidate /\ A.piece_action_certificate count source candidate piece.
Proof.
  intro NTH; pose proof (single_actions certificate) as ALL.
  apply Forall_forall with (x:=(candidate,piece)) in ALL;
    [exact ALL|eapply nth_error_In; exact NTH].
Qed.
Lemma single_coordinate_at items ordinal candidate piece :
  nth_error items ordinal=Some (candidate,piece) -> nth_error (single_coordinates items) ordinal=Some piece.
Proof. intro NTH; unfold single_coordinates; rewrite nth_error_map,NTH; reflexivity. Qed.
Lemma single_item_from_coordinate items ordinal piece :
  nth_error (single_coordinates items) ordinal=Some piece ->
  exists candidate, nth_error items ordinal=Some (candidate,piece).
Proof.
  intro SAME; unfold single_coordinates in SAME; apply Misc.nth_error_map_inv in SAME.
  destruct SAME as [[candidate coordinates] [NTH SAME]].
  cbn in SAME; subst piece; exists candidate; exact NTH.
Qed.
Lemma single_point_canonical instruction point :
  PL.pi_point_witness instruction=PSWIdentity (PL.pi_depth instruction) ->
  PL.belongs_to point instruction ->
  point=A.piece_canonical_point (PL.ILSema.ip_nth point) instruction (PL.ILSema.ip_index point).
Proof.
  intros IDENTITY BELONG; unfold PL.belongs_to in BELONG.
  destruct BELONG as [DOMAIN [TRANSFORM [TIME [INSTRUCTION DEPTH]]]].
  rewrite C.memory_identity_current_transform in TRANSFORM by exact IDENTITY.
  destruct point; cbn in *; subst; reflexivity.
Qed.
Lemma single_retimed_action count source candidate piece
  (certificate : A.piece_action_certificate count source candidate piece) :
  A.piece_action_certificate count source (A.piece_retimed_instruction source candidate piece) piece.
Proof.
  destruct certificate; constructor; cbn [A.piece_retimed_instruction]; assumption.
Qed.
Definition single_forward source items point :=
  match piece_find_image (PL.ILSema.ip_index point) (single_coordinates items) with
  | Some ordinal=>match nth_error items ordinal with
    | Some (candidate,piece)=>A.piece_canonical_point ordinal
      (A.piece_retimed_instruction source candidate piece)
      (affine_product (piece_project piece) (PL.ILSema.ip_index point))
    | None=>point end
  | None=>point end.
Definition single_backward source (items : list piece_item) point := match nth_error items (PL.ILSema.ip_nth point) with
  | Some (candidate,piece)=>A.piece_canonical_point O source
    (affine_product (piece_embed piece) (PL.ILSema.ip_index point))
  | None=>point end.
Lemma single_forward_at source items point ordinal candidate piece :
  piece_find_image (PL.ILSema.ip_index point) (single_coordinates items)=Some ordinal ->
  nth_error items ordinal=Some (candidate,piece) ->
  single_forward source items point=A.piece_canonical_point ordinal
    (A.piece_retimed_instruction source candidate piece)
    (affine_product (piece_project piece) (PL.ILSema.ip_index point)).
Proof. intros FOUND ITEM; unfold single_forward; rewrite FOUND,ITEM; reflexivity. Qed.
Lemma single_backward_at source items point candidate piece :
  nth_error items (PL.ILSema.ip_nth point)=Some (candidate,piece) ->
  single_backward source items point=A.piece_canonical_point O source
    (affine_product (piece_embed piece) (PL.ILSema.ip_index point)).
Proof. intro ITEM; unfold single_backward,piece_item in *; rewrite ITEM; reflexivity. Qed.

Lemma single_source_description parameters source point
  (IDENTITY : PL.pi_point_witness source=PSWIdentity (PL.pi_depth source)) :
  C.memory_sequence_valid_point parameters [source] point ->
  point=A.piece_canonical_point O source (PL.ILSema.ip_index point) /\
  firstn (length parameters) (PL.ILSema.ip_index point)=parameters /\
  in_poly (PL.ILSema.ip_index point) (PL.pi_poly source)=true /\
  length (PL.ILSema.ip_index point)=(length parameters+PL.pi_depth source)%nat.
Proof.
  intros [instruction [NTH [PREFIX [BELONG LENGTH]]]].
  assert (ORDINAL : PL.ILSema.ip_nth point=O).
  { assert (BOUND : (PL.ILSema.ip_nth point<length [source])%nat).
    { apply nth_error_Some; rewrite NTH; discriminate. }
    cbn in BOUND; lia. }
  rewrite ORDINAL in NTH; cbn in NTH.
  inversion NTH; subst instruction.
  split; [rewrite <- ORDINAL; apply single_point_canonical; assumption|].
  split; [exact PREFIX|]; split; [exact (proj1 BELONG)|exact LENGTH].
Qed.
Lemma single_target_description parameters source items point
  (certificate : single_certificate (length parameters) source items) :
  C.memory_sequence_valid_point parameters (single_target source items) point ->
  exists candidate piece,
    nth_error items (PL.ILSema.ip_nth point)=Some (candidate,piece) /\
    point=A.piece_canonical_point (PL.ILSema.ip_nth point)
      (A.piece_retimed_instruction source candidate piece) (PL.ILSema.ip_index point) /\
    firstn (length parameters) (PL.ILSema.ip_index point)=parameters /\
    in_poly (PL.ILSema.ip_index point) (piece_domain piece)=true /\
    length (PL.ILSema.ip_index point)=length (piece_project piece).
Proof.
  intros [instruction [NTH [PREFIX [BELONG LENGTH]]]].
  unfold single_target in NTH; apply Misc.nth_error_map_inv in NTH.
  destruct NTH as [[candidate piece] [ITEM SAME]]; cbn in SAME; subst instruction.
  destruct (@single_item_at (length parameters) source items (PL.ILSema.ip_nth point)
    candidate piece certificate ITEM) as [DOMAIN ACTION].
  exists candidate,piece; split; [exact ITEM|]; split.
  - apply single_point_canonical; [exact (A.action_candidate_identity ACTION)|exact BELONG].
  - split; [exact PREFIX|]; split.
    + rewrite DOMAIN; exact (proj1 BELONG).
    + rewrite (A.action_candidate_dimension ACTION); exact LENGTH.
Qed.
Lemma single_forward_valid parameters source items point
  (certificate : single_certificate (length parameters) source items) :
  C.memory_sequence_valid_point parameters [source] point ->
  C.memory_sequence_valid_point parameters (single_target source items) (single_forward source items point).
Proof.
  intro VALID; destruct (@single_source_description parameters source point (single_identity certificate) VALID)
    as [CANON [PREFIX [DOMAIN LENGTH]]].
  destruct (@S.piece_selected_instance (length parameters+PL.pi_depth source) (PL.pi_poly source)
    (single_coordinates items) (PL.ILSema.ip_index point) (single_family certificate) LENGTH DOMAIN)
    as [ordinal [piece [FOUND [NTH [INSTANCE UNIQUE]]]]].
  destruct (@single_item_from_coordinate items ordinal piece NTH) as [candidate ITEM].
  destruct (@single_item_at (length parameters) source items ordinal candidate piece certificate ITEM) as [DOMAIN_EQ ACTION].
  destruct INSTANCE as [selected [SELECTED [TARGET_LENGTH [TARGET_DOMAIN INVERSE]]]].
  rewrite NTH in SELECTED; inversion SELECTED; subst selected.
  unfold single_forward; rewrite FOUND,ITEM; unfold C.memory_sequence_valid_point;
    cbn [PL.ILSema.ip_nth PL.ILSema.ip_index A.piece_canonical_point].
  exists (A.piece_retimed_instruction source candidate piece); split.
  - change (nth_error (single_target source items) ordinal=
      Some (A.piece_retimed_instruction source candidate piece)).
    unfold single_target; exact (@Misc.nth_error_map_fwd piece_item PL.PolyInstr
      (fun item=>A.piece_retimed_instruction source (fst item) (snd item))
      ordinal items (candidate,piece) ITEM).
  - split.
    + rewrite <- (@A.action_parameter_prefix (length parameters) source candidate piece ACTION
        (affine_product (piece_project piece) (PL.ILSema.ip_index point)) TARGET_LENGTH TARGET_DOMAIN),INVERSE; exact PREFIX.
    + split.
      * apply A.piece_canonical_belongs; [exact (A.action_candidate_identity ACTION)|].
        cbn [A.piece_retimed_instruction PL.pi_poly]; rewrite <- DOMAIN_EQ; exact TARGET_DOMAIN.
      * cbn [A.piece_retimed_instruction PL.pi_depth]; rewrite <- (A.action_candidate_dimension ACTION); exact TARGET_LENGTH.
Qed.
Lemma single_backward_valid parameters source items point
  (certificate : single_certificate (length parameters) source items) :
  C.memory_sequence_valid_point parameters (single_target source items) point ->
  C.memory_sequence_valid_point parameters [source] (single_backward source items point).
Proof.
  intro VALID; destruct (@single_target_description parameters source items point certificate VALID)
    as [candidate [piece [ITEM [CANON [PREFIX [DOMAIN LENGTH]]]]]].
  destruct (@single_item_at (length parameters) source items (PL.ILSema.ip_nth point)
    candidate piece certificate ITEM) as [DOMAIN_EQ ACTION].
  pose proof (@S.F.family_coordinate_at (length parameters+PL.pi_depth source) (PL.pi_poly source)
    (single_coordinates items) (PL.ILSema.ip_nth point) piece (single_family certificate)
    (@single_coordinate_at items (PL.ILSema.ip_nth point) candidate piece ITEM)) as COORD.
  rewrite (@single_backward_at source items point candidate piece ITEM).
  exists source; split; [reflexivity|]; split.
  - exact (eq_trans (@A.action_parameter_prefix (length parameters) source candidate piece ACTION
      (PL.ILSema.ip_index point) LENGTH DOMAIN) PREFIX).
  - split.
    + apply A.piece_canonical_belongs; [exact (single_identity certificate)|].
      eapply S.F.K.piece_embed_valid; [exact COORD|exact DOMAIN].
    + cbn [A.piece_canonical_point PL.ILSema.ip_index]; unfold affine_product; rewrite map_length;
        exact (A.action_source_dimension ACTION).
Qed.
Lemma single_forward_inverse parameters source items point
  (certificate : single_certificate (length parameters) source items) :
  C.memory_sequence_valid_point parameters [source] point ->
  single_backward source items (single_forward source items point)=point.
Proof.
  intro VALID; destruct (@single_source_description parameters source point (single_identity certificate) VALID)
    as [CANON [PREFIX [DOMAIN LENGTH]]].
  destruct (@S.piece_selected_instance (length parameters+PL.pi_depth source) (PL.pi_poly source)
    (single_coordinates items) (PL.ILSema.ip_index point) (single_family certificate) LENGTH DOMAIN)
    as [ordinal [piece [FOUND [NTH [INSTANCE UNIQUE]]]]].
  destruct (@single_item_from_coordinate items ordinal piece NTH) as [candidate ITEM].
  destruct INSTANCE as [selected [SELECTED [TARGET_LENGTH [TARGET_DOMAIN INVERSE]]]].
  rewrite NTH in SELECTED; inversion SELECTED; subst selected.
  rewrite (@single_forward_at source items point ordinal candidate piece FOUND ITEM).
  rewrite (@single_backward_at source items
    (A.piece_canonical_point ordinal (A.piece_retimed_instruction source candidate piece)
      (affine_product (piece_project piece) (PL.ILSema.ip_index point))) candidate piece ITEM).
  cbn [A.piece_canonical_point PL.ILSema.ip_index]; rewrite INVERSE; symmetry; exact CANON.
Qed.
Lemma single_backward_inverse parameters source items point
  (certificate : single_certificate (length parameters) source items) :
  C.memory_sequence_valid_point parameters (single_target source items) point ->
  single_forward source items (single_backward source items point)=point.
Proof.
  intro VALID; destruct (@single_target_description parameters source items point certificate VALID)
    as [candidate [piece [ITEM [CANON [PREFIX [DOMAIN LENGTH]]]]]].
  destruct (@single_item_at (length parameters) source items (PL.ILSema.ip_nth point)
    candidate piece certificate ITEM) as [DOMAIN_EQ ACTION].
  pose proof (@single_coordinate_at items (PL.ILSema.ip_nth point) candidate piece ITEM) as COORD_NTH.
  pose proof (@S.F.family_coordinate_at (length parameters+PL.pi_depth source) (PL.pi_poly source)
    (single_coordinates items) (PL.ILSema.ip_nth point) piece (single_family certificate) COORD_NTH) as COORD.
  assert (EMBED_LENGTH : length (affine_product (piece_embed piece) (PL.ILSema.ip_index point))=
    (length parameters+PL.pi_depth source)%nat).
  { unfold affine_product; rewrite map_length; exact (A.action_source_dimension ACTION). }
  assert (FOUND : piece_find_image (affine_product (piece_embed piece) (PL.ILSema.ip_index point))
      (single_coordinates items)=Some (PL.ILSema.ip_nth point)).
  { eapply S.piece_selection_recovers; [exact (single_family certificate)|exact EMBED_LENGTH|].
    exists piece; repeat split; try assumption; reflexivity. }
  rewrite (@single_backward_at source items point candidate piece ITEM).
  rewrite (@single_forward_at source items
    (A.piece_canonical_point O source (affine_product (piece_embed piece) (PL.ILSema.ip_index point)))
    (PL.ILSema.ip_nth point) candidate piece FOUND ITEM).
  cbn [A.piece_canonical_point PL.ILSema.ip_index].
  rewrite (@S.F.K.piece_candidate_inverse (length parameters+PL.pi_depth source) (PL.pi_poly source)
    piece COORD (PL.ILSema.ip_index point) LENGTH DOMAIN); symmetry; exact CANON.
Qed.
Lemma single_backward_time parameters source items point
  (certificate : single_certificate (length parameters) source items) :
  C.memory_sequence_valid_point parameters (single_target source items) point ->
  PL.ILSema.ip_time_stamp (single_backward source items point)=PL.ILSema.ip_time_stamp point.
Proof.
  intro VALID; destruct (@single_target_description parameters source items point certificate VALID)
    as [candidate [piece [ITEM [CANON [PREFIX [DOMAIN LENGTH]]]]]].
  destruct (@single_item_at (length parameters) source items (PL.ILSema.ip_nth point)
    candidate piece certificate ITEM) as [DOMAIN_EQ ACTION].
  rewrite (@single_backward_at source items point candidate piece ITEM); cbn [A.piece_canonical_point PL.ILSema.ip_time_stamp].
  rewrite (f_equal PL.ILSema.ip_time_stamp CANON); cbn [A.piece_canonical_point PL.ILSema.ip_time_stamp].
  symmetry; exact (@A.piece_retimed_timestamp (length parameters) source candidate piece
    (PL.ILSema.ip_index point) ACTION).
Qed.
Lemma single_backward_execution parameters source items point initial final
  (certificate : single_certificate (length parameters) source items) :
  C.memory_sequence_valid_point parameters (single_target source items) point ->
  (PL.instr_point_sema (single_backward source items point) initial final <-> PL.instr_point_sema point initial final).
Proof.
  intro VALID; destruct (@single_target_description parameters source items point certificate VALID)
    as [candidate [piece [ITEM [CANON [PREFIX [DOMAIN LENGTH]]]]]].
  destruct (@single_item_at (length parameters) source items (PL.ILSema.ip_nth point)
    candidate piece certificate ITEM) as [DOMAIN_EQ ACTION].
  rewrite (@single_backward_at source items point candidate piece ITEM).
  rewrite CANON at 2.
  apply A.piece_canonical_action_iff with (certificate:=single_retimed_action ACTION); exact DOMAIN.
Qed.
Definition single_isomorphism parameters source items
  (certificate : single_certificate (length parameters) source items) :
  C.memory_point_isomorphism parameters [source] (single_target source items).
Proof.
  refine {| C.point_forward:=single_forward source items; C.point_backward:=single_backward source items |}.
  - intros point VALID; exact (@single_forward_valid parameters source items point certificate VALID).
  - intros point VALID; exact (@single_backward_valid parameters source items point certificate VALID).
  - intros point VALID; exact (@single_forward_inverse parameters source items point certificate VALID).
  - intros point VALID; exact (@single_backward_inverse parameters source items point certificate VALID).
  - intros point VALID.
    pose proof (@single_backward_time parameters source items (single_forward source items point)
      certificate (@single_forward_valid parameters source items point certificate VALID)) as TIME.
    rewrite (@single_forward_inverse parameters source items point certificate VALID) in TIME; symmetry; exact TIME.
  - intros point VALID; exact (@single_backward_time parameters source items point certificate VALID).
  - intros point initial final VALID RUN.
    pose proof (@single_backward_execution parameters source items (single_forward source items point)
      initial final certificate (@single_forward_valid parameters source items point certificate VALID)) as EXEC.
    rewrite (@single_forward_inverse parameters source items point certificate VALID) in EXEC; apply EXEC; exact RUN.
  - intros point initial final VALID RUN; apply (@single_backward_execution parameters source items point initial final certificate VALID); exact RUN.
Defined.
Theorem checked_single_family_execution parameters source items witness context vars initial final :
  length context=length parameters ->
  mayReturn (check_single_family (length parameters) source items witness) true ->
  (PL.poly_instance_list_semantics parameters ([source],context,vars) initial final <->
   PL.poly_instance_list_semantics parameters (single_target source items,context,vars) initial final).
Proof.
  intros LENGTH CHECK; apply C.memory_point_isomorphism_execution; [|exact LENGTH].
  apply single_isomorphism; eapply check_single_family_sound; exact CHECK.
Qed.
End PolCertPieceSingleExecutionFor.
