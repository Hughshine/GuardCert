From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg.
From polcert.polygen Require Import PolIRs.
From Guard Require Import PolCertPieceCoordinates PolCertPieceFamily.
Import ListNotations.
Set Implicit Arguments.

Fixpoint piece_find_image index (pieces : list piece_coordinates) := match pieces with
  | []=>None
  | piece::rest=>if in_poly index (piece_image_domain piece) then Some O
    else option_map S (piece_find_image index rest) end.
Lemma piece_find_image_sound index pieces ordinal : piece_find_image index pieces=Some ordinal ->
  exists piece, nth_error pieces ordinal=Some piece /\ in_poly index (piece_image_domain piece)=true.
Proof.
  revert ordinal; induction pieces as [|piece rest IH]; intro ordinal; cbn; [discriminate|].
  destruct (in_poly index (piece_image_domain piece)) eqn:DOMAIN.
  - intro FOUND; inversion FOUND; exists piece; auto.
  - destruct (piece_find_image index rest) as [selected|] eqn:REST; cbn; [|discriminate].
    intro FOUND; inversion FOUND; destruct (IH selected eq_refl) as [other [NTH OTHER]].
    exists other; cbn; auto.
Qed.
Lemma piece_find_image_complete index pieces :
  (exists piece, In piece pieces /\ in_poly index (piece_image_domain piece)=true) ->
  exists ordinal, piece_find_image index pieces=Some ordinal.
Proof.
  induction pieces as [|piece rest IH]; intros [other [MEMBER DOMAIN]]; [contradiction|].
  cbn; destruct (in_poly index (piece_image_domain piece)) eqn:HEAD; [exists O; reflexivity|].
  destruct MEMBER as [SAME|MEMBER]; [subst other; congruence|].
  destruct (IH ltac:(exists other; auto)) as [ordinal FOUND].
  rewrite FOUND; exists (S ordinal); reflexivity.
Qed.

Module PolCertPieceSelectionFor (IRs : POLIRS).
Module F := PolCertPieceFamilyFor IRs.
Theorem piece_selected_instance source_width source_domain pieces index
  (certificate : F.piece_family_certificate source_width source_domain pieces) :
  length index=source_width -> in_poly index source_domain=true ->
  exists ordinal piece,
    piece_find_image index pieces=Some ordinal /\ nth_error pieces ordinal=Some piece /\
    F.family_instance pieces index ordinal (affine_product (piece_project piece) index) /\
    forall other_id other_index, F.family_instance pieces index other_id other_index ->
      other_id=ordinal /\ other_index=affine_product (piece_project piece) index.
Proof.
  intros LENGTH DOMAIN.
  destruct (@F.family_coverage source_width source_domain pieces certificate index DOMAIN)
    as [image [MEMBER COVER]].
  apply in_map_iff in MEMBER as [piece [<- MEMBER]].
  destruct (@piece_find_image_complete index pieces ltac:(exists piece; auto)) as [ordinal FOUND].
  destruct (@piece_find_image_sound index pieces ordinal FOUND) as [selected [NTH IMAGE]].
  pose proof (@F.family_coordinate_at source_width source_domain pieces ordinal selected certificate NTH) as COORD.
  pose proof (proj1 (@F.K.piece_image_correct source_width source_domain selected index COORD LENGTH) IMAGE)
    as [TARGET INVERSE].
  assert (INSTANCE : F.family_instance pieces index ordinal (affine_product (piece_project selected) index)).
  { exists selected; repeat split; try assumption; unfold affine_product; apply map_length. }
  destruct (@F.family_exactly_one source_width source_domain pieces index certificate LENGTH DOMAIN)
    as [unique_id [unique_index [UNIQUE OTHER]]].
  pose proof (OTHER _ _ INSTANCE) as [ID VALUE].
  exists ordinal,selected; split; [exact FOUND|]; split; [exact NTH|]; split; [exact INSTANCE|].
  intros other_id other_index RELATED; specialize (OTHER _ _ RELATED); congruence.
Qed.
Theorem piece_selection_recovers source_width source_domain pieces index ordinal candidate_index
  (certificate : F.piece_family_certificate source_width source_domain pieces) :
  length index=source_width -> F.family_instance pieces index ordinal candidate_index ->
  piece_find_image index pieces=Some ordinal.
Proof.
  intros LENGTH INSTANCE.
  pose proof (@F.family_instance_valid source_width source_domain pieces index ordinal candidate_index certificate INSTANCE) as DOMAIN.
  destruct (@piece_selected_instance source_width source_domain pieces index certificate LENGTH DOMAIN)
    as [selected [piece [FOUND [NTH [RELATED UNIQUE]]]]].
  destruct (UNIQUE _ _ INSTANCE) as [SAME _]; subst selected; exact FOUND.
Qed.
End PolCertPieceSelectionFor.

Print Assumptions piece_find_image_sound.
Print Assumptions piece_find_image_complete.
