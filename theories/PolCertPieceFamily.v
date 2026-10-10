From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg ImpureAlarmConfig.
From polcert.polygen Require Import PolIRs.
From Vpl Require Import Impure.
From Guard Require Import PolCertPieceAffineMaps PolCertPieceDomainCover PolCertPieceCoordinates.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** One source-domain instance has exactly one candidate-domain instance.
    Instruction, parameter-prefix, schedule and Loop bridges are additional
    obligations; this certificate cannot authorize a program replacement. *)
Module PolCertPieceFamilyFor (IRs : POLIRS).
Module K := PolCertPieceCoordinatesFor IRs.
Module D := K.D.
Definition check_piece_family source_width source_domain pieces witness :=
  BIND coordinates <- K.check_coordinate_family source_width source_domain pieces -;
  if coordinates then
    BIND covered <- D.check_cover source_domain (map piece_image_domain pieces) witness -;
    if covered then D.check_disjoint_family (map piece_image_domain pieces) else pure false
  else pure false.
Record piece_family_certificate source_width source_domain pieces := PieceFamilyCertificate {
  family_coordinates : Forall (K.piece_coordinate_certificate source_width source_domain) pieces;
  family_coverage : forall index, in_poly index source_domain=true ->
    exists domain, In domain (map piece_image_domain pieces) /\ in_poly index domain=true;
  family_disjoint : forall first second i j,
    nth_error (map piece_image_domain pieces) i=Some first ->
    nth_error (map piece_image_domain pieces) j=Some second -> i<>j -> D.disjoint first second
}.
Theorem check_piece_family_sound source_width source_domain pieces witness :
  mayReturn (check_piece_family source_width source_domain pieces witness) true ->
  piece_family_certificate source_width source_domain pieces.
Proof.
  unfold check_piece_family; intro CHECK; bind_imp_destruct CHECK coordinates COORDINATES.
  destruct coordinates; [|apply mayReturn_pure in CHECK; discriminate].
  bind_imp_destruct CHECK covered COVERED; destruct covered;
    [|apply mayReturn_pure in CHECK; discriminate].
  constructor.
  - apply K.check_coordinate_family_sound; exact COORDINATES.
  - eapply D.check_cover_sound; exact COVERED.
  - eapply D.check_disjoint_family_sound; exact CHECK.
Qed.
Definition family_instance pieces source_index piece_id candidate_index :=
  exists piece, nth_error pieces piece_id=Some piece /\
    length candidate_index=length (piece_project piece) /\
    in_poly candidate_index (piece_domain piece)=true /\
    affine_product (piece_embed piece) candidate_index=source_index.
Lemma family_coordinate_at source_width source_domain pieces piece_id piece
  (certificate : piece_family_certificate source_width source_domain pieces) :
  nth_error pieces piece_id=Some piece -> K.piece_coordinate_certificate source_width source_domain piece.
Proof.
  intro NTH; pose proof (family_coordinates certificate) as ALL.
  apply Forall_forall with (x:=piece) in ALL;
    [exact ALL|eapply nth_error_In; exact NTH].
Qed.
Theorem family_instance_valid source_width source_domain pieces source_index piece_id candidate_index
  (certificate : piece_family_certificate source_width source_domain pieces) :
  family_instance pieces source_index piece_id candidate_index -> in_poly source_index source_domain=true.
Proof.
  intros [piece [NTH [LENGTH [DOMAIN EMBED]]]]; subst source_index.
  pose proof (@family_coordinate_at source_width source_domain pieces piece_id piece certificate NTH) as COORD.
  eapply K.piece_embed_valid; [exact COORD|exact DOMAIN].
Qed.
Theorem family_exactly_one source_width source_domain pieces source_index
  (certificate : piece_family_certificate source_width source_domain pieces) :
  length source_index=source_width -> in_poly source_index source_domain=true ->
  exists piece_id candidate_index,
    family_instance pieces source_index piece_id candidate_index /\
    forall other_id other_index, family_instance pieces source_index other_id other_index ->
      other_id=piece_id /\ other_index=candidate_index.
Proof.
  intros LENGTH SOURCE.
  destruct (@family_coverage source_width source_domain pieces certificate source_index SOURCE)
    as [domain [MEMBER DOMAIN]].
  apply in_map_iff in MEMBER as [piece [<- MEMBER]].
  apply In_nth_error in MEMBER as [piece_id NTH].
  pose proof (@family_coordinate_at source_width source_domain pieces piece_id piece certificate NTH) as COORD.
  pose proof (proj1 (@K.piece_image_correct source_width source_domain piece source_index COORD LENGTH) DOMAIN)
    as [CANDIDATE INVERSE].
  exists piece_id,(affine_product (piece_project piece) source_index); split.
  - exists piece; repeat split; try assumption; unfold affine_product; apply map_length.
  - intros other_id other_index [other [OTHER [OTHER_LENGTH [OTHER_DOMAIN OTHER_EMBED]]]].
    pose proof (@family_coordinate_at source_width source_domain pieces other_id other certificate OTHER) as OTHER_COORD.
    assert (OTHER_IMAGE : in_poly source_index (piece_image_domain other)=true).
    { rewrite <- OTHER_EMBED; eapply K.piece_candidate_image; eassumption. }
    assert (IDS : other_id=piece_id).
    { destruct (Nat.eq_dec other_id piece_id) as [SAME|DIFFERENT]; [exact SAME|].
      assert (PIECE_NTH : nth_error (map piece_image_domain pieces) piece_id=Some (piece_image_domain piece)).
      { rewrite nth_error_map,NTH; reflexivity. }
      assert (OTHER_NTH : nth_error (map piece_image_domain pieces) other_id=Some (piece_image_domain other)).
      { rewrite nth_error_map,OTHER; reflexivity. }
      pose proof (@family_disjoint source_width source_domain pieces certificate
        (piece_image_domain piece) (piece_image_domain other) piece_id other_id
        PIECE_NTH OTHER_NTH ltac:(congruence) source_index DOMAIN) as APART.
      congruence. }
    split; [exact IDS|].
    subst other_id; rewrite NTH in OTHER; inversion OTHER; subst other.
    rewrite <- (@K.piece_candidate_inverse source_width source_domain piece COORD
      other_index OTHER_LENGTH OTHER_DOMAIN) at 1.
    rewrite OTHER_EMBED; reflexivity.
Qed.
End PolCertPieceFamilyFor.
