From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg ImpureAlarmConfig.
From polcert.polygen Require Import PolIRs.
From Vpl Require Import Impure.
From Guard Require Import PolCertPieceAffineMaps PolCertPieceDomainCover.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint piece_identity width := match width with
  | O=>[]
  | S rest=>(1::repeat 0 rest,0)::
    map (fun row=>(0::fst row,snd row)) (piece_identity rest) end.
Lemma piece_zero_dot width index : dot_product (repeat 0 width) index=0.
Proof. revert index; induction width; intros [|x xs]; cbn; try reflexivity; rewrite IHwidth; lia. Qed.
Lemma piece_prefix_zero rows x index :
  affine_product (map (fun row=>(0::fst row,snd row)) rows) (x::index)=affine_product rows index.
Proof.
  induction rows as [|[coefficients bias] rows IH]; [reflexivity|].
  change ((dot_product (0::coefficients) (x::index)+bias)::
    affine_product (map (fun row=>(0::fst row,snd row)) rows) (x::index) =
    (dot_product coefficients index+bias)::affine_product rows index).
  rewrite IH; reflexivity.
Qed.
Theorem piece_identity_correct width index :
  length index=width -> affine_product (piece_identity width) index=index.
Proof.
  revert index; induction width; intros [|x xs] LENGTH; cbn in LENGTH; try discriminate; [reflexivity|].
  change ((dot_product (1::repeat 0 width) (x::xs)+0)::
    affine_product (map (fun row=>(0::fst row,snd row)) (piece_identity width)) (x::xs) = x::xs).
  rewrite piece_prefix_zero; cbn [dot_product]; rewrite piece_zero_dot,IHwidth by lia; f_equal; ring.
Qed.

Record piece_coordinates := PieceCoordinates {
  piece_domain : list (list Z*Z);
  piece_embed : list (list Z*Z);
  piece_project : list (list Z*Z)
}.
Definition piece_image_domain piece :=
  piece_pullback_poly (piece_project piece) (piece_domain piece) ++
  piece_equal_maps (matrix_product (piece_embed piece) (piece_project piece))
    (piece_identity (length (piece_embed piece))).

Module PolCertPieceCoordinatesFor (IRs : POLIRS).
Module D := PolCertPieceDomainCoverFor IRs.
Module C := D.C.
Definition check_piece_coordinates source_width source_domain piece :=
  let candidate_width := length (piece_project piece) in
  if Nat.eqb (length (piece_embed piece)) source_width &&
     piece_map_width candidate_width (piece_embed piece) &&
     piece_map_width source_width (piece_project piece)
  then
    BIND contained <- C.memory_check_domain_inclusion (piece_domain piece)
      (piece_pullback_poly (piece_embed piece) source_domain) -;
    if contained then C.memory_check_domain_inclusion (piece_domain piece)
      (piece_equal_maps (matrix_product (piece_project piece) (piece_embed piece))
        (piece_identity candidate_width))
    else pure false
  else pure false.

Record piece_coordinate_certificate source_width source_domain piece := PieceCoordinateCertificate {
  piece_embed_height : length (piece_embed piece)=source_width;
  piece_embed_width : exact_listzzs_cols (length (piece_project piece)) (piece_embed piece);
  piece_project_width : exact_listzzs_cols source_width (piece_project piece);
  piece_embed_valid : forall index, in_poly index (piece_domain piece)=true ->
    in_poly (affine_product (piece_embed piece) index) source_domain=true;
  piece_candidate_inverse : forall index, length index=length (piece_project piece) ->
    in_poly index (piece_domain piece)=true ->
    affine_product (piece_project piece) (affine_product (piece_embed piece) index)=index
}.
Theorem check_piece_coordinates_sound source_width source_domain piece :
  mayReturn (check_piece_coordinates source_width source_domain piece) true ->
  piece_coordinate_certificate source_width source_domain piece.
Proof.
  unfold check_piece_coordinates.
  destruct (Nat.eqb (length (piece_embed piece)) source_width &&
    piece_map_width (length (piece_project piece)) (piece_embed piece) &&
    piece_map_width source_width (piece_project piece)) eqn:SHAPE;
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  apply andb_true_iff in SHAPE as [SHAPE PROJECT]; apply andb_true_iff in SHAPE as [HEIGHT EMBED].
  apply Nat.eqb_eq in HEIGHT; apply piece_map_width_sound in EMBED,PROJECT.
  intro CHECK; bind_imp_destruct CHECK contained CONTAINED; destruct contained;
    [|apply mayReturn_pure in CHECK; discriminate].
  constructor; try assumption.
  - intros index DOMAIN.
    pose proof (@C.memory_check_domain_inclusion_correct (piece_domain piece)
      (piece_pullback_poly (piece_embed piece) source_domain) CONTAINED index DOMAIN) as INCLUDED.
    rewrite (@piece_pullback_poly_correct (piece_embed piece) source_domain index
      (length (piece_project piece)) EMBED) in INCLUDED; exact INCLUDED.
  - intros index LENGTH DOMAIN.
    pose proof (@C.memory_check_domain_inclusion_correct (piece_domain piece)
      (piece_equal_maps (matrix_product (piece_project piece) (piece_embed piece))
        (piece_identity (length (piece_project piece)))) CHECK index DOMAIN) as INVERSE.
    apply piece_equal_maps_correct in INVERSE.
    rewrite (@matrix_product_assoc (piece_project piece) (piece_embed piece) index
      (length (piece_project piece)) EMBED) in INVERSE.
    rewrite piece_identity_correct in INVERSE by exact LENGTH; exact INVERSE.
Qed.

Lemma piece_image_correct source_width source_domain piece index
  (certificate : piece_coordinate_certificate source_width source_domain piece) :
  length index=source_width ->
  in_poly index (piece_image_domain piece)=true <->
  in_poly (affine_product (piece_project piece) index) (piece_domain piece)=true /\
  affine_product (piece_embed piece) (affine_product (piece_project piece) index)=index.
Proof.
  intro LENGTH; unfold piece_image_domain; rewrite in_poly_app,andb_true_iff.
  rewrite (@piece_pullback_poly_correct (piece_project piece) (piece_domain piece) index
    source_width (piece_project_width certificate)),piece_equal_maps_correct.
  rewrite (@matrix_product_assoc (piece_embed piece) (piece_project piece) index
    source_width (piece_project_width certificate)).
  rewrite piece_identity_correct by
    (rewrite (@piece_embed_height source_width source_domain piece certificate); exact LENGTH); reflexivity.
Qed.
Lemma piece_candidate_image source_width source_domain piece index
  (certificate : piece_coordinate_certificate source_width source_domain piece) :
  length index=length (piece_project piece) -> in_poly index (piece_domain piece)=true ->
  in_poly (affine_product (piece_embed piece) index) (piece_image_domain piece)=true.
Proof.
  intros LENGTH DOMAIN; apply (@piece_image_correct source_width source_domain piece
    (affine_product (piece_embed piece) index) certificate).
  - unfold affine_product; rewrite map_length; exact (@piece_embed_height source_width source_domain piece certificate).
  - rewrite (@piece_candidate_inverse source_width source_domain piece certificate index LENGTH DOMAIN).
    split; [exact DOMAIN|reflexivity].
Qed.

Fixpoint check_coordinate_family source_width source_domain pieces := match pieces with
  | []=>pure true
  | piece::rest=>BIND accepted <- check_piece_coordinates source_width source_domain piece -;
    if accepted then check_coordinate_family source_width source_domain rest else pure false end.
Theorem check_coordinate_family_sound source_width source_domain pieces :
  mayReturn (check_coordinate_family source_width source_domain pieces) true ->
  Forall (piece_coordinate_certificate source_width source_domain) pieces.
Proof.
  induction pieces as [|piece rest IH]; cbn; intro CHECK; [constructor|].
  bind_imp_destruct CHECK accepted ACCEPT; destruct accepted;
    [|apply mayReturn_pure in CHECK; discriminate].
  constructor; [apply check_piece_coordinates_sound; exact ACCEPT|apply IH; exact CHECK].
Qed.
End PolCertPieceCoordinatesFor.

Print Assumptions piece_identity_correct.
