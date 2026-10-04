From Stdlib Require Import List Bool.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightLoopSyntax ClightRegionProgress ClightFrontendLoopProtocol
  ClightRectangularLoops ClightStraightLine ClightTempFrame.
From GuardMemory Require Import GuardMemoryTripleSource.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit.
Import ListNotations.
Set Implicit Arguments.

Theorem affine_nest_source_quiet nest :
  affine_nest_shapes nest -> quiet_statement (affine_nest_leaf nest)=true ->
  quiet_statement (affine_nest_source nest)=true.
Proof.
  induction nest as [code|iterator bound expression body child IH];
    cbn [affine_nest_shapes affine_nest_leaf]; intros SHAPES QUIET; [exact QUIET|].
  change (quiet_statement (frontend_counted_loop iterator bound body)=true).
  apply memory_frontend_loop_quiet; destruct SHAPES as [SHAPE SHAPES]; specialize (IH SHAPES QUIET).
  destruct child; cbn [affine_nest_child_shape affine_nest_child_prefix] in SHAPE; [subst; exact IH|].
  apply flatten_quiet_certificate; rewrite SHAPE; cbn [app].
  constructor; [reflexivity|constructor; [reflexivity|constructor; [exact IH|constructor]]].
Qed.

Theorem affine_nest_source_writes nest :
  affine_nest_shapes nest -> writes_only [] (affine_nest_leaf nest) ->
  writes_only (affine_nest_controls nest) (affine_nest_source nest).
Proof.
  induction nest as [code|iterator bound expression body child IH];
    cbn [affine_nest_shapes affine_nest_leaf]; intros SHAPES WRITES; [exact WRITES|].
  change (writes_only (iterator::bound::affine_nest_controls child) (frontend_counted_loop iterator bound body)).
  apply memory_frontend_loop_writes; [cbn; auto|].
  destruct SHAPES as [SHAPE SHAPES]; specialize (IH SHAPES WRITES).
  assert (BODY:writes_only (affine_nest_controls child) body).
  { destruct child; cbn [affine_nest_child_shape affine_nest_child_prefix] in SHAPE; [subst; exact IH|].
    apply flatten_writes_certificate; rewrite SHAPE; cbn [app].
    constructor; [constructor; cbn; auto|constructor; [unfold rectangle_reset; constructor; cbn; auto|constructor; [exact IH|constructor]]]. }
  eapply writes_only_weaken; [|exact BODY]; cbn; auto.
Qed.

Theorem affine_nest_body_writes iterator bound expression body child :
  affine_nest_shapes (AffineSourceAxis iterator bound expression body child) ->
  writes_only [] (affine_nest_leaf child) -> writes_only (affine_nest_controls child) body.
Proof.
  cbn [affine_nest_shapes]; intros [SHAPE SHAPES] WRITES.
  pose proof (@affine_nest_source_writes child SHAPES WRITES) as SOURCE.
  destruct child; cbn [affine_nest_child_shape affine_nest_child_prefix] in SHAPE; [subst; exact SOURCE|].
  apply flatten_writes_certificate; rewrite SHAPE; cbn [app].
  constructor; [constructor; cbn; auto|constructor; [unfold rectangle_reset; constructor; cbn; auto|constructor; [exact SOURCE|constructor]]].
Qed.

Theorem affine_nest_body_normal iterator bound expression body child :
  affine_nest_shapes (AffineSourceAxis iterator bound expression body child) ->
  normal_statement (affine_nest_leaf child)=true -> quiet_statement (affine_nest_leaf child)=true ->
  normal_statement body=true.
Proof.
  cbn [affine_nest_shapes]; intros [SHAPE SHAPES] NORMAL QUIET.
  pose proof (@affine_nest_source_quiet child SHAPES QUIET) as SOURCE.
  destruct child; cbn [affine_nest_child_shape affine_nest_child_prefix] in SHAPE; [subst; exact NORMAL|].
  apply flatten_normal_certificate; rewrite SHAPE; cbn [app].
  constructor; [reflexivity|constructor; [reflexivity|constructor; [exact SOURCE|constructor]]].
Qed.
Print Assumptions affine_nest_source_quiet.
Print Assumptions affine_nest_source_writes.
Print Assumptions affine_nest_body_writes.
Print Assumptions affine_nest_body_normal.
