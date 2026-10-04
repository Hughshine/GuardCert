From Stdlib Require Import List.
From compcert.lib Require Import Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestProbe AffineNestProbeFrame AffineNestProbeInitialize.
Import ListNotations.
Set Implicit Arguments.

Theorem affine_initialized_probe_writes iterator bound expression body child rename result allowed :
  In result allowed ->
  (forall identifier, In identifier(affine_nest_controls(AffineSourceAxis iterator bound expression body child)) ->
    In(rename identifier) allowed) ->
  writes_only allowed(Ssequence(affine_root_probe_initialize iterator bound rename)
    (affine_first_probe(AffineSourceAxis iterator bound expression body child) rename result)).
Proof.
  intros RESULT CONTROLS; constructor.
  - unfold affine_root_probe_initialize; constructor; constructor; apply CONTROLS;
      cbn [affine_nest_controls List.In]; auto.
  - apply affine_first_probe_writes; assumption.
Qed.

Theorem affine_initialized_probe_public_frame iterator bound expression body child fe ge locals rename result protected temps memory after final :
  ~In result protected ->
  (forall identifier, In identifier(affine_nest_controls(AffineSourceAxis iterator bound expression body child)) ->
    ~In(rename identifier) protected) ->
  exec_stmt fe ge locals temps memory
    (Ssequence(affine_root_probe_initialize iterator bound rename)
      (affine_first_probe(AffineSourceAxis iterator bound expression body child) rename result)) E0 after final Out_normal ->
  temp_agree protected temps after.
Proof.
  intros RESULT PRIVATE RUN.
  eapply structured_temp_frame with(allowed:=map rename(affine_nest_controls(AffineSourceAxis iterator bound expression body child))++[result]);
    [| |exact RUN].
  - apply affine_initialized_probe_writes; [apply in_or_app; right; cbn; auto|].
    intros identifier MEMBER; apply in_or_app; left; apply in_map; exact MEMBER.
  - intros identifier MEMBER BAD; apply in_app_or in BAD; destruct BAD as [BAD|BAD].
    + apply in_map_iff in BAD as [source [<- SOURCE]]; exact(PRIVATE source SOURCE MEMBER).
    + cbn in BAD; destruct BAD as [SAME|BAD]; [subst; contradiction|contradiction].
Qed.
Print Assumptions affine_initialized_probe_writes.
Print Assumptions affine_initialized_probe_public_frame.
