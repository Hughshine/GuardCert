From Stdlib Require Import List.
From compcert.lib Require Import Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestProbe.
Import ListNotations.
Set Implicit Arguments.

Theorem affine_first_probe_writes nest : forall rename result allowed,
  In result allowed ->
  (forall identifier, In identifier(affine_nest_controls nest) -> In (rename identifier) allowed) ->
  writes_only allowed(affine_first_probe nest rename result).
Proof.
  induction nest as [leaf|iterator bound expression body child IH]; intros rename result allowed RESULT CONTROLS.
  - constructor; exact RESULT.
  - cbn [affine_first_probe]; constructor; [|constructor; exact RESULT].
    assert (CHILD:forall identifier, In identifier(affine_nest_controls child) -> In(rename identifier) allowed).
    { intros identifier MEMBER; apply CONTROLS; cbn [affine_nest_controls List.In]; auto. }
    destruct child as [source|child_iterator child_bound child_expression child_body grandchild].
    + apply IH; [exact RESULT|exact CHILD].
    + constructor.
      * constructor; apply CHILD; cbn [affine_nest_controls List.In]; auto.
      * constructor.
        -- constructor; apply CHILD; cbn [affine_nest_controls List.In]; auto.
        -- apply IH; [exact RESULT|exact CHILD].
Qed.

Theorem affine_first_probe_public_frame nest fe ge locals rename result protected temps memory after final :
  ~In result protected ->
  (forall identifier, In identifier(affine_nest_controls nest) -> ~In(rename identifier) protected) ->
  exec_stmt fe ge locals temps memory(affine_first_probe nest rename result) E0 after final Out_normal ->
  temp_agree protected temps after.
Proof.
  intros RESULT PRIVATE RUN.
  eapply structured_temp_frame with(allowed:=map rename(affine_nest_controls nest)++[result]); [| |exact RUN].
  - apply affine_first_probe_writes; [apply in_or_app; right; cbn; auto|].
    intros identifier MEMBER; apply in_or_app; left; apply in_map; exact MEMBER.
  - intros identifier MEMBER BAD; apply in_app_or in BAD; destruct BAD as [BAD|BAD].
    + apply in_map_iff in BAD as [source [<- SOURCE]]; exact(PRIVATE source SOURCE MEMBER).
    + cbn in BAD; destruct BAD as [SAME|BAD]; [subst; contradiction|contradiction].
Qed.
Print Assumptions affine_first_probe_writes.
Print Assumptions affine_first_probe_public_frame.
