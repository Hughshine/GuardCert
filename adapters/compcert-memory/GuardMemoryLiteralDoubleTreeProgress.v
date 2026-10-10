From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightRegionProgress ClightFragmentProgress ClightSequenceProgress.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleSourceInstruction GuardMemoryDoubleAssignmentFactory
  GuardMemoryLongControl GuardMemoryLongProgressControl GuardMemoryLongLoopControl
  GuardMemoryLongLoadedProgress GuardMemoryLongRangeSource GuardMemoryLiteralDoubleTreeData GuardMemoryLiteralDoubleTreeSyntax GuardMemoryDoubleSourceTreeData GuardMemoryDoubleSourceTreeProgress GuardMemorySignedBoundRangeProgress GuardMemorySignedBoundLoadedProgress.
Import ListNotations.
Set Implicit Arguments.

(** This source protocol is independent of accepted bounds, mathematical point
    validity, and header stability. It also permits a stuck source execution. *)
Theorem literal_double_source_tree_framed_progress p controls tree :
  literal_double_source_tree_checked p controls tree ->
  forall protected, incl protected controls -> framed_progress (literal_double_source_tree_code tree) protected.
Proof.
  revert controls; induction tree; intros controls CHECK protected INCLUDED; cbn [literal_double_source_tree_code].
  - apply finite_framed_progress; reflexivity.
  - change (checked_double_source_instruction p controls body=Some instruction) in CHECK.
    destruct body; cbn [checked_double_source_instruction decode_double_assignment] in CHECK; try discriminate;
      apply finite_framed_progress; reflexivity.
  - destruct CHECK as [FIRST SECOND]; apply sequence_framed_progress;
      [apply IHtree1 with (controls:=controls)|apply IHtree2 with (controls:=controls)]; assumption.
  - destruct CHECK as [FRESH [DECODE [RANGE CHILD]]].
    assert (SAFE : ~ In iterator protected) by (intro MEMBER; apply FRESH,INCLUDED; exact MEMBER).
    assert (BODY : framed_progress (literal_double_source_tree_code tree) (iterator::protected)).
    { apply IHtree with (controls:=controls++[iterator]); [exact CHILD|].
      intros identifier [SAME|MEMBER]; apply in_or_app;
        [right; subst identifier; cbn; auto|left; apply INCLUDED; exact MEMBER]. }
    destruct raw.
    + apply signed_bound_raw_from_framed_progress; [eapply literal_double_bound_type; exact DECODE|exact SAFE|exact BODY].
    + apply signed_bound_from_framed_progress; [eapply literal_double_bound_type; exact DECODE|exact SAFE|exact BODY].
Defined.

Definition literal_double_source_tree_active_root tree := match tree with
  | LiteralDoubleSequence _ _ | LiteralDoubleRange _ _ _ _ _ _=>true | _=>false end.
Theorem literal_double_source_tree_region_progress p controls tree :
  literal_double_source_tree_checked p controls tree -> literal_double_source_tree_active_root tree=true ->
  region_progress (literal_double_source_tree_code tree).
Proof.
  intros CHECK ACTIVE; destruct tree; try discriminate; cbn [literal_double_source_tree_code].
  - destruct CHECK as [FIRST SECOND]; apply sequence_region_progress with (protected:=controls);
      apply literal_double_source_tree_framed_progress with (p:=p) (controls:=controls);
      [exact FIRST|apply incl_refl|exact SECOND|apply incl_refl].
  - destruct CHECK as [FRESH [DECODE [RANGE CHILD]]].
    assert (BODY : framed_progress (literal_double_source_tree_code tree) (iterator::controls)).
    { apply literal_double_source_tree_framed_progress with (p:=p) (controls:=controls++[iterator]); [exact CHILD|].
      intros identifier [SAME|MEMBER]; apply in_or_app;
        [right; subst identifier; cbn; auto|left; exact MEMBER]. }
    destruct raw.
    + apply signed_bound_raw_from_region_progress with (protected:=controls); [eapply literal_double_bound_type; exact DECODE|exact FRESH|exact BODY].
    + apply signed_bound_from_region_progress with (protected:=controls);
        [eapply literal_double_bound_type; exact DECODE|exact FRESH|exact BODY].
Defined.

Print Assumptions literal_double_source_tree_framed_progress.
Print Assumptions literal_double_source_tree_region_progress.
