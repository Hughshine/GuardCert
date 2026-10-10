From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGlobalScope ClightRegionProgress.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceTransport
  GuardMemoryDoubleSourceResolvedPoints GuardMemoryDoubleInitializedReductionSource
  GuardMemoryDoubleSourceTreeData GuardMemoryDoubleSourceTreeState GuardMemoryDoubleTreeCaptureFacts
  GuardMemoryDoubleTreeProfileBounds GuardMemoryDoubleAffineBoxBounds.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The untrusted profile is checked over the original entire tree. It bounds
    each active source coordinate, preserving signed starts and shared headers;
    a statically empty envelope needs no child-footprint check. *)
Fixpoint double_tree_footprint_check tree upper box := match tree with
  | DoubleTreeSkip=>true
  | DoubleTreePoint _ instruction=>double_affine_box_instruction_check box instruction
  | DoubleTreeSequence first second=>double_tree_footprint_check first upper box&&double_tree_footprint_check second upper box
  | DoubleTreeRange _ _ start bound child=>
      if Int.signed start <? double_tree_bound_value upper bound
      then double_tree_footprint_check child upper (box++[(Int.signed start,double_tree_bound_value upper bound)]) else true
  end.
Lemma double_tree_child_box controls control_values iterator value box lower upper :
  ~ In iterator controls -> double_affine_box_contains box (map control_values controls) -> lower<=value<upper ->
  double_affine_box_contains (box++[(lower,upper)])
    (map (double_source_control_value control_values iterator value) (controls++[iterator])).
Proof.
  intros FRESH BOX RANGE; unfold double_affine_box_contains in *.
  assert (VALUES : map (double_source_control_value control_values iterator value) (controls++[iterator])=
    map control_values controls++[value]).
  { exact (@GuardMemoryDoubleInitializedReductionSource.double_source_control_values controls control_values iterator value FRESH). }
  rewrite VALUES.
  apply Forall2_app; [exact BOX|constructor; [exact RANGE|constructor]].
Qed.
Theorem double_tree_footprint_model_facts tree :
  forall p controls valuation control_values ge locals layouts upper box,
  double_source_tree_checked p controls tree -> double_source_tree_shared_layout tree layouts ->
  preserving_globals (globalenv p) ge -> double_source_tree_scope tree locals ->
  double_tree_footprint_check tree upper box=true -> double_affine_box_contains box (map control_values controls) ->
  (forall header, In header (double_source_tree_active_headers valuation tree) -> valuation header<=upper header) ->
  double_tree_capture_range_facts tree valuation ->
  double_source_tree_model_facts tree controls valuation control_values ge layouts.
Proof.
  induction tree; intros p controls valuation control_values ge locals layouts upper box
    CHECK LAYOUT GLOBAL SCOPE FOOTPRINT BOX PROFILE RANGES; [exact I| | |].
  - cbn [double_source_tree_model_facts]; eapply checked_double_source_instruction_resolved_from_bounds.
    + exact CHECK.
    + apply LAYOUT; cbn; left; reflexivity.
    + exact GLOBAL.
    + apply SCOPE; cbn; left; reflexivity.
    + eapply double_affine_box_instruction_check_sound; eassumption.
  - destruct CHECK as [FIRST SECOND]; apply andb_true_iff in FOOTPRINT as [FOOTPRINT1 FOOTPRINT2].
    destruct RANGES as [RANGE1 RANGE2]; split; [eapply IHtree1|eapply IHtree2]; try eassumption.
    + intros instruction MEMBER; apply LAYOUT; cbn; apply in_or_app; left; exact MEMBER.
    + intros instruction MEMBER; apply SCOPE; cbn; apply in_or_app; left; exact MEMBER.
    + intros header MEMBER; apply PROFILE; cbn; apply in_or_app; left; exact MEMBER.
    + intros instruction MEMBER; apply LAYOUT; cbn; apply in_or_app; right; exact MEMBER.
    + intros instruction MEMBER; apply SCOPE; cbn; apply in_or_app; right; exact MEMBER.
    + intros header MEMBER; apply PROFILE; cbn; apply in_or_app; right; exact MEMBER.
  - destruct CHECK as [FRESH [DECL CHILD]]; destruct RANGES as [RANGE CHILD_RANGES].
    cbn [double_source_tree_model_facts]; split; [exact RANGE|intros value VALUE].
    assert (BOUND : double_tree_bound_value valuation bound<=double_tree_bound_value upper bound).
    { unfold double_tree_bound_value; pose proof (PROFILE _ (or_introl eq_refl)); lia. }
    assert (ACTIVE : (Int.signed start <? double_tree_bound_value valuation bound)=true) by (apply Z.ltb_lt; lia).
    assert (ENVELOPE : (Int.signed start <? double_tree_bound_value upper bound)=true) by (apply Z.ltb_lt; lia).
    cbn [double_tree_footprint_check] in FOOTPRINT; rewrite ENVELOPE in FOOTPRINT.
    rewrite ACTIVE in CHILD_RANGES.
    eapply IHtree; [exact CHILD|exact LAYOUT|exact GLOBAL|exact SCOPE|exact FOOTPRINT| | |exact CHILD_RANGES].
    + apply double_tree_child_box; [exact FRESH|exact BOX|lia].
    + intros header MEMBER; apply PROFILE; cbn; rewrite ACTIVE; right; exact MEMBER.
Qed.

Print Assumptions double_tree_child_box.
Print Assumptions double_tree_footprint_model_facts.
