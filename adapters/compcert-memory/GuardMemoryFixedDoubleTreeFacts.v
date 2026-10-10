From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightGlobalScope ClightRegionProgress.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleSourceInstruction
  GuardMemoryDoubleSourceTransport GuardMemoryDoubleSourceResolvedPoints GuardMemoryDoubleInitializedReductionSource
  GuardMemoryDoubleSourceTreeData GuardMemoryDoubleSourceTreeState GuardMemoryDoubleTreeFootprint
  GuardMemoryDoubleAffineBoxBounds GuardMemoryLongExpressionCapture
  GuardMemoryFixedDoubleTreeData GuardMemoryFixedDoubleTreeDecode GuardMemoryFixedDoubleTreeSource.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem fixed_double_tree_header_ranges p controls tree :
  fixed_double_source_tree_checked p controls tree ->
  forall header, In header (double_source_tree_headers (fixed_double_tree_skeleton tree)) ->
    Int.min_signed<=fixed_double_parameter_value header<=Int.max_signed.
Proof.
  revert controls; induction tree; intros controls CHECK header MEMBER;
    cbn [fixed_double_tree_skeleton double_source_tree_headers] in MEMBER; try contradiction.
  - destruct CHECK as [FIRST SECOND]; apply in_app_or in MEMBER as [MEMBER|MEMBER];
      [eapply IHtree1|eapply IHtree2]; eassumption.
  - destruct CHECK as [FRESH [DECODE [RANGE CHILD]]]; destruct MEMBER as [SAME|MEMBER].
    + subst header.
      change (Int.min_signed<=fixed_double_parameter_value
        (fixed_double_parameter_name upper)<=Int.max_signed).
      rewrite fixed_double_parameter_roundtrip; exact RANGE.
    + eapply IHtree; eassumption.
Qed.
Theorem checked_fixed_double_tree_shared_layout p source tree :
  checked_fixed_double_source_tree p source=Some tree ->
  double_source_tree_shared_layout (fixed_double_tree_skeleton tree)
    (double_source_tree_layouts (fixed_double_tree_skeleton tree)).
Proof.
  intros CHECK instruction POINT access MEMBER.
  destruct (@checked_fixed_double_source_tree_sound p source tree CHECK) as [_ [_ LAYOUT]].
  unfold double_source_tree_layout_check in LAYOUT.
  apply (@double_source_layout_check_sound (double_source_tree_layouts (fixed_double_tree_skeleton tree))
    (double_source_tree_accesses (fixed_double_tree_skeleton tree)) LAYOUT access).
  unfold double_source_tree_accesses; apply in_flat_map; exists instruction; auto.
Qed.

Definition fixed_double_tree_footprint_check tree box :=
  double_tree_footprint_check (fixed_double_tree_skeleton tree) fixed_double_parameter_value box.
Theorem fixed_double_tree_footprint_model_facts tree : forall p controls values ge locals layouts box,
  fixed_double_source_tree_checked p controls tree ->
  double_source_tree_shared_layout (fixed_double_tree_skeleton tree) layouts ->
  preserving_globals (globalenv p) ge -> double_source_tree_scope (fixed_double_tree_skeleton tree) locals ->
  fixed_double_tree_footprint_check tree box=true ->
  double_affine_box_contains box (map values controls) ->
  fixed_double_tree_facts tree controls values ge layouts.
Proof.
  induction tree; intros p controls values ge locals layouts box CHECK LAYOUT GLOBAL SCOPE FOOTPRINT BOX.
  - exact I.
  - eapply checked_double_source_instruction_resolved_from_bounds.
    + exact CHECK.
    + apply LAYOUT; left; reflexivity.
    + exact GLOBAL.
    + apply SCOPE; left; reflexivity.
    + eapply double_affine_box_instruction_check_sound;
        [exact FOOTPRINT|exact BOX].
  - destruct CHECK as [FIRST SECOND].
    unfold fixed_double_tree_footprint_check in FOOTPRINT;
      cbn [fixed_double_tree_skeleton double_tree_footprint_check] in FOOTPRINT.
    apply andb_true_iff in FOOTPRINT as [FOOTPRINT1 FOOTPRINT2].
    split; [eapply IHtree1|eapply IHtree2]; try eassumption.
    + intros instruction MEMBER; apply LAYOUT,in_or_app; left; exact MEMBER.
    + intros instruction MEMBER; apply SCOPE,in_or_app; left; exact MEMBER.
    + intros instruction MEMBER; apply LAYOUT,in_or_app; right; exact MEMBER.
    + intros instruction MEMBER; apply SCOPE,in_or_app; right; exact MEMBER.
  - destruct CHECK as [FRESH [DECODE [RANGE CHILD]]].
    unfold fixed_double_tree_facts; cbn [fixed_double_tree_skeleton double_source_tree_model_facts].
    rewrite fixed_double_skeleton_bound; split; [apply memory_i32_range_is_i64; exact RANGE|intros value VALUE].
    assert (ACTIVE : (Int.signed start <? upper)=true) by (apply Z.ltb_lt; lia).
    unfold fixed_double_tree_footprint_check in FOOTPRINT;
      cbn [fixed_double_tree_skeleton double_tree_footprint_check] in FOOTPRINT.
    rewrite fixed_double_skeleton_bound,ACTIVE in FOOTPRINT.
    eapply IHtree; [exact CHILD|exact LAYOUT|exact GLOBAL|exact SCOPE|exact FOOTPRINT|].
    apply double_tree_child_box; [exact FRESH|exact BOX|exact VALUE].
Qed.

Print Assumptions fixed_double_tree_header_ranges.
Print Assumptions checked_fixed_double_tree_shared_layout.
Print Assumptions fixed_double_tree_footprint_model_facts.
