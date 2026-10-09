From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGlobalScope ClightTempFootprint ClightRegionProgress.
From GuardInterface Require Import ClightCheckPlanFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryValueInstr GuardMemoryDoubleLocations GuardMemoryDoubleProgramBindings
  GuardMemoryDynamicTensorLayout GuardMemoryDoubleTensorBackend GuardMemoryDoubleSourceInstruction
  GuardMemoryDoubleSourceTransport GuardMemoryDoubleSourceResolvedPoints GuardMemoryDoubleAffineSourceAccess
  GuardMemoryDoubleInitializedNestSource GuardMemoryDoubleInitializedRawNest GuardMemoryDoubleReductionNestSource GuardMemoryLongControl
  GuardMemoryLongRawLoadedProgress GuardMemoryLongProgressControl GuardMemoryDoublePipelineTransport GuardMemoryDoublePolyhedral
  GuardMemoryDoubleRectangularNestData GuardMemoryDoubleRectangularNestModel
  GuardMemoryDoubleRectangularNestSource GuardMemoryDoubleRectangularNestDecoder GuardMemoryDoubleRectangularBounds.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition double_rectangular_globals description := map snd (rectangular_nest_axes description)++
  double_source_instruction_globals (rectangular_nest_instruction description).
Definition double_rectangular_public_globals description := map snd (rectangular_nest_axes description)++
  map fst (PTree.elements (double_source_instruction_layouts (rectangular_nest_instruction description))).
Definition double_rectangular_layout_span_check description := forallb
  (fun entry => 8*tensor_volume (snd entry)<=?Ptrofs.modulus)
  (PTree.elements (double_source_instruction_layouts (rectangular_nest_instruction description))).
Theorem double_rectangular_layout_span_check_sound description ge locals :
  double_rectangular_layout_span_check description=true ->
  locals_avoid (double_rectangular_public_globals description) locals ->
  double_tensor_static ge locals (double_source_instruction_layouts (rectangular_nest_instruction description)).
Proof.
  intros CHECK LOCAL identifier dimensions LAYOUT.
  pose proof (@PTree.elements_correct (list Z) _ identifier dimensions LAYOUT) as MEMBER; split.
  - apply LOCAL; unfold double_rectangular_public_globals; apply in_or_app; right.
    apply in_map_iff; exists (identifier,dimensions); split; [reflexivity|exact MEMBER].
  - unfold double_rectangular_layout_span_check in CHECK.
    apply forallb_forall with (x:=(identifier,dimensions)) in CHECK; [|exact MEMBER].
    cbn [snd] in CHECK; apply Z.leb_le; exact CHECK.
Qed.
Theorem checked_double_rectangular_public_scope p controls source description locals :
  checked_double_rectangular_raw_nest p controls source=Some description ->
  locals_avoid (double_rectangular_public_globals description) locals ->
  locals_avoid (double_rectangular_globals description) locals.
Proof.
  intros CHECK LOCAL.
  destruct (@checked_double_rectangular_raw_nest_sound p controls source description CHECK) as [_ [CANONICAL _]].
  destruct (@checked_double_rectangular_nest_sound p controls _ description CANONICAL) as [_ [LEAF _]].
  destruct (@checked_double_source_instruction_sound p _ _ _ LEAF) as [_ [_ [_ REGISTRY]]].
  pose proof (@double_source_layout_check_sound _ _ REGISTRY) as LAYOUT.
  intros identifier MEMBER; unfold double_rectangular_globals in MEMBER; apply in_app_or in MEMBER as [HEADER|MEMBER].
  - apply LOCAL; unfold double_rectangular_public_globals; apply in_or_app; left; exact HEADER.
  - unfold double_source_instruction_globals in MEMBER; apply in_map_iff in MEMBER as [access [SAME ACCESS]].
    subst identifier; apply LOCAL; unfold double_rectangular_public_globals; apply in_or_app; right.
    apply in_map_iff; exists (fst (double_affine_source_function access),double_affine_source_dimensions access).
    split; [reflexivity|apply PTree.elements_correct; apply LAYOUT; exact ACCESS].
Qed.
Theorem checked_double_rectangular_entry_headers p controls source description ge locals :
  checked_double_rectangular_raw_nest p controls source=Some description ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_rectangular_globals description) locals ->
  forall axis, In axis (rectangular_nest_axes description) ->
    exists bound_block, double_global_binding ge locals (snd axis) bound_block.
Proof.
  intros CHECK GLOBAL LOCAL axis MEMBER.
  destruct (@checked_double_rectangular_raw_nest_sound p controls source description CHECK) as [_ [CANONICAL _]].
  destruct (@checked_double_rectangular_nest_sound p controls _ description CANONICAL) as [_ [_ [_ [_ HEADERS]]]].
  destruct (@double_rectangular_headers_check_sound p description HEADERS axis MEMBER) as [DECL WRITE].
  eapply (@checked_global_binding p [(snd axis,memory_long_type)] ge locals (snd axis) memory_long_type).
  - unfold global_declarations_check; cbn [forallb]; rewrite DECL; reflexivity.
  - cbn; auto.
  - exact GLOBAL.
  - intros identifier SINGLE; cbn in SINGLE; destruct SINGLE as [SAME|EMPTY]; [subst|contradiction].
    apply LOCAL; unfold double_rectangular_globals; apply in_or_app; left; apply in_map; exact MEMBER.
Qed.
Theorem checked_double_rectangular_raw_frameable p controls source description :
  checked_double_rectangular_raw_nest p controls source=Some description -> check_plan_frameable source=true.
Proof.
  intro CHECK; destruct (@checked_double_rectangular_raw_nest_sound p controls source description CHECK)
    as [RAW [CANONICAL EQUIV]].
  destruct (@checked_double_rectangular_nest_sound p controls _ description CANONICAL) as [_ [LEAF _]].
  destruct (@checked_double_reduction_assignment_shape p _ _ _ LEAF) as [target [rhs BODY]].
  rewrite RAW; generalize (rectangular_nest_axes description); intro axes; induction axes as [|[iterator header] rest IH];
    cbn [double_rectangular_raw_nest_code]; unfold long_raw_initialized_loop,long_raw_loaded_loop,long_counter_increment;
    cbn [check_plan_frameable]; rewrite ?BODY in *; rewrite ?IH; reflexivity.
Qed.
Definition double_rectangular_entry_bounds_check caps description :=
  Nat.eqb (length caps) (length (rectangular_nest_axes description)) &&
  forallb (fun cap => (0<?cap) && (cap<=?Int.max_signed)) caps &&
  double_rectangular_instruction_bounds_check caps (rectangular_nest_instruction description).
Theorem double_rectangular_checked_caps caps description :
  double_rectangular_entry_bounds_check caps description=true ->
  length caps=length (rectangular_nest_axes description) /\ Forall (fun cap => 0<cap<=Int.max_signed) caps.
Proof.
  unfold double_rectangular_entry_bounds_check; intro CHECK.
  apply andb_true_iff in CHECK as [CHECK _]; apply andb_true_iff in CHECK as [LENGTH RANGES].
  split; [apply Nat.eqb_eq; exact LENGTH|].
  apply Forall_forall; intros cap MEMBER; apply forallb_forall with (x:=cap) in RANGES; [|exact MEMBER].
  apply andb_true_iff in RANGES as [POSITIVE MAXIMUM]; apply Z.ltb_lt in POSITIVE; apply Z.leb_le in MAXIMUM; auto.
Qed.
Theorem double_rectangular_entry_bounds_check_ready p source description caps ge locals counts :
  checked_double_rectangular_raw_nest p [] source=Some description ->
  double_rectangular_entry_bounds_check caps description=true ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_rectangular_globals description) locals ->
  Forall2 (fun cap count => Z.of_nat count<=cap) caps counts ->
  double_rectangular_nest_ready (rectangular_nest_instruction description) ge counts [].
Proof.
  intros CHECK BOUNDS GLOBAL LOCAL LIMITS.
  unfold double_rectangular_entry_bounds_check in BOUNDS; apply andb_true_iff in BOUNDS as [_ BOUNDS].
  destruct (@checked_double_rectangular_raw_nest_sound p [] source description CHECK) as [_ [CANONICAL _]].
  destruct (@checked_double_rectangular_nest_sound p [] _ description CANONICAL) as [_ [LEAF _]].
  destruct (@checked_double_source_instruction_sound p _ _ _ LEAF) as [_ [_ [_ REGISTRY]]].
  pose proof (@double_source_layout_check_sound _ _ REGISTRY) as LAYOUT.
  intros coordinates WITHIN; cbn [app].
  eapply checked_double_source_instruction_resolved_from_bounds;
    [exact LEAF|exact LAYOUT|exact GLOBAL| |].
  - intros identifier MEMBER; apply LOCAL; unfold double_rectangular_globals; apply in_or_app; right; exact MEMBER.
  - eapply double_rectangular_instruction_bounds_check_sound; [exact BOUNDS|].
    eapply double_rectangular_counts_within_caps; eassumption.
Qed.

Lemma double_rectangular_linked_observation_axis (axes : double_rectangular_axes)
  (observations : double_rectangular_observations) header bound_block count :
  Forall2 (fun axis observation => snd axis=fst observation) axes observations ->
  In (header,(bound_block,count)) observations ->
  exists axis, In axis axes /\ snd axis=header.
Proof.
  intro LINK; induction LINK; intro MEMBER; [contradiction|].
  cbn in MEMBER; destruct MEMBER as [SAME|MEMBER].
  - subst y; exists x; split; [left; reflexivity|exact H].
  - destruct (IHLINK MEMBER) as [axis [AXIS HEADER]]; exists axis; split; [right; exact AXIS|exact HEADER].
Qed.
Lemma double_rectangular_linked_observed_axes (axes : double_rectangular_axes)
  (observations : double_rectangular_observations) :
  Forall2 (fun axis observation => snd axis=fst observation) axes observations ->
  double_rectangular_observed_axes axes (map (fun observation => snd (snd observation)) observations) observations.
Proof.
  intro LINK; induction LINK; cbn [map]; [constructor|].
  constructor.
  - destruct y as [header [bound_block count]]; exists bound_block; cbn [fst snd] in *; left; f_equal; symmetry; exact H.
  - unfold double_rectangular_observed_axes in *; eapply Forall2_impl; [|exact IHLINK].
    intros axis count [bound_block MEMBER]; exists bound_block; right; exact MEMBER.
Qed.
Definition double_rectangular_pipeline_model description := double_pipeline_statement
  (double_rectangular_nest_model (double_source_instruction_model (rectangular_nest_instruction description))
    (length (rectangular_nest_axes description)) 0 0).
Definition double_rectangular_pipeline_request description : DoubleAssignmentIRs.Loop.t :=
  (double_rectangular_pipeline_model description,map snd (rectangular_nest_axes description),
    map (fun key => (key,tt)) (double_rectangular_public_globals description)).
Theorem checked_double_rectangular_raw_pipeline_execution p source description caps fe ge locals
  observations temps memory after final :
  checked_double_rectangular_raw_nest p [] source=Some description ->
  double_rectangular_entry_bounds_check caps description=true ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_rectangular_globals description) locals ->
  (forall header bound_block count, In (header,(bound_block,count)) observations ->
    double_global_binding ge locals header bound_block) ->
  Forall2 (fun axis observation => snd axis=fst observation) (rectangular_nest_axes description) observations ->
  Forall2 (fun cap observation => Z.of_nat (snd (snd observation))<=cap) caps observations ->
  double_rectangular_observed_loads observations memory ->
  (exec_stmt fe ge locals temps memory source E0 after final Out_normal <->
   DoubleAssignmentIRs.Loop.loop_semantics (double_rectangular_pipeline_model description)
     (map (fun observation => Z.of_nat (snd (snd observation))) observations)
     (RuntimeState (global_double_locations ge (double_source_instruction_layouts (rectangular_nest_instruction description))) memory)
     (RuntimeState (global_double_locations ge (double_source_instruction_layouts (rectangular_nest_instruction description))) final) /\
   after=double_rectangular_nest_exit (double_rectangular_iterators (rectangular_nest_axes description))
     (map (fun observation => snd (snd observation)) observations) temps).
Proof.
  intros CHECK BOUNDS GLOBAL LOCAL BINDINGS LINK LIMITS LOADS.
  pose proof (@double_rectangular_checked_caps caps description BOUNDS) as [_ CAP_RANGES].
  assert (COUNT_LIMITS : Forall2 (fun cap count => Z.of_nat count<=cap) caps
    (map (fun observation => snd (snd observation)) observations)).
  { clear - LIMITS; induction LIMITS; cbn [map]; constructor; assumption. }
  assert (UPPERS : Forall (fun count => Z.of_nat count<=Int64.max_signed)
    (map (fun observation => snd (snd observation)) observations)).
  { clear - COUNT_LIMITS CAP_RANGES; revert CAP_RANGES; induction COUNT_LIMITS as [|cap count caps counts LIMIT TAIL IH];
      intro CAP_RANGES; [constructor|].
    inversion CAP_RANGES as [|cap' caps' CAP REST]; subst cap' caps'.
    constructor; [change (Z.of_nat count<=9223372036854775807);
      change (0<cap<=2147483647) in CAP; lia|apply IH; exact REST]. }
  destruct (@checked_double_rectangular_raw_nest_sound p [] source description CHECK) as [_ [CANONICAL EQUIV]].
  destruct (@checked_double_rectangular_nest_sound p [] _ description CANONICAL) as [_ [LEAF [FRESH [_ HEADERS]]]].
  assert (WRITE : forall header bound_block count, In (header,(bound_block,count)) observations ->
    fst (value_instruction_write (double_source_instruction_model (rectangular_nest_instruction description)))<>header).
  { intros header bound_block count MEMBER.
    destruct (@double_rectangular_linked_observation_axis _ _ _ _ _ LINK MEMBER) as [axis [AXIS HEADER]].
    rewrite <- HEADER; exact (proj2 (@double_rectangular_headers_check_sound p description HEADERS axis AXIS)). }
  rewrite (@EQUIV fe ge locals temps memory E0 after final Out_normal).
  pose proof (@double_rectangular_nest_canonical_source_model p fe ge locals observations GLOBAL BINDINGS
    (rectangular_nest_axes description) (map (fun observation => snd (snd observation)) observations)
    0 (map Z.of_nat (map (fun observation => snd (snd observation)) observations)) [] (fun _=>0)
    (rectangular_nest_body description) (rectangular_nest_instruction description) temps memory after final
    LEAF FRESH ltac:(intros identifier MEMBER; apply LOCAL; unfold double_rectangular_globals;
      apply in_or_app; right; exact MEMBER) WRITE
    (@double_rectangular_linked_observed_axes _ _ LINK) UPPERS eq_refl
    (@double_rectangular_entry_bounds_check_ready p source description caps ge locals _
      CHECK BOUNDS GLOBAL LOCAL COUNT_LIMITS)
    ltac:(split; [intros key MEMBER; contradiction|exact LOADS])) as MODEL.
  cbn [map rev app length] in MODEL; rewrite map_map,double_pipeline_execution in MODEL.
  exact MODEL.
Qed.

Print Assumptions double_rectangular_layout_span_check_sound.
Print Assumptions checked_double_rectangular_public_scope.
Print Assumptions checked_double_rectangular_entry_headers.
Print Assumptions checked_double_rectangular_raw_frameable.
Print Assumptions double_rectangular_checked_caps.
Print Assumptions double_rectangular_entry_bounds_check_ready.
Print Assumptions double_rectangular_linked_observation_axis.
Print Assumptions double_rectangular_linked_observed_axes.
Print Assumptions checked_double_rectangular_raw_pipeline_execution.
