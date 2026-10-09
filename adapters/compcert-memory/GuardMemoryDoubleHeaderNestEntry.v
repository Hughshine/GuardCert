From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGlobalScope ClightProjectedExecution ClightTempFrame ClightTempFootprint ClightRegionProgress.
From GuardInterface Require Import ClightCheckPlanFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations GuardMemoryDoubleProgramBindings GuardMemoryDynamicTensorLayout GuardMemoryDoubleTensorBackend GuardMemoryDoubleSourceInstruction
  GuardMemoryDoubleSourceTransport GuardMemoryDoubleSourceResolvedPoints GuardMemoryDoubleAffineSourceAccess
  GuardMemoryDoubleReductionNestData GuardMemoryDoubleReductionNestModel GuardMemoryDoubleReductionNestSource
  GuardMemoryDoubleInitializedNestSource GuardMemoryDoubleInitializedBounds GuardMemoryDoubleInitializedRawNest
  GuardMemoryLongControl GuardMemoryLongLoopControl GuardMemoryLongHeaderLicense GuardMemoryLongRangeCapture
  GuardMemoryLongRawLoadedProgress GuardMemoryLongProgressControl GuardMemoryDoublePipelineTransport GuardMemoryDoublePolyhedral
  GuardMemoryDoubleReductionNestEntry GuardMemoryDoubleHeaderBounds GuardMemoryDoubleHeaderInstruction
  GuardMemoryDoubleHeaderNestData GuardMemoryDoubleHeaderNestModel GuardMemoryDoubleHeaderNestSource.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem checked_double_header_public_scope p controls source description locals :
  checked_double_header_raw_nest p controls source=Some description ->
  locals_avoid (double_reduction_public_globals description) locals -> locals_avoid (double_reduction_globals description) locals.
Proof.
  intros CHECK LOCAL.
  destruct (@checked_double_header_raw_nest_sound p controls source description CHECK) as [_ [CANONICAL _]].
  destruct (@checked_double_header_nest_sound p controls _ description CANONICAL) as [_ [LEAF _]].
  destruct (@checked_double_header_source_instruction_sound p _ _ _ _ LEAF) as [_ [_ [_ REGISTRY]]].
  pose proof (@double_source_layout_check_sound _ _ REGISTRY) as LAYOUT.
  intros identifier MEMBER; unfold double_reduction_globals in MEMBER; destruct MEMBER as [SAME|MEMBER].
  - subst identifier; apply LOCAL; unfold double_reduction_public_globals; left; reflexivity.
  - unfold double_source_instruction_globals in MEMBER; apply in_map_iff in MEMBER as [access [SAME ACCESS]].
    subst identifier; apply LOCAL; unfold double_reduction_public_globals; right.
    apply in_map_iff; exists (fst (double_affine_source_function access),double_affine_source_dimensions access).
    split; [reflexivity|apply PTree.elements_correct; apply LAYOUT; exact ACCESS].
Qed.
Theorem checked_double_header_entry_header p controls source description ge locals :
  checked_double_header_raw_nest p controls source=Some description ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_reduction_globals description) locals ->
  exists header_block, double_global_binding ge locals (reduction_nest_header description) header_block.
Proof.
  intros CHECK GLOBAL LOCAL.
  destruct (@checked_double_header_raw_nest_sound p controls source description CHECK) as [_ [CANONICAL _]].
  destruct (@checked_double_header_nest_sound p controls _ description CANONICAL) as [_ [_ [_ [_ [DECL _]]]]].
  eapply (@checked_global_binding p [(reduction_nest_header description,memory_long_type)] ge locals
    (reduction_nest_header description) memory_long_type).
  - unfold global_declarations_check; cbn [forallb]; rewrite DECL; reflexivity.
  - cbn; auto.
  - exact GLOBAL.
  - intros identifier MEMBER; cbn in MEMBER; destruct MEMBER as [SAME|EMPTY]; [subst|contradiction].
    apply LOCAL; left; reflexivity.
Qed.
Theorem checked_double_header_raw_header_license p controls source description fe ge locals temps memory header_block after final :
  checked_double_header_raw_nest p controls source=Some description ->
  double_global_binding ge locals (reduction_nest_header description) header_block ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists word, Mem.load Mint64 memory header_block 0=Some (Vlong word).
Proof.
  intros CHECK HEADER SOURCE.
  destruct (@checked_double_header_raw_nest_sound p controls source description CHECK) as [_ [CANONICAL EQUIV]].
  destruct (@checked_double_header_nest_sound p controls _ description CANONICAL) as [_ [LEAF [_ [NONEMPTY _]]]].
  destruct (reduction_nest_iterators description) as [|iterator rest] eqn:ITERATORS; [contradiction|].
  apply EQUIV in SOURCE; cbn [double_reduction_nest_code] in SOURCE.
  destruct (@memory_global_long_initialized_license fe ge locals temps memory iterator (reduction_nest_header description)
    header_block (double_reduction_nest_code rest (reduction_nest_header description) (reduction_nest_body description))
    after final HEADER (@double_reduction_nest_normal rest _ _
      (@checked_double_header_assignment_shape p _ _ _ _ LEAF)) SOURCE) as [word [LOAD NEXT]].
  exists word; exact LOAD.
Qed.
Theorem checked_double_header_raw_frameable p controls source description :
  checked_double_header_raw_nest p controls source=Some description -> check_plan_frameable source=true.
Proof.
  intro CHECK; destruct (@checked_double_header_raw_nest_sound p controls source description CHECK) as [RAW [CANONICAL EQUIV]].
  destruct (@checked_double_header_nest_sound p controls _ description CANONICAL) as [_ [LEAF _]].
  destruct (@checked_double_header_assignment_shape p _ _ _ _ LEAF) as [target [rhs BODY]].
  rewrite RAW; generalize (reduction_nest_iterators description); intro iterators; induction iterators;
    cbn [double_reduction_raw_nest_code]; unfold long_raw_initialized_loop,long_raw_loaded_loop,long_counter_increment;
    cbn [check_plan_frameable]; rewrite ?BODY in *; rewrite ?IHiterators; reflexivity.
Qed.
Definition double_header_nest_entry_bounds_check limit description :=
  (0<?limit) && (limit<=?Int.max_signed) &&
  double_header_instruction_bounds_check limit (reduction_nest_instruction description).
Lemma double_header_nest_checked_limit limit description :
  double_header_nest_entry_bounds_check limit description=true -> 0<limit<=Int.max_signed.
Proof.
  unfold double_header_nest_entry_bounds_check; intro CHECK.
  apply andb_true_iff in CHECK as [CHECK _]; apply andb_true_iff in CHECK as [POSITIVE MAXIMUM].
  apply Z.ltb_lt in POSITIVE; apply Z.leb_le in MAXIMUM; split; assumption.
Qed.
Theorem double_header_nest_entry_bounds_check_ready p source description limit ge locals count :
  checked_double_header_raw_nest p [] source=Some description -> double_header_nest_entry_bounds_check limit description=true ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_reduction_globals description) locals -> Z.of_nat count<=limit ->
  double_header_nest_ready (reduction_nest_instruction description) ge count [] (length (reduction_nest_iterators description)).
Proof.
  intros CHECK BOUNDS GLOBAL LOCAL UPPER.
  pose proof (@double_header_nest_checked_limit limit description BOUNDS) as LIMIT.
  unfold double_header_nest_entry_bounds_check in BOUNDS; apply andb_true_iff in BOUNDS as [_ BOUNDS].
  destruct (@checked_double_header_raw_nest_sound p [] source description CHECK) as [_ [CANONICAL _]].
  destruct (@checked_double_header_nest_sound p [] _ description CANONICAL) as [_ [LEAF _]].
  destruct (@checked_double_header_source_instruction_sound p _ _ _ _ LEAF) as [_ [_ [_ REGISTRY]]].
  pose proof (@double_source_layout_check_sound _ _ REGISTRY) as LAYOUT.
  intros coordinates LENGTH WITHIN; cbn [app].
  eapply checked_double_header_source_instruction_resolved_from_bounds;
    [exact LEAF|exact LAYOUT|exact GLOBAL| |].
  - intros identifier MEMBER; apply LOCAL; right; exact MEMBER.
  - assert (NONEMPTY : reduction_nest_iterators description<>[]).
    { destruct (@checked_double_header_nest_sound p [] _ description CANONICAL) as [_ [_ [_ [NE _]]]]; exact NE. }
    assert (POSITIVE : 1<=Z.of_nat count).
    { destruct coordinates as [|value rest].
      - cbn in LENGTH; apply eq_sym in LENGTH; apply length_zero_iff_nil in LENGTH; contradiction.
      - inversion WITHIN; lia. }
    exact (@double_header_instruction_bounds_check_sound limit (reduction_nest_instruction description)
      (Z.of_nat count) coordinates BOUNDS ltac:(lia) WITHIN).
Qed.
Definition double_header_pipeline_model description := double_pipeline_statement
  (double_header_nest_model (double_source_instruction_model (reduction_nest_instruction description))
    (length (reduction_nest_iterators description)) 0).
Definition double_header_pipeline_request description : DoubleAssignmentIRs.Loop.t :=
  (double_header_pipeline_model description,[reduction_nest_header description],
    map (fun key => (key,tt)) (double_reduction_public_globals description)).
Theorem checked_double_header_raw_pipeline_execution p source description limit fe ge locals header_block count temps memory after final :
  checked_double_header_raw_nest p [] source=Some description -> double_header_nest_entry_bounds_check limit description=true ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_reduction_globals description) locals ->
  double_global_binding ge locals (reduction_nest_header description) header_block -> Z.of_nat count<=limit ->
  Mem.load Mint64 memory header_block 0=Some (Vlong (Int64.repr (Z.of_nat count))) ->
  (exec_stmt fe ge locals temps memory source E0 after final Out_normal <->
   DoubleAssignmentIRs.Loop.loop_semantics (double_header_pipeline_model description) [Z.of_nat count]
     (RuntimeState (global_double_locations ge (double_source_instruction_layouts (reduction_nest_instruction description))) memory)
     (RuntimeState (global_double_locations ge (double_source_instruction_layouts (reduction_nest_instruction description))) final) /\
   after=double_reduction_nest_exit (reduction_nest_iterators description) count temps).
Proof.
  intros CHECK BOUNDS GLOBAL LOCAL HEADER UPPER LOAD.
  pose proof (@double_header_nest_checked_limit limit description BOUNDS) as LIMIT.
  destruct (@checked_double_header_raw_nest_sound p [] source description CHECK) as [_ [CANONICAL EQUIV]].
  destruct (@checked_double_header_nest_sound p [] _ description CANONICAL) as [_ [LEAF [FRESH [_ [_ WRITE]]]]].
  rewrite (@EQUIV fe ge locals temps memory E0 after final Out_normal).
  pose proof (@double_header_nest_canonical_source_model p fe ge locals (reduction_nest_header description) header_block count
    GLOBAL ltac:(change (Z.of_nat count<=9223372036854775807); change (0<limit<=2147483647) in LIMIT; lia)
    (reduction_nest_iterators description) [] (fun _=>Z.of_nat count) (reduction_nest_body description) (reduction_nest_instruction description)
    temps memory after final LEAF FRESH eq_refl ltac:(intros identifier MEMBER; apply LOCAL; right; exact MEMBER) HEADER WRITE
    (@double_header_nest_entry_bounds_check_ready p source description limit ge locals count CHECK BOUNDS GLOBAL LOCAL UPPER)
    ltac:(split; [intros key MEMBER; contradiction|exact LOAD])) as MODEL.
  cbn [map rev app length] in MODEL; rewrite double_pipeline_execution in MODEL; exact MODEL.
Qed.


Print Assumptions checked_double_header_public_scope.
Print Assumptions checked_double_header_entry_header.
Print Assumptions checked_double_header_raw_header_license.
Print Assumptions checked_double_header_raw_frameable.
Print Assumptions double_header_nest_checked_limit.
Print Assumptions double_header_nest_entry_bounds_check_ready.
Print Assumptions checked_double_header_raw_pipeline_execution.
