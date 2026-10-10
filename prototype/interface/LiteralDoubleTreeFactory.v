From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightGuard ClightCountedLoop ClightTempFrame ClightTempFootprint ClightGlobalScope
  ClightProjectedExecution ClightScopedPrivateRegion ClightRegionProgress CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryDoubleSourceTreeData GuardMemoryDoubleTreeEntry
  GuardMemoryDoubleTreePrepared GuardMemoryDoubleTreeSourcePrepared GuardMemoryDoubleTreeResidualCandidate
  GuardMemoryLiteralDoubleTreeData GuardMemoryLiteralDoubleTreeDecode GuardMemoryLiteralDoubleTreeSyntax GuardMemoryLiteralDoubleTreeProgress
  GuardMemoryLiteralDoubleTreeFacts GuardMemoryLiteralDoubleTreeScope GuardMemoryLiteralDoubleTreeExecution.
From GuardInterface Require Import RectangularDoubleTiledFactory TightenedRectangularDoubleFactory DoubleTreeRegionFactory.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem literal_double_tree_region_contract p source tree cache flag live pool phase adapt shifts choices generated code :
  checked_literal_double_source_tree p source=Some tree -> literal_double_tree_footprint_check tree []=true ->
  double_tree_layout_span_check (literal_double_tree_skeleton tree)=true ->
  double_tree_resources source (literal_double_tree_skeleton tree) cache flag live=true ->
  mayReturn (checked_double_tree_source_prepared_loop_progress phase adapt shifts choices
    (double_tree_parameter_intervals (double_source_tree_parameters (literal_double_tree_skeleton tree))
      literal_double_parameter_value literal_double_parameter_value) (literal_double_tree_pipeline_request tree)) (Some generated) ->
  compile_residual_double_tree_candidate (double_source_tree_layouts (literal_double_tree_skeleton tree))
    (literal_double_tree_skeleton tree) cache flag literal_double_parameter_value literal_double_parameter_value live pool generated=Some code ->
  ScopedPrivateRegion.projected_region_contract live (globalenv p) (literal_double_tree_public_globals tree)
    source (literal_double_tree_candidate_code tree cache code).
Proof.
  intros CHECK FOOTPRINT SPAN RESOURCES PIPELINE CODE.
  destruct (@checked_literal_double_source_tree_sound p source tree CHECK) as [SHAPE [TREE LAYOUT]].
  assert (WRITES : writes_only (double_source_tree_writes (literal_double_tree_skeleton tree)) source).
  { rewrite SHAPE; apply literal_double_source_tree_writes_only with (p:=p) (controls:=[]); exact TREE. }
  intros temps reference locals le tle memory after final GLOBAL LOCAL SCOPE FRAME SOURCE f k.
  pose proof (@checked_literal_double_tree_public_scope p source tree locals CHECK LOCAL) as LEAF_SCOPE.
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv reference) locals le memory
    source E0 after final Out_normal SOURCE live tle (double_source_tree_writes (literal_double_tree_skeleton tree)) WRITES SCOPE FRAME)
    as [transported [TRANSPORT FRAME_OUT]].
  destruct (@checked_literal_double_tree_candidate_execution p source tree cache flag live pool phase adapt shifts choices generated code
    (adapter_entry temps) (globalenv reference) locals tle memory transported final CHECK GLOBAL LEAF_SCOPE
    (@literal_double_tree_layout_span_sound tree (globalenv reference) locals SPAN LOCAL) FOOTPRINT RESOURCES PIPELINE CODE TRANSPORT)
    as [target_after [TARGET FRAME_TARGET]].
  exists target_after,final; split; [apply normal_fragment_steps; exact TARGET|].
  split; [eapply temp_agree_trans; eauto|apply memory_equivalent_refl].
Qed.

(** Static refusal returns None; the host retains the original source. All
    model parameters here are constants. No speculative header load is emitted. *)
Definition check_literal_double_tree_region p live pool phase adapt shifts choices source : Base.imp (option statement) :=
  match pool,checked_literal_double_source_tree p source with
  | (flag,flag_type)::pool,Some tree=>
    if literal_double_source_tree_active_root tree && negb (Nat.eqb (length (double_source_tree_instructions (literal_double_tree_skeleton tree))) O) then
    if type_eq flag_type type_int32s then
    match take_rectangular_double_caches (length (double_source_tree_parameters (literal_double_tree_skeleton tree))) pool with
    | Some (caches,private)=>match rectangular_counter_pairs private with
      | Some pairs=>let model:=literal_double_tree_skeleton tree in
        let cache:=double_tree_allocated_cache model caches flag in
        if literal_double_tree_footprint_check tree [] then
        if double_tree_layout_span_check model then
        if double_tree_resources source model cache flag live then
          BIND generated <- checked_double_tree_source_prepared_loop_progress phase adapt shifts choices
            (double_tree_parameter_intervals (double_source_tree_parameters model)
              literal_double_parameter_value literal_double_parameter_value) (literal_double_tree_pipeline_request tree) -;
          pure (match generated with
            | Some generated=>match compile_residual_double_tree_candidate (double_source_tree_layouts model) model cache flag
                literal_double_parameter_value literal_double_parameter_value live pairs generated with
              | Some code=>Some (literal_double_tree_candidate_code tree cache code) | None=>None end
            | None=>None end)
        else pure None else pure None else pure None
      | None=>pure None end
    | None=>pure None end else pure None else pure None
  | _,_=>pure None end.
Theorem check_literal_double_tree_region_sound p live pool phase adapt shifts choices source target :
  mayReturn (check_literal_double_tree_region p live pool phase adapt shifts choices source) (Some target) ->
  ScopedPrivateRegion.projected_region_contract live (globalenv p) (literal_double_tree_source_globals p source) source target.
Proof.
  unfold check_literal_double_tree_region,literal_double_tree_source_globals.
  destruct pool as [|[flag flag_type] pool]; [intro RUN; apply mayReturn_pure in RUN; discriminate|].
  destruct (checked_literal_double_source_tree p source) as [tree|] eqn:CHECK;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (literal_double_source_tree_active_root tree && negb (Nat.eqb (length (double_source_tree_instructions (literal_double_tree_skeleton tree))) O));
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (type_eq flag_type type_int32s); [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (take_rectangular_double_caches (length (double_source_tree_parameters (literal_double_tree_skeleton tree))) pool)
    as [[caches private]|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (rectangular_counter_pairs private) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (literal_double_tree_footprint_check tree []) eqn:FOOTPRINT; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (double_tree_layout_span_check (literal_double_tree_skeleton tree)) eqn:SPAN;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (double_tree_resources source (literal_double_tree_skeleton tree)
    (double_tree_allocated_cache (literal_double_tree_skeleton tree) caches flag) flag live) eqn:RESOURCES;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN generated PIPELINE.
  destruct generated as [generated|]; [|apply mayReturn_pure in RUN; discriminate].
  destruct (compile_residual_double_tree_candidate (double_source_tree_layouts (literal_double_tree_skeleton tree))
    (literal_double_tree_skeleton tree) (double_tree_allocated_cache (literal_double_tree_skeleton tree) caches flag)
    flag literal_double_parameter_value literal_double_parameter_value live pairs generated) as [code|] eqn:CODE;
    apply mayReturn_pure in RUN; [|discriminate].
  inversion RUN; subst target; eapply literal_double_tree_region_contract; eauto.
Qed.
Print Assumptions literal_double_tree_region_contract.
Print Assumptions check_literal_double_tree_region_sound.
