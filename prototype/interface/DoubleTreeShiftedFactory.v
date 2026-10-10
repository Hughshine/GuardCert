From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightGuard ClightCountedLoop ClightTempFrame ClightTempFootprint ClightGlobalScope ClightProjectedExecution
  ClightScopedPrivateRegion ClightRegionProgress CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryDoubleSourceTreeData GuardMemoryDoubleSourceTreeDecode
  GuardMemoryDoubleSourceTreeSyntax GuardMemoryDoubleSourceTreeProgress GuardMemoryDoubleSourceTreeCertificates
  GuardMemoryDoubleSourceTreeModelData GuardMemoryDoubleTreeEntry GuardMemoryDoubleTreeFootprint
  GuardMemoryDoubleTreeGuarded GuardMemoryDoubleTreePrepared GuardMemoryDoubleTreeCandidate GuardMemoryDoubleTreeShiftedPrepared GuardMemoryDoubleTreeShiftedGuarded.
From GuardInterface Require Import RectangularDoubleTiledFactory TightenedRectangularDoubleFactory DoubleTreeRegionFactory.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem double_tree_shifted_region_contract p source tree cache flag lower upper live pool phase adapt shifts_proposal choices generated code :
  checked_double_source_tree p source=Some tree -> double_tree_profile_check tree lower upper=true ->
  double_tree_footprint_check tree upper []=true -> double_tree_layout_span_check tree=true ->
  double_tree_resources source tree cache flag live=true ->
  mayReturn (checked_double_tree_shifted_prepared_loop_progress phase adapt shifts_proposal choices
    (double_tree_parameter_intervals (double_source_tree_parameters tree) lower upper) (double_tree_pipeline_request tree))
    (Some generated) ->
  compile_double_tree_candidate (double_source_tree_layouts tree) tree cache flag lower upper live pool generated=Some code ->
  ScopedPrivateRegion.projected_region_contract live (globalenv p) (double_tree_public_globals tree) source
    (double_tree_guarded_code source tree cache flag lower upper code).
Proof.
  intros CHECK PROFILE FOOTPRINT SPAN RESOURCES PIPELINE CODE.
  destruct (@double_tree_resources_sound source tree cache flag live RESOURCES) as [DISTINCT [FLAG [CACHES PRIVATE]]].
  destruct (@checked_double_source_tree_sound p source tree CHECK) as [SHAPE [TREE REST]].
  assert (WRITES : writes_only (double_source_tree_writes tree) source).
  { rewrite SHAPE; apply double_source_tree_writes_only with (p:=p) (controls:=[]); exact TREE. }
  intros temps reference locals le tle memory after final GLOBAL LOCAL SCOPE FRAME SOURCE f k.
  destruct (@checked_double_tree_public_scope p source tree locals CHECK LOCAL) as [LEAF_SCOPE HEADER_SCOPE].
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv reference) locals le memory
    source E0 after final Out_normal SOURCE live tle (double_source_tree_writes tree) WRITES SCOPE FRAME)
    as [transported [TRANSPORT FRAME_OUT]].
  destruct (@checked_double_tree_shifted_guarded_execution p source tree cache flag lower upper live pool phase adapt shifts_proposal choices generated code
    (adapter_entry temps) (globalenv reference) locals tle memory transported final CHECK GLOBAL LEAF_SCOPE HEADER_SCOPE
    (@double_tree_layout_span_check_sound tree (globalenv reference) locals SPAN LOCAL) FOOTPRINT
    (@double_tree_profile_check_sound tree lower upper PROFILE) DISTINCT FLAG CACHES PRIVATE PIPELINE CODE TRANSPORT)
    as [target_after [TARGET FRAME_TARGET]].
  exists target_after,final; split; [apply normal_fragment_steps; exact TARGET|].
  split; [eapply temp_agree_trans; eauto|apply memory_equivalent_refl].
Qed.
(** Profiles and phase/adaptation proposals are ordinary untrusted data. The
    factory constructs typed private capture slots and the actual candidate,
    fallback and public-exit code, and validates every semantic prerequisite. *)
Definition check_double_tree_shifted_region p live pool phase adapt shifts_proposal choices
  (lower_proposal upper_proposal : double_source_tree -> ident -> Z) source : Base.imp (option statement) :=
  match pool,checked_double_source_tree p source with
  | (flag,flag_type)::pool,Some tree=>if type_eq flag_type type_int32s then
    match take_rectangular_double_caches (length (double_source_tree_parameters tree)) pool with
    | Some (caches,private)=>match rectangular_counter_pairs private with
      | Some pairs=>let cache:=double_tree_allocated_cache tree caches flag in
        let lower:=lower_proposal tree in let upper:=upper_proposal tree in
        if double_tree_profile_check tree lower upper then
        if double_tree_footprint_check tree upper [] then
        if double_tree_layout_span_check tree then
        if double_tree_resources source tree cache flag live then
          BIND generated <- checked_double_tree_shifted_prepared_loop_progress phase adapt shifts_proposal choices
            (double_tree_parameter_intervals (double_source_tree_parameters tree) lower upper) (double_tree_pipeline_request tree) -;
          pure (match generated with
            | Some generated=>match compile_double_tree_candidate (double_source_tree_layouts tree) tree cache flag
                lower upper live pairs generated with
              | Some code=>Some (double_tree_guarded_code source tree cache flag lower upper code) | None=>None end
            | None=>None end)
        else pure None else pure None else pure None else pure None
      | None=>pure None end
    | None=>pure None end else pure None
  | _,_=>pure None end.
Theorem check_double_tree_shifted_region_sound p live pool phase adapt shifts_proposal choices lower_proposal upper_proposal source target :
  mayReturn (check_double_tree_shifted_region p live pool phase adapt shifts_proposal choices lower_proposal upper_proposal source) (Some target) ->
  ScopedPrivateRegion.projected_region_contract live (globalenv p) (double_tree_source_globals p source) source target.
Proof.
  unfold check_double_tree_shifted_region,double_tree_source_globals.
  destruct pool as [|[flag flag_type] pool]; [intro RUN; apply mayReturn_pure in RUN; discriminate|].
  destruct (checked_double_source_tree p source) as [tree|] eqn:CHECK; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (type_eq flag_type type_int32s); [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (take_rectangular_double_caches (length (double_source_tree_parameters tree)) pool) as [[caches private]|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (rectangular_counter_pairs private) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (double_tree_profile_check tree (lower_proposal tree) (upper_proposal tree)) eqn:PROFILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (double_tree_footprint_check tree (upper_proposal tree) []) eqn:FOOTPRINT;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (double_tree_layout_span_check tree) eqn:SPAN; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (double_tree_resources source tree (double_tree_allocated_cache tree caches flag) flag live) eqn:RESOURCES;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN generated PIPELINE.
  destruct generated as [generated|]; [|apply mayReturn_pure in RUN; discriminate].
  destruct (compile_double_tree_candidate (double_source_tree_layouts tree) tree (double_tree_allocated_cache tree caches flag)
    flag (lower_proposal tree) (upper_proposal tree) live pairs generated) as [code|] eqn:CODE;
    apply mayReturn_pure in RUN; [|discriminate].
  inversion RUN; subst target; eapply double_tree_shifted_region_contract; eauto.
Qed.

Print Assumptions double_tree_shifted_region_contract.
Print Assumptions check_double_tree_shifted_region_sound.
