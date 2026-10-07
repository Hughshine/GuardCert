From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightProjectedExecution.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryBoundedSourceChecker GuardMemoryWindowBackend.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestPackageDecode
  AffineNestPackageRanges AffineNestMultiStaticPackage AffineNestMultiPresumption AffineNestMultiCandidateLocal.
From GuardInterface Require Import ClightLoadedAffineNumericGuard ClightLoadedAffineNumericSite ClightLoadedAffineBodyPrefix
  ClightLoadedAffineScanSite ClightLoadedAffineScanExecution ClightLoadedAffineScanCertificate ClightLoadedAffineScanTransfer
  ClightCheckPlanFrame ClightAffineNestMaterialized ClightExpressionAffineNumericSite
  ClightLoadedOffsetHeader ClightLoadedOffsetAffineCache ClightLoadedOffsetAffineScanSite
  ClightLoadedOffsetAffineScanExecution ClightLoadedOffsetAffineScanCertificate ClightLoadedOffsetAffineScanTransfer.
Import ListNotations.
Set Implicit Arguments.

Lemma offset_affine_snapshot_word_unique proposal pointer delta entry first second :
  pointer<>affine_proposed_bound proposal ->
  loaded_offset_cached_header pointer delta(affine_proposed_bound proposal)(loaded_affine_scan_prepared proposal entry first) ->
  loaded_offset_cached_header pointer delta(affine_proposed_bound proposal)(loaded_affine_scan_prepared proposal entry second) -> first=second.
Proof.
  intros PRIVATE [block [offset [upper [POINTER [READ CACHE]]]]]
    [other [base [value [OTHER [LOAD WORD]]]]].
  cbn [loaded_affine_scan_prepared entry_temps entry_memory] in *.
  rewrite PTree.gso in POINTER,OTHER by exact PRIVATE; rewrite PTree.gss in CACHE,WORD.
  injection CACHE as FIRST; injection WORD as SECOND.
  assert(SAME:Vptr block offset=Vptr other base) by congruence; injection SAME as BLOCK OFFSET; subst other base.
  congruence.
Qed.

Lemma offset_affine_pointer_cache_distinct source parameters live proposal pointer delta
  (site : offset_affine_scan_site source parameters live proposal pointer delta) : pointer<>affine_proposed_bound proposal.
Proof.
  intro SAME; apply(expression_numeric_private(offset_scan_numeric site)),in_or_app; right.
  rewrite <-SAME; exact(offset_scan_pointer_ports site (or_introl eq_refl)).
Qed.

Theorem offset_affine_cached_source_at_snapshot source parameters live proposal pointer delta
  (site : offset_affine_scan_site source parameters live proposal pointer delta) fe ge locals temps memory after final upper :
  offset_affine_scan_presumption fe parameters proposal pointer delta(Entry ge locals temps memory) ->
  loaded_offset_cached_header pointer delta(affine_proposed_bound proposal)(loaded_affine_scan_prepared proposal(Entry ge locals temps memory) upper) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists cached_after,
    exec_stmt fe ge locals(PTree.set(affine_proposed_bound proposal)(Vint upper) temps) memory
      (affine_nest_source(affine_proposal_nest proposal)) E0 cached_after final Out_normal /\
    temp_agree live after cached_after.
Proof.
  intros [value [SNAPSHOT [NUMERIC [ROW [NONNEGATIVE PRESERVE]]]]] EXPECTED SOURCE.
  pose proof(@offset_affine_snapshot_word_unique proposal pointer delta(Entry ge locals temps memory) value upper
    (offset_affine_pointer_cache_distinct site) SNAPSHOT EXPECTED) as SAME; subst value.
  pose proof(expression_numeric_private(offset_scan_numeric site)) as PRIVATE.
  pose proof(expression_numeric_frameable(offset_scan_numeric site)) as FRAMEABLE.
  destruct(@structured_execution_temp_transport fe ge locals temps memory source E0 after final Out_normal SOURCE
    (statement_temps source++live)(PTree.set(affine_proposed_bound proposal)(Vint upper) temps)(statement_temps source)
    (@check_plan_frameable_writes source FRAMEABLE)
    ltac:(unfold statement_scope; intros identifier MEMBER; apply in_or_app; left; exact MEMBER)
    (@temp_agree_set _ temps(affine_proposed_bound proposal)(Vint upper) PRIVATE)) as [cached_after [PREPARED FRAME]].
  exists cached_after; split.
  - rewrite(expression_numeric_exact(offset_scan_numeric site)) in PREPARED.
    exact(@offset_affine_body_cached_source _ parameters _ proposal(expression_numeric_package(offset_scan_numeric site))
      pointer delta fe ge locals _ memory cached_after final (offset_scan_body_names site) SNAPSHOT ROW NONNEGATIVE PRESERVE PREPARED).
  - eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER; apply in_or_app; right; exact MEMBER.
Qed.

(* The model reference is produced by the preceding check. Its protected
   inputs are related to the original entry and its freshly read cache. *)
Definition offset_affine_candidate_presumption fe parameters live proposal pointer delta entry :=
  offset_affine_scan_presumption fe parameters proposal pointer delta entry /\
  exists upper reference,
    loaded_offset_cached_header pointer delta(affine_proposed_bound proposal)(loaded_affine_scan_prepared proposal entry upper) /\
    temp_agree(loaded_affine_scan_ports parameters proposal live)
      (entry_temps(loaded_affine_scan_prepared proposal entry upper)) reference /\
    affine_multi_guard_flag parameters proposal(Entry(entry_ge entry)(entry_env entry) reference(entry_memory entry))=true.

Section CANDIDATE.
Variables source : statement.
Variables parameters live allocated : list ident.
Variable proposal : affine_guard_proposal.
Variable pointer : ident.
Variable delta : int.
Variable site : offset_affine_scan_site source parameters live proposal pointer delta.
Let ports := loaded_affine_scan_ports parameters proposal live.
Let cached := affine_nest_source(affine_proposal_nest proposal).
Variable package : affine_multi_static_package cached parameters ports allocated proposal.
Hypothesis CACHED_SCOPE : statement_scope ports cached.
Variable candidate : L.stmt.
Variable pool : list(ident*ident).
Variable code : statement.
Hypothesis VALIDATOR : memory_bounded_source_certificate(affine_package_validator_bounds proposal)
  (affine_multi_source_loop package)(affine_package_context parameters proposal) candidate.
Hypothesis COMPILE : compile_window_multi_pointer_buffer_loop(affine_proposed_pointers proposal)
  (affine_package_context parameters proposal)(affine_package_encoder_bounds proposal) ports pool candidate=Some code.

Theorem offset_affine_candidate_local fe ge locals temps memory current source_after final :
  offset_affine_candidate_presumption fe parameters live proposal pointer delta(Entry ge locals temps memory) ->
  offset_affine_scan_entry_relation parameters live proposal pointer delta(Entry ge locals temps memory)(Entry ge locals current memory) ->
  exec_stmt fe ge locals temps memory source E0 source_after final Out_normal ->
  exists after,
    exec_stmt fe ge locals current memory(affine_multi_candidate_code proposal code) E0 after final Out_normal /\
    temp_agree live source_after after.
Proof.
  intros [STABILITY [upper [reference [SNAPSHOT [REFERENCE ACCEPT]]]]]
    [checked_word [CHECKED_SNAPSHOT [_ [_ [_ CHECKED]]]]] SOURCE.
  pose proof(@offset_affine_snapshot_word_unique proposal pointer delta(Entry ge locals temps memory) checked_word upper
    (offset_affine_pointer_cache_distinct site) CHECKED_SNAPSHOT SNAPSHOT) as SAME; subst checked_word.
  destruct(@offset_affine_cached_source_at_snapshot _ _ _ _ _ _ site fe ge locals temps memory source_after final upper
    STABILITY SNAPSHOT SOURCE) as [cached_after [CACHED PUBLIC]].
  destruct(@structured_execution_temp_transport fe ge locals _ memory cached E0 cached_after final Out_normal CACHED
    ports reference(affine_nest_controls(affine_proposal_nest proposal))
    (affine_materialized_source_writes(affine_multi_guard package)) CACHED_SCOPE REFERENCE)
    as [reference_after [REFERENCE_SOURCE SOURCE_FRAME]].
  assert(ENTRY:temp_agree(affine_package_context parameters proposal++affine_proposed_pointers proposal++ports) reference current).
  { intros identifier MEMBER.
    assert(PROTECTED:In identifier ports).
    { repeat rewrite in_app_iff in MEMBER; destruct MEMBER as [CONTEXT|[POINTER|PORT]]; [|apply(affine_multi_pointer_public package); exact POINTER|exact PORT].
      unfold affine_package_context in CONTEXT; apply in_app_or in CONTEXT as [PARAMETER|ROOT];
        [apply(affine_multi_parameters_public package); exact PARAMETER|].
      cbn [List.In] in ROOT; destruct ROOT as [<-|BAD]; [apply(affine_multi_root_public package)|contradiction]. }
    rewrite CHECKED,REFERENCE by exact PROTECTED; reflexivity. }
  destruct(@affine_multi_candidate_local cached parameters ports proposal allocated package
    (affine_multi_source_loop package) candidate pool code(affine_multi_pointer_private package)
    (affine_multi_window_low package)(affine_multi_window_high package)
    (affine_multi_source_lower package)(affine_multi_shadow_scope package) VALIDATOR COMPILE
    fe ge locals reference current memory reference_after final ENTRY ACCEPT REFERENCE_SOURCE) as [after [RUN FRAME]].
  exists after; split; [exact RUN|].
  eapply temp_agree_trans; [exact PUBLIC|].
  eapply temp_agree_weaken; [|eapply temp_agree_trans; [exact SOURCE_FRAME|exact FRAME]].
  intros identifier MEMBER; apply(proj2(loaded_affine_scan_ports_inclusions parameters proposal live)); right; right; exact MEMBER.
Qed.
End CANDIDATE.

Print Assumptions offset_affine_snapshot_word_unique.
Print Assumptions offset_affine_pointer_cache_distinct.
Print Assumptions offset_affine_cached_source_at_snapshot.
Print Assumptions offset_affine_candidate_local.
