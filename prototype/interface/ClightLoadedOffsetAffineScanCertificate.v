From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightProjectedExecution.
From GuardAffineNest Require Import AffineNestSyntax AffineNestGuardPackage.
From GuardInterface Require Import GuardInterface ClightSharedGuard ClightMaterializedCheck ClightMaterializedCertificate
  ClightPrivateScanHost ClightCheckPlanFrame ClightLoadedAffineNumericGuard ClightLoadedAffineNumericSite
  ClightLoadedAffineBodyPrefix ClightLoadedAffineScanSite ClightLoadedAffineScanExecution
  ClightExpressionAffineNumericSite ClightLoadedOffsetHeader ClightLoadedOffsetAffineBody
  ClightLoadedOffsetAffineCache ClightLoadedOffsetAffineScanSite ClightLoadedOffsetAffineScanExecution
  ClightStrictLoopProgress.
Set Implicit Arguments.

Lemma offset_affine_numeric_source_quiet source parameters live proposal pointer delta
  (package : affine_guard_package source parameters live proposal) :
  Guard.ClightRegionProgress.quiet_statement(expression_affine_numeric_source(signed_load_offset pointer delta) proposal)=true.
Proof.
  destruct(affine_loaded_numeric_body_properties package) as [_ QUIET].
  cbn [expression_affine_numeric_source strict_frontend_loop Guard.ClightRegionProgress.quiet_statement
    Guard.ClightCountedLoop.counter_increment]; rewrite QUIET; reflexivity.
Qed.

(* This is a checked producer for the existing host/certificate interface.
   Its domain is actual source completion. No numeric, alias, stability,
   cached-loop-completion, or per-body-safety premise is supplied by users. *)
Definition offset_affine_scan_site_certificate source parameters live proposal pointer delta
  (site : offset_affine_scan_site source parameters live proposal pointer delta)
  fe O (observe : fragment_observation -> O -> Prop) :
  guard_certificate(materialized_host fe observe)(materialized_source_completion source)
    (offset_affine_scan_presumption fe parameters proposal pointer delta)
    (private_scan_entry_frame live)(private_scan_entry_frame live)(offset_scan_test site).
Proof.
  apply materialized_execution_certificate; intros [ge locals temps memory] DOMAIN.
  assert(QUIET:Guard.ClightRegionProgress.quiet_statement source=true).
  { rewrite(expression_numeric_exact(offset_scan_numeric site));
      apply offset_affine_numeric_source_quiet with(pointer:=pointer)(delta:=delta)(package:=expression_numeric_package(offset_scan_numeric site)). }
  destruct(@materialized_source_receipt fe source(Entry ge locals temps memory) QUIET DOMAIN)
    as [source_after [final SOURCE]].
  destruct(@offset_affine_scan_site_execution source parameters live proposal pointer delta site fe ge locals temps memory
    source_after final SOURCE) as [after [RUN [FRAME [RESULT ACCEPT]]]].
  exists(offset_affine_scan_flag parameters proposal pointer delta(Entry ge locals temps memory)),after.
  destruct(@describe_materialized_check_exact _ _ _ (offset_scan_describe site)) as [BODY CONDITION].
  rewrite BODY,CONDITION; cbn [entry_ge entry_env entry_temps entry_memory].
  split; [exact RUN|split; [apply shared_guard_choice_test; exact RESULT|split; assumption]].
Defined.

(* The semantic premise can be consumed with any actual completed original
   source execution. A fresh cache is hidden from the original observation. *)
Theorem offset_affine_scan_presumption_cached_source source parameters live proposal pointer delta
  (site : offset_affine_scan_site source parameters live proposal pointer delta) fe ge locals temps memory after final :
  offset_affine_scan_presumption fe parameters proposal pointer delta(Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists upper cached_after,
    exec_stmt fe ge locals (PTree.set(affine_proposed_bound proposal)(Vint upper) temps) memory
      (affine_nest_source(affine_proposal_nest proposal)) E0 cached_after final Out_normal /\
    temp_agree live after cached_after.
Proof.
  intros [upper [SNAPSHOT [NUMERIC [ROW [NONNEGATIVE PRESERVE]]]]] SOURCE.
  pose proof(expression_numeric_private(offset_scan_numeric site)) as PRIVATE.
  pose proof(expression_numeric_frameable(offset_scan_numeric site)) as FRAMEABLE.
  destruct(@structured_execution_temp_transport fe ge locals temps memory source E0 after final Out_normal SOURCE
    (statement_temps source++live)(PTree.set(affine_proposed_bound proposal)(Vint upper) temps)(statement_temps source)
    (@check_plan_frameable_writes source FRAMEABLE)
    ltac:(unfold statement_scope; intros identifier MEMBER; apply in_or_app; left; exact MEMBER)
    (@temp_agree_set _ temps(affine_proposed_bound proposal)(Vint upper) PRIVATE)) as [cached_after [PREPARED FRAME]].
  exists upper,cached_after; split.
  - rewrite(expression_numeric_exact(offset_scan_numeric site)) in PREPARED.
    exact(@offset_affine_body_cached_source _ parameters _ proposal(expression_numeric_package(offset_scan_numeric site))
      pointer delta fe ge locals(PTree.set(affine_proposed_bound proposal)(Vint upper) temps) memory
      cached_after final (offset_scan_body_names site) SNAPSHOT ROW NONNEGATIVE PRESERVE PREPARED).
  - eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER; apply in_or_app; right; exact MEMBER.
Qed.

Print Assumptions offset_affine_numeric_source_quiet.
Print Assumptions offset_affine_scan_site_certificate.
Print Assumptions offset_affine_scan_presumption_cached_source.
