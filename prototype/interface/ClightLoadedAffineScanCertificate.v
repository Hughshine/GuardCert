From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightProjectedExecution.
From GuardAffineNest Require Import AffineNestSyntax AffineNestGuardPackage.
From GuardInterface Require Import GuardInterface ClightSharedGuard ClightMaterializedCheck ClightMaterializedCertificate
  ClightPrivateScanHost ClightCheckPlanFrame ClightLoadedAffineNumericGuard ClightLoadedAffineNumericSite
  ClightLoadedAffineBodyPrefix ClightLoadedAffineScanSite ClightLoadedAffineScanExecution.
Set Implicit Arguments.

(* This is a checked producer for the existing host/certificate interface.
   Its domain is actual source completion. No numeric, alias, stability,
   cached-loop-completion, or per-body-safety premise is supplied by users. *)
Definition loaded_affine_scan_site_certificate source parameters live proposal pointer
  (site : loaded_affine_scan_site source parameters live proposal pointer)
  fe O (observe : fragment_observation -> O -> Prop) :
  guard_certificate(materialized_host fe observe)(materialized_source_completion source)
    (loaded_affine_scan_presumption fe parameters proposal pointer)
    (private_scan_entry_frame live)(private_scan_entry_frame live)(loaded_scan_test site).
Proof.
  apply materialized_execution_certificate; intros [ge locals temps memory] DOMAIN.
  assert(QUIET:Guard.ClightRegionProgress.quiet_statement source=true).
  { rewrite(loaded_numeric_exact(loaded_scan_numeric site));
      apply affine_loaded_numeric_source_quiet with(package:=loaded_numeric_package(loaded_scan_numeric site)). }
  destruct(@materialized_source_receipt fe source(Entry ge locals temps memory) QUIET DOMAIN)
    as [source_after [final SOURCE]].
  destruct(@loaded_affine_scan_site_execution source parameters live proposal pointer site fe ge locals temps memory
    source_after final SOURCE) as [after [RUN [FRAME [RESULT ACCEPT]]]].
  exists(loaded_affine_scan_flag parameters proposal pointer(Entry ge locals temps memory)),after.
  destruct(@describe_materialized_check_exact _ _ _ (loaded_scan_describe site)) as [BODY CONDITION].
  rewrite BODY,CONDITION; cbn [entry_ge entry_env entry_temps entry_memory].
  split; [exact RUN|split; [apply shared_guard_choice_test; exact RESULT|split; assumption]].
Defined.

(* The semantic premise can be consumed with any actual completed original
   source execution. A fresh cache is hidden from the original observation. *)
Theorem loaded_affine_scan_presumption_cached_source source parameters live proposal pointer
  (site : loaded_affine_scan_site source parameters live proposal pointer) fe ge locals temps memory after final :
  loaded_affine_scan_presumption fe parameters proposal pointer(Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists upper cached_after,
    exec_stmt fe ge locals (PTree.set(affine_proposed_bound proposal)(Vint upper) temps) memory
      (affine_nest_source(affine_proposal_nest proposal)) E0 cached_after final Out_normal /\
    temp_agree live after cached_after.
Proof.
  intros [upper [SNAPSHOT [NUMERIC [ROW [NONNEGATIVE PRESERVE]]]]] SOURCE.
  pose proof(loaded_numeric_private(loaded_scan_numeric site)) as PRIVATE.
  pose proof(loaded_numeric_frameable(loaded_scan_numeric site)) as FRAMEABLE.
  destruct(@structured_execution_temp_transport fe ge locals temps memory source E0 after final Out_normal SOURCE
    (statement_temps source++live)(PTree.set(affine_proposed_bound proposal)(Vint upper) temps)(statement_temps source)
    (@check_plan_frameable_writes source FRAMEABLE)
    ltac:(unfold statement_scope; intros identifier MEMBER; apply in_or_app; left; exact MEMBER)
    (@temp_agree_set _ temps(affine_proposed_bound proposal)(Vint upper) PRIVATE)) as [cached_after [PREPARED FRAME]].
  exists upper,cached_after; split.
  - rewrite(loaded_numeric_exact(loaded_scan_numeric site)) in PREPARED.
    exact(@affine_loaded_body_cached_source _ parameters _ proposal(loaded_numeric_package(loaded_scan_numeric site))
      pointer(loaded_scan_body_names site) fe ge locals(PTree.set(affine_proposed_bound proposal)(Vint upper) temps) memory
      cached_after final SNAPSHOT ROW NONNEGATIVE PRESERVE PREPARED).
  - eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER; apply in_or_app; right; exact MEMBER.
Qed.

Print Assumptions loaded_affine_scan_site_certificate.
Print Assumptions loaded_affine_scan_presumption_cached_source.
