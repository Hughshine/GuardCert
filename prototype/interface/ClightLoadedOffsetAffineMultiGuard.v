From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightProjectedExecution.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestPackageGuard AffineNestShadowTransport
  AffineNestMultiStaticPackage AffineNestMultiPresumption AffineNestMultiGuardExecution.
From GuardAffineNest Require Import AffineNestGuardFactTransport AffineNestAliasOnlyGuard.
From GuardInterface Require Import GuardInterface ClightSharedGuard ClightMaterializedCheck ClightMaterializedCertificate
  ClightMaterializedEntryCertificate ClightPrivateScanHost ClightLoadedAffineNumericGuard ClightLoadedAffineNumericSite
  ClightLoadedAffineScanSite ClightLoadedAffineScanExecution ClightLoadedAffineScanTransfer ClightLoadedAffineCandidate
  ClightAffineNestMaterialized ClightExpressionAffineNumericSite ClightLoadedOffsetAffineScanSite
  ClightLoadedOffsetAffineScanExecution ClightLoadedOffsetAffineScanCertificate ClightLoadedOffsetAffineScanTransfer
  ClightLoadedOffsetAffineCandidate.
Import ListNotations.
Set Implicit Arguments.

Definition offset_affine_multi_guard_body source parameters live allocated proposal pointer delta
  (transfer : offset_affine_transfer_site source parameters live proposal pointer delta)
  (package : affine_multi_static_package (affine_nest_source(affine_proposal_nest proposal)) parameters
    (loaded_affine_scan_ports parameters proposal live) allocated proposal) :=
  Ssequence (offset_affine_scan_body(offset_scan_numeric(offset_transfer_scan transfer)))
    (Sifthenelse(shared_guard_choice(affine_proposed_result proposal))(affine_multi_alias_only_code package) Sskip).

Record offset_affine_multi_site source parameters live allocated proposal pointer delta := {
  offset_multi_transfer : offset_affine_transfer_site source parameters live proposal pointer delta;
  offset_multi_package : affine_multi_static_package (affine_nest_source(affine_proposal_nest proposal)) parameters
    (loaded_affine_scan_ports parameters proposal live) allocated proposal;
  offset_multi_cached_scope : statement_scope (loaded_affine_scan_ports parameters proposal live)
    (affine_nest_source(affine_proposal_nest proposal));
  offset_multi_test : materialized_check;
  offset_multi_describe : describe_materialized_check
    (offset_affine_multi_guard_body offset_multi_transfer offset_multi_package)
    (shared_guard_choice(affine_proposed_result proposal))=Some offset_multi_test
}.

Definition check_offset_affine_multi_site source parameters live allocated proposal pointer delta :
  option(offset_affine_multi_site source parameters live allocated proposal pointer delta).
Proof.
  destruct(check_offset_affine_transfer_site source parameters live proposal pointer delta) as [transfer|]; [|exact None].
  destruct(check_affine_multi_static_package (affine_nest_source(affine_proposal_nest proposal)) parameters
    (loaded_affine_scan_ports parameters proposal live) allocated proposal) as [package|]; [|exact None].
  destruct(affine_statement_scope_check(loaded_affine_scan_ports parameters proposal live)
    (affine_nest_source(affine_proposal_nest proposal))) eqn:SCOPE; [|exact None].
  destruct(describe_materialized_check(offset_affine_multi_guard_body transfer package)
    (shared_guard_choice(affine_proposed_result proposal))) as [test|] eqn:TEST; [|exact None].
  exact(Some {| offset_multi_transfer:=transfer; offset_multi_package:=package;
    offset_multi_cached_scope:=@affine_statement_scope_check_sound _ _ SCOPE;
    offset_multi_test:=test; offset_multi_describe:=TEST |}).
Defined.

Lemma offset_affine_entry_relation_frame parameters live proposal pointer delta original checked later :
  offset_affine_scan_entry_relation parameters live proposal pointer delta original checked ->
  private_scan_entry_frame(loaded_affine_scan_ports parameters proposal live) checked later ->
  offset_affine_scan_entry_relation parameters live proposal pointer delta original later.
Proof.
  intros [upper [SNAPSHOT [GE [ENV [MEMORY TEMPS]]]]] [NEXT_GE [NEXT_ENV [NEXT_MEMORY NEXT_TEMPS]]].
  exists upper; split; [exact SNAPSHOT|].
  repeat split; try congruence; eapply temp_agree_trans; eassumption.
Qed.

(** The alias scan is executed only after stability has supplied an actual
    cached-source execution. Its safety domain is never a caller hypothesis. *)
Theorem offset_affine_multi_guard_execution source parameters live allocated proposal pointer delta
  (site : offset_affine_multi_site source parameters live allocated proposal pointer delta)
  fe ge locals temps memory source_after final :
  exec_stmt fe ge locals temps memory source E0 source_after final Out_normal ->
  exists accepted after,
    exec_stmt fe ge locals temps memory (offset_affine_multi_guard_body(offset_multi_transfer site)(offset_multi_package site))
      E0 after memory Out_normal /\
    expression_test(shared_guard_choice(affine_proposed_result proposal))(Entry ge locals after memory) accepted /\
    offset_affine_scan_entry_relation parameters live proposal pointer delta(Entry ge locals temps memory)(Entry ge locals after memory) /\
    (accepted=true -> offset_affine_candidate_presumption fe parameters live proposal pointer delta(Entry ge locals temps memory)).
Proof.
  intro SOURCE.
  destruct(@offset_affine_scan_site_execution _ _ _ _ _ _ (offset_transfer_scan(offset_multi_transfer site))
    fe ge locals temps memory source_after final SOURCE) as [reference [SCAN [_ [FLAG STABILITY]]]].
  pose proof(@offset_affine_scan_transfer_execution _ _ _ _ _ _ (offset_multi_transfer site)
    fe ge locals temps memory source_after final reference SOURCE SCAN) as ENTRY.
  pose proof(@shared_guard_choice_test ge locals reference memory(affine_proposed_result proposal)
    (offset_affine_scan_flag parameters proposal pointer delta(Entry ge locals temps memory)) FLAG) as TEST.
  destruct TEST as [value [EVAL BOOL]].
  destruct(offset_affine_scan_flag parameters proposal pointer delta(Entry ge locals temps memory)) eqn:ACCEPT.
  - specialize(STABILITY eq_refl).
    destruct ENTRY as [upper [SNAPSHOT [GE [ENV [MEMORY FRAME]]]]].
    destruct(@offset_affine_cached_source_at_snapshot _ _ _ _ _ _ (offset_transfer_scan(offset_multi_transfer site))
      fe ge locals temps memory source_after final upper STABILITY SNAPSHOT SOURCE) as [cached_after [CACHED PUBLIC]].
    destruct(@structured_execution_temp_transport fe ge locals _ memory _ E0 cached_after final Out_normal CACHED
      (loaded_affine_scan_ports parameters proposal live) reference
      (affine_nest_controls(affine_proposal_nest proposal))
      (affine_materialized_source_writes(affine_multi_guard(offset_multi_package site)))
      (offset_multi_cached_scope site) FRAME) as [reference_after [REFERENCE_SOURCE _]].
    assert(NUMERIC:affine_package_guard_flag parameters proposal(Entry ge locals reference memory)=true).
    { destruct STABILITY as [word [WORD_SNAPSHOT [[NUMERIC MATH] REST]]].
      assert(SAME:word=upper).
      { eapply offset_affine_snapshot_word_unique;
          [exact(offset_affine_pointer_cache_distinct(offset_transfer_scan(offset_multi_transfer site)))|
           exact WORD_SNAPSHOT|exact SNAPSHOT]. }
      subst word.
      rewrite (@affine_package_guard_flag_frame _ _ _ _ (affine_multi_guard(offset_multi_package site))
        ge locals memory (PTree.set(affine_proposed_bound proposal)(Vint upper) temps) reference).
      - exact NUMERIC.
      - intros identifier MEMBER; apply FRAME.
        destruct(loaded_affine_scan_ports_inclusions parameters proposal live) as [PARAMETERS ROOT].
        apply in_app_or in MEMBER as [MEMBER|MEMBER]; [apply PARAMETERS; exact MEMBER|].
        apply ROOT; cbn [List.In] in *; tauto. }
    destruct(@affine_multi_alias_only_execution _ _ _ _ _ (offset_multi_package site) fe ge locals reference memory
      reference_after final REFERENCE_SOURCE NUMERIC FLAG) as [after [ALIAS [AFTER RESULT]]].
    exists(affine_multi_guard_flag parameters proposal(Entry ge locals reference memory)),after.
    split.
    + unfold offset_affine_multi_guard_body; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact SCAN|].
      eapply exec_Sifthenelse with(v1:=value)(b:=true); eassumption.
    + split; [apply shared_guard_choice_test; exact RESULT|split].
      * eapply offset_affine_entry_relation_frame with(checked:=Entry ge locals reference memory).
        -- exists upper; split; [exact SNAPSHOT|repeat split; try reflexivity; exact FRAME].
        -- repeat split; try reflexivity; exact AFTER.
      * intro PASS; split; [exact STABILITY|exists upper,reference; auto].
  - exists false,reference; split.
    + unfold offset_affine_multi_guard_body; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact SCAN|].
      eapply exec_Sifthenelse with(v1:=value)(b:=false); [exact EVAL|exact BOOL|apply exec_Sskip].
    + split; [exists value; auto|split; [exact ENTRY|discriminate]].
Qed.

Definition offset_affine_multi_guard_certificate source parameters live allocated proposal pointer delta
  (site : offset_affine_multi_site source parameters live allocated proposal pointer delta)
  fe O (observe : fragment_observation -> O -> Prop) :
  guard_certificate(materialized_host fe observe)(materialized_source_completion source)
    (offset_affine_candidate_presumption fe parameters live proposal pointer delta)
    (offset_affine_scan_entry_relation parameters live proposal pointer delta)
    (offset_affine_scan_entry_relation parameters live proposal pointer delta)(offset_multi_test site).
Proof.
  apply materialized_entry_execution_certificate; intros [ge locals temps memory] DOMAIN.
  assert(QUIET:Guard.ClightRegionProgress.quiet_statement source=true).
  { rewrite(expression_numeric_exact(offset_scan_numeric(offset_transfer_scan(offset_multi_transfer site))));
      apply offset_affine_numeric_source_quiet with(pointer:=pointer)(delta:=delta)
        (package:=expression_numeric_package(offset_scan_numeric(offset_transfer_scan(offset_multi_transfer site)))). }
  destruct(@materialized_source_receipt fe source(Entry ge locals temps memory) QUIET DOMAIN) as [source_after [final SOURCE]].
  destruct(@offset_affine_multi_guard_execution _ _ _ _ _ _ _ site fe ge locals temps memory source_after final SOURCE)
    as [accepted [after [RUN [TEST [ENTRY PREMISE]]]]].
  exists accepted,after.
  destruct(@describe_materialized_check_exact _ _ _ (offset_multi_describe site)) as [BODY CONDITION].
  rewrite BODY,CONDITION; cbn [entry_ge entry_env entry_temps entry_memory].
  split; [exact RUN|split; [exact TEST|]].
  destruct accepted; [split; [apply PREMISE; reflexivity|exact ENTRY]|exact ENTRY].
Defined.

Print Assumptions check_offset_affine_multi_site.
Print Assumptions offset_affine_entry_relation_frame.
Print Assumptions offset_affine_multi_guard_execution.
Print Assumptions offset_affine_multi_guard_certificate.
