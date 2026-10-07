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
  ClightAffineNestMaterialized.
Import ListNotations.
Set Implicit Arguments.

Definition loaded_affine_multi_guard_body source parameters live allocated proposal pointer
  (transfer : loaded_affine_transfer_site source parameters live proposal pointer)
  (package : affine_multi_static_package (affine_nest_source(affine_proposal_nest proposal)) parameters
    (loaded_affine_scan_ports parameters proposal live) allocated proposal) :=
  Ssequence (loaded_affine_scan_body(loaded_scan_numeric(loaded_transfer_scan transfer)))
    (Sifthenelse(shared_guard_choice(affine_proposed_result proposal))(affine_multi_alias_only_code package) Sskip).

Record loaded_affine_multi_site source parameters live allocated proposal pointer := {
  loaded_multi_transfer : loaded_affine_transfer_site source parameters live proposal pointer;
  loaded_multi_package : affine_multi_static_package (affine_nest_source(affine_proposal_nest proposal)) parameters
    (loaded_affine_scan_ports parameters proposal live) allocated proposal;
  loaded_multi_cached_scope : statement_scope (loaded_affine_scan_ports parameters proposal live)
    (affine_nest_source(affine_proposal_nest proposal));
  loaded_multi_test : materialized_check;
  loaded_multi_describe : describe_materialized_check
    (loaded_affine_multi_guard_body loaded_multi_transfer loaded_multi_package)
    (shared_guard_choice(affine_proposed_result proposal))=Some loaded_multi_test
}.

Definition check_loaded_affine_multi_site source parameters live allocated proposal pointer :
  option(loaded_affine_multi_site source parameters live allocated proposal pointer).
Proof.
  destruct(check_loaded_affine_transfer_site source parameters live proposal pointer) as [transfer|]; [|exact None].
  destruct(check_affine_multi_static_package (affine_nest_source(affine_proposal_nest proposal)) parameters
    (loaded_affine_scan_ports parameters proposal live) allocated proposal) as [package|]; [|exact None].
  destruct(affine_statement_scope_check(loaded_affine_scan_ports parameters proposal live)
    (affine_nest_source(affine_proposal_nest proposal))) eqn:SCOPE; [|exact None].
  destruct(describe_materialized_check(loaded_affine_multi_guard_body transfer package)
    (shared_guard_choice(affine_proposed_result proposal))) as [test|] eqn:TEST; [|exact None].
  exact(Some {| loaded_multi_transfer:=transfer; loaded_multi_package:=package;
    loaded_multi_cached_scope:=@affine_statement_scope_check_sound _ _ SCOPE;
    loaded_multi_test:=test; loaded_multi_describe:=TEST |}).
Defined.

Lemma loaded_affine_entry_relation_frame parameters live proposal pointer original checked later :
  loaded_affine_scan_entry_relation parameters live proposal pointer original checked ->
  private_scan_entry_frame(loaded_affine_scan_ports parameters proposal live) checked later ->
  loaded_affine_scan_entry_relation parameters live proposal pointer original later.
Proof.
  intros [upper [SNAPSHOT [GE [ENV [MEMORY TEMPS]]]]] [NEXT_GE [NEXT_ENV [NEXT_MEMORY NEXT_TEMPS]]].
  exists upper; split; [exact SNAPSHOT|].
  repeat split; try congruence; eapply temp_agree_trans; eassumption.
Qed.

(** The alias scan is executed only after stability has supplied an actual
    cached-source execution. Its safety domain is never a caller hypothesis. *)
Theorem loaded_affine_multi_guard_execution source parameters live allocated proposal pointer
  (site : loaded_affine_multi_site source parameters live allocated proposal pointer)
  fe ge locals temps memory source_after final :
  exec_stmt fe ge locals temps memory source E0 source_after final Out_normal ->
  exists accepted after,
    exec_stmt fe ge locals temps memory (loaded_affine_multi_guard_body(loaded_multi_transfer site)(loaded_multi_package site))
      E0 after memory Out_normal /\
    expression_test(shared_guard_choice(affine_proposed_result proposal))(Entry ge locals after memory) accepted /\
    loaded_affine_scan_entry_relation parameters live proposal pointer(Entry ge locals temps memory)(Entry ge locals after memory) /\
    (accepted=true -> loaded_affine_candidate_presumption fe parameters live proposal pointer(Entry ge locals temps memory)).
Proof.
  intro SOURCE.
  destruct(@loaded_affine_scan_site_execution _ _ _ _ _ (loaded_transfer_scan(loaded_multi_transfer site))
    fe ge locals temps memory source_after final SOURCE) as [reference [SCAN [_ [FLAG STABILITY]]]].
  pose proof(@loaded_affine_scan_transfer_execution _ _ _ _ _ (loaded_multi_transfer site)
    fe ge locals temps memory source_after final reference SOURCE SCAN) as ENTRY.
  pose proof(@shared_guard_choice_test ge locals reference memory(affine_proposed_result proposal)
    (loaded_affine_scan_flag parameters proposal pointer(Entry ge locals temps memory)) FLAG) as TEST.
  destruct TEST as [value [EVAL BOOL]].
  destruct(loaded_affine_scan_flag parameters proposal pointer(Entry ge locals temps memory)) eqn:ACCEPT.
  - specialize(STABILITY eq_refl).
    destruct ENTRY as [upper [SNAPSHOT [GE [ENV [MEMORY FRAME]]]]].
    destruct(@loaded_affine_cached_source_at_snapshot _ _ _ _ _ (loaded_transfer_scan(loaded_multi_transfer site))
      fe ge locals temps memory source_after final upper STABILITY SNAPSHOT SOURCE) as [cached_after [CACHED PUBLIC]].
    destruct(@structured_execution_temp_transport fe ge locals _ memory _ E0 cached_after final Out_normal CACHED
      (loaded_affine_scan_ports parameters proposal live) reference
      (affine_nest_controls(affine_proposal_nest proposal))
      (affine_materialized_source_writes(affine_multi_guard(loaded_multi_package site)))
      (loaded_multi_cached_scope site) FRAME) as [reference_after [REFERENCE_SOURCE _]].
    assert(NUMERIC:affine_package_guard_flag parameters proposal(Entry ge locals reference memory)=true).
    { destruct STABILITY as [word [WORD_SNAPSHOT [[NUMERIC MATH] REST]]].
      assert(SAME:word=upper).
      { eapply loaded_affine_snapshot_word_unique;
          [exact(loaded_affine_pointer_cache_distinct(loaded_transfer_scan(loaded_multi_transfer site)))|
           exact WORD_SNAPSHOT|exact SNAPSHOT]. }
      subst word.
      rewrite (@affine_package_guard_flag_frame _ _ _ _ (affine_multi_guard(loaded_multi_package site))
        ge locals memory (PTree.set(affine_proposed_bound proposal)(Vint upper) temps) reference).
      - exact NUMERIC.
      - intros identifier MEMBER; apply FRAME.
        destruct(loaded_affine_scan_ports_inclusions parameters proposal live) as [PARAMETERS ROOT].
        apply in_app_or in MEMBER as [MEMBER|MEMBER]; [apply PARAMETERS; exact MEMBER|].
        apply ROOT; cbn [List.In] in *; tauto. }
    destruct(@affine_multi_alias_only_execution _ _ _ _ _ (loaded_multi_package site) fe ge locals reference memory
      reference_after final REFERENCE_SOURCE NUMERIC FLAG) as [after [ALIAS [AFTER RESULT]]].
    exists(affine_multi_guard_flag parameters proposal(Entry ge locals reference memory)),after.
    split.
    + unfold loaded_affine_multi_guard_body; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact SCAN|].
      eapply exec_Sifthenelse with(v1:=value)(b:=true); eassumption.
    + split; [apply shared_guard_choice_test; exact RESULT|split].
      * eapply loaded_affine_entry_relation_frame with(checked:=Entry ge locals reference memory).
        -- exists upper; split; [exact SNAPSHOT|repeat split; try reflexivity; exact FRAME].
        -- repeat split; try reflexivity; exact AFTER.
      * intro PASS; split; [exact STABILITY|exists upper,reference; auto].
  - exists false,reference; split.
    + unfold loaded_affine_multi_guard_body; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact SCAN|].
      eapply exec_Sifthenelse with(v1:=value)(b:=false); [exact EVAL|exact BOOL|apply exec_Sskip].
    + split; [exists value; auto|split; [exact ENTRY|discriminate]].
Qed.

Definition loaded_affine_multi_guard_certificate source parameters live allocated proposal pointer
  (site : loaded_affine_multi_site source parameters live allocated proposal pointer)
  fe O (observe : fragment_observation -> O -> Prop) :
  guard_certificate(materialized_host fe observe)(materialized_source_completion source)
    (loaded_affine_candidate_presumption fe parameters live proposal pointer)
    (loaded_affine_scan_entry_relation parameters live proposal pointer)
    (loaded_affine_scan_entry_relation parameters live proposal pointer)(loaded_multi_test site).
Proof.
  apply materialized_entry_execution_certificate; intros [ge locals temps memory] DOMAIN.
  assert(QUIET:Guard.ClightRegionProgress.quiet_statement source=true).
  { rewrite(loaded_numeric_exact(loaded_scan_numeric(loaded_transfer_scan(loaded_multi_transfer site))));
      apply affine_loaded_numeric_source_quiet with
        (package:=loaded_numeric_package(loaded_scan_numeric(loaded_transfer_scan(loaded_multi_transfer site)))). }
  destruct(@materialized_source_receipt fe source(Entry ge locals temps memory) QUIET DOMAIN) as [source_after [final SOURCE]].
  destruct(@loaded_affine_multi_guard_execution _ _ _ _ _ _ site fe ge locals temps memory source_after final SOURCE)
    as [accepted [after [RUN [TEST [ENTRY PREMISE]]]]].
  exists accepted,after.
  destruct(@describe_materialized_check_exact _ _ _ (loaded_multi_describe site)) as [BODY CONDITION].
  rewrite BODY,CONDITION; cbn [entry_ge entry_env entry_temps entry_memory].
  split; [exact RUN|split; [exact TEST|]].
  destruct accepted; [split; [apply PREMISE; reflexivity|exact ENTRY]|exact ENTRY].
Defined.

Print Assumptions check_loaded_affine_multi_site.
Print Assumptions loaded_affine_entry_relation_frame.
Print Assumptions loaded_affine_multi_guard_execution.
Print Assumptions loaded_affine_multi_guard_certificate.
