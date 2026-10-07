From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightLoopSyntax.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestScanNamespace.
From GuardInterface Require Import GuardInterface ClightMaterializedCheck ClightMaterializedCertificate ClightPrivateScanHost
  ClightQuietDeterminacy ClightLoadedBoundSyntax ClightLoadedSnapshotInsertion ClightLoadedAffineFirstPath ClightLoadedAffineNumericGuard
  ClightLoadedAffineNumericSite ClightLoadedAffineScanSite ClightLoadedAffineScanExecution ClightLoadedAffineScanCertificate
  ClightCheckedTempWrites ClightExpressionHeaderCapture ClightExpressionAffineNumericSite
  ClightLoadedOffsetHeader ClightLoadedOffsetAffineScanSite ClightLoadedOffsetAffineScanExecution
  ClightLoadedOffsetAffineScanCertificate.
Import ListNotations.
Set Implicit Arguments.

Definition offset_affine_scan_raw source parameters live proposal pointer delta
  (numeric : expression_affine_numeric_site source parameters live proposal (signed_load_offset pointer delta)) :=
  Ssequence(materialized_body(expression_numeric_test numeric))(loaded_affine_scan_tail proposal pointer).
Definition loaded_affine_scan_private_writes proposal := affine_proposed_result proposal::
  map(affine_proposal_rename proposal)(affine_nest_controls(affine_proposal_nest proposal)).
Record offset_affine_transfer_site source parameters live proposal pointer delta := {
  offset_transfer_scan : offset_affine_scan_site source parameters live proposal pointer delta;
  offset_transfer_writes : writes_only(loaded_affine_scan_private_writes proposal)
    (offset_affine_scan_raw(offset_scan_numeric offset_transfer_scan))
}.
Definition check_offset_affine_transfer_site source parameters live proposal pointer delta :
  option(offset_affine_transfer_site source parameters live proposal pointer delta).
Proof.
  destruct(check_offset_affine_scan_site source parameters live proposal pointer delta) as [scan|]; [|exact None].
  destruct(check_temp_writes(loaded_affine_scan_private_writes proposal)(offset_affine_scan_raw(offset_scan_numeric scan)))
    eqn:WRITES; [|exact None].
  exact(Some {| offset_transfer_scan:=scan; offset_transfer_writes:=@check_temp_writes_sound _ _ WRITES |}).
Defined.

Lemma offset_affine_scan_private_ports source parameters live proposal pointer delta
  (site : offset_affine_scan_site source parameters live proposal pointer delta) :
  forall identifier, In identifier(loaded_affine_scan_ports parameters proposal live) ->
    ~In identifier(loaded_affine_scan_private_writes proposal).
Proof.
  intros identifier PUBLIC [FLAG|CONTROL].
  - subst identifier; apply(affine_scan_names_flag_private(offset_scan_namespace site)),in_or_app; right; exact PUBLIC.
  - apply in_map_iff in CONTROL as [original [<- MEMBER]].
    apply(proj1(affine_scan_names_private(offset_scan_namespace site) original MEMBER)),in_or_app; right; exact PUBLIC.
Qed.

(* A completed check retains the private cache it established at entry.
   The value is related to the original load, rather than its original temp. *)
Definition offset_affine_scan_entry_relation parameters live proposal pointer delta original checked :=
  exists upper,
    loaded_offset_cached_header pointer delta (affine_proposed_bound proposal)(loaded_affine_scan_prepared proposal original upper) /\
    private_scan_entry_frame(loaded_affine_scan_ports parameters proposal live)
      (loaded_affine_scan_prepared proposal original upper) checked.

Lemma offset_affine_scan_capture_and_raw source parameters live proposal pointer delta
  (site : offset_affine_scan_site source parameters live proposal pointer delta) fe ge locals temps memory after :
  exec_stmt fe ge locals temps memory(offset_affine_scan_body(offset_scan_numeric site)) E0 after memory Out_normal ->
  exists value,
    eval_expr ge locals temps memory(signed_load_offset pointer delta) value /\
    exists trace,
      exec_stmt fe ge locals(PTree.set(affine_proposed_bound proposal) value temps) memory
        (offset_affine_scan_raw(offset_scan_numeric site)) trace after memory Out_normal.
Proof.
  intro RUN; unfold offset_affine_scan_body,expression_numeric_check_code in RUN.
  assert(PREFIX_NORMAL:normal_statement
    (Ssequence(Sset(affine_proposed_bound proposal)(signed_load_offset pointer delta))
      (materialized_body(expression_numeric_test(offset_scan_numeric site))))=true).
  { cbn [normal_statement]; exact(materialized_normal(expression_numeric_test(offset_scan_numeric site))). }
  inversion RUN; subst.
  - match goal with PREFIX:exec_stmt _ _ _ _ _ (Ssequence(Sset _ _) _) _ _ _ _ |- _ => inversion PREFIX; subst end.
    + match goal with CAPTURE:exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion CAPTURE; subst end.
      eexists; split; [eassumption|].
      eexists; unfold offset_affine_scan_raw; eapply exec_Sseq_1; eassumption.
    + match goal with CAPTURE:exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion CAPTURE; subst end; contradiction.
  - match goal with PREFIX:exec_stmt _ _ _ _ _ (Ssequence(Sset _ _) _) _ _ _ _ |- _ =>
      pose proof(@normal_statement_execution fe ge locals _ PREFIX_NORMAL _ _ _ _ _ _ PREFIX); subst end; contradiction.
Qed.

Theorem offset_affine_scan_transfer_execution source parameters live proposal pointer delta
  (site : offset_affine_transfer_site source parameters live proposal pointer delta) fe ge locals temps memory source_after final after :
  exec_stmt fe ge locals temps memory source E0 source_after final Out_normal ->
  exec_stmt fe ge locals temps memory(offset_affine_scan_body(offset_scan_numeric(offset_transfer_scan site)))
    E0 after memory Out_normal ->
  offset_affine_scan_entry_relation parameters live proposal pointer delta(Entry ge locals temps memory)(Entry ge locals after memory).
Proof.
  intros SOURCE CHECK.
  rewrite(expression_numeric_exact(offset_scan_numeric(offset_transfer_scan site))) in SOURCE.
  destruct(signed_expression_completed_header SOURCE) as [first TEST].
  destruct(@signed_expression_test_facts ge locals temps memory (affine_proposed_iterator proposal)
    (signed_load_offset pointer delta) first eq_refl TEST) as [counter [upper [ROW [EVAL FLAG]]]].
  destruct(@offset_affine_scan_capture_and_raw _ _ _ _ _ _ (offset_transfer_scan site) fe ge locals temps memory after CHECK)
    as [value [CAPTURE [trace RAW]]].
  pose proof(proj1(expressions_determinate ge locals temps memory) _ _ CAPTURE _ EVAL) as SAME; subst value.
  destruct(signed_load_offset_inv EVAL) as [block [offset [raw [POINTER [READ UPPER]]]]].
  assert(PRIVATE:pointer<>affine_proposed_bound proposal).
  { intro SAME; apply(expression_numeric_private(offset_scan_numeric(offset_transfer_scan site))),in_or_app; left.
    rewrite(expression_numeric_exact(offset_scan_numeric(offset_transfer_scan site))); rewrite <-SAME; apply(signed_expression_bound_in_scope (affine_proposed_iterator proposal) (signed_load_offset pointer delta) (affine_proposed_body proposal));
    change(pointer=pointer \/ False); left; reflexivity. }
  exists upper; split.
  - exists block,offset,raw; cbn [loaded_affine_scan_prepared entry_temps entry_memory].
    split; [rewrite PTree.gso by exact PRIVATE; exact POINTER|split; [exact READ|rewrite <-UPPER; apply PTree.gss]].
  - repeat split; try reflexivity.
    exact(@structured_temp_frame fe ge locals _ memory _ trace after memory Out_normal
      (loaded_affine_scan_private_writes proposal)(loaded_affine_scan_ports parameters proposal live)
      (offset_transfer_writes site)(offset_affine_scan_private_ports(offset_transfer_scan site)) RAW).
Qed.

Definition offset_affine_scan_transfer_certificate source parameters live proposal pointer delta
  (site : offset_affine_transfer_site source parameters live proposal pointer delta) fe O (observe : fragment_observation -> O -> Prop) :
  guard_certificate(materialized_host fe observe)(materialized_source_completion source)
    (offset_affine_scan_presumption fe parameters proposal pointer delta)
    (offset_affine_scan_entry_relation parameters live proposal pointer delta)
    (offset_affine_scan_entry_relation parameters live proposal pointer delta)(offset_scan_test(offset_transfer_scan site)).
Proof.
  pose(ordinary:=offset_affine_scan_site_certificate(offset_transfer_scan site) fe observe).
  constructor.
  - exact(check_safety ordinary).
  - exact(check_available ordinary).
  - intros entry accepted checked DOMAIN CHECK.
    pose proof(check_sound ordinary entry accepted checked DOMAIN CHECK) as SOUND.
    assert(QUIET:Guard.ClightRegionProgress.quiet_statement source=true).
    { rewrite(expression_numeric_exact(offset_scan_numeric(offset_transfer_scan site)));
        apply offset_affine_numeric_source_quiet with(pointer:=pointer)(delta:=delta)(package:=expression_numeric_package(offset_scan_numeric(offset_transfer_scan site))). }
    destruct(materialized_source_receipt fe QUIET DOMAIN) as [source_after [final SOURCE]].
    destruct CHECK as [after [RUN [TEST SAME]]]; subst checked.
    destruct(@describe_materialized_check_exact _ _ _ (offset_scan_describe(offset_transfer_scan site))) as [BODY CONDITION];
      rewrite BODY in RUN.
    pose proof(@offset_affine_scan_transfer_execution _ _ _ _ _ _ site fe (entry_ge entry)(entry_env entry)(entry_temps entry)
      (entry_memory entry) source_after final after SOURCE RUN) as TRANSFER.
    destruct accepted; [split; [exact(proj1 SOUND)|exact TRANSFER]|exact TRANSFER].
Defined.

Print Assumptions check_offset_affine_transfer_site.
Print Assumptions offset_affine_scan_private_ports.
Print Assumptions offset_affine_scan_capture_and_raw.
Print Assumptions offset_affine_scan_transfer_execution.
Print Assumptions offset_affine_scan_transfer_certificate.
