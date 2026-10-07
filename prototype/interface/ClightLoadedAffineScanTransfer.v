From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightLoopSyntax.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestScanNamespace.
From GuardInterface Require Import GuardInterface ClightMaterializedCheck ClightMaterializedCertificate ClightPrivateScanHost
  ClightQuietDeterminacy ClightLoadedBoundSyntax ClightLoadedSnapshotInsertion ClightLoadedAffineFirstPath ClightLoadedAffineNumericGuard
  ClightLoadedAffineNumericSite ClightLoadedAffineScanSite ClightLoadedAffineScanExecution ClightLoadedAffineScanCertificate
  ClightCheckedTempWrites.
Import ListNotations.
Set Implicit Arguments.

Definition loaded_affine_scan_raw source parameters live proposal pointer
  (numeric : loaded_affine_numeric_site source parameters live proposal pointer) :=
  Ssequence(materialized_body(loaded_numeric_test numeric))(loaded_affine_scan_tail proposal pointer).
Definition loaded_affine_scan_private_writes proposal := affine_proposed_result proposal::
  map(affine_proposal_rename proposal)(affine_nest_controls(affine_proposal_nest proposal)).
Record loaded_affine_transfer_site source parameters live proposal pointer := {
  loaded_transfer_scan : loaded_affine_scan_site source parameters live proposal pointer;
  loaded_transfer_writes : writes_only(loaded_affine_scan_private_writes proposal)
    (loaded_affine_scan_raw(loaded_scan_numeric loaded_transfer_scan))
}.
Definition check_loaded_affine_transfer_site source parameters live proposal pointer :
  option(loaded_affine_transfer_site source parameters live proposal pointer).
Proof.
  destruct(check_loaded_affine_scan_site source parameters live proposal pointer) as [scan|]; [|exact None].
  destruct(check_temp_writes(loaded_affine_scan_private_writes proposal)(loaded_affine_scan_raw(loaded_scan_numeric scan)))
    eqn:WRITES; [|exact None].
  exact(Some {| loaded_transfer_scan:=scan; loaded_transfer_writes:=@check_temp_writes_sound _ _ WRITES |}).
Defined.

Lemma loaded_affine_scan_private_ports source parameters live proposal pointer
  (site : loaded_affine_scan_site source parameters live proposal pointer) :
  forall identifier, In identifier(loaded_affine_scan_ports parameters proposal live) ->
    ~In identifier(loaded_affine_scan_private_writes proposal).
Proof.
  intros identifier PUBLIC [FLAG|CONTROL].
  - subst identifier; apply(affine_scan_names_flag_private(loaded_scan_namespace site)),in_or_app; right; exact PUBLIC.
  - apply in_map_iff in CONTROL as [original [<- MEMBER]].
    apply(proj1(affine_scan_names_private(loaded_scan_namespace site) original MEMBER)),in_or_app; right; exact PUBLIC.
Qed.

(* A completed check retains the private cache it established at entry.
   The value is related to the original load, rather than its original temp. *)
Definition loaded_affine_scan_entry_relation parameters live proposal pointer original checked :=
  exists upper,
    affine_loaded_numeric_snapshot pointer proposal(loaded_affine_scan_prepared proposal original upper) /\
    private_scan_entry_frame(loaded_affine_scan_ports parameters proposal live)
      (loaded_affine_scan_prepared proposal original upper) checked.

Lemma loaded_affine_scan_capture_and_raw source parameters live proposal pointer
  (site : loaded_affine_scan_site source parameters live proposal pointer) fe ge locals temps memory after :
  exec_stmt fe ge locals temps memory(loaded_affine_scan_body(loaded_scan_numeric site)) E0 after memory Out_normal ->
  exists value,
    eval_expr ge locals temps memory(signed_load pointer) value /\
    exists trace,
      exec_stmt fe ge locals(PTree.set(affine_proposed_bound proposal) value temps) memory
        (loaded_affine_scan_raw(loaded_scan_numeric site)) trace after memory Out_normal.
Proof.
  intro RUN; unfold loaded_affine_scan_body,loaded_numeric_check_code in RUN.
  assert(PREFIX_NORMAL:normal_statement
    (Ssequence(Sset(affine_proposed_bound proposal)(signed_load pointer))
      (materialized_body(loaded_numeric_test(loaded_scan_numeric site))))=true).
  { cbn [normal_statement]; exact(materialized_normal(loaded_numeric_test(loaded_scan_numeric site))). }
  inversion RUN; subst.
  - match goal with PREFIX:exec_stmt _ _ _ _ _ (Ssequence(Sset _ _) _) _ _ _ _ |- _ => inversion PREFIX; subst end.
    + match goal with CAPTURE:exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion CAPTURE; subst end.
      eexists; split; [eassumption|].
      eexists; unfold loaded_affine_scan_raw; eapply exec_Sseq_1; eassumption.
    + match goal with CAPTURE:exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion CAPTURE; subst end; contradiction.
  - match goal with PREFIX:exec_stmt _ _ _ _ _ (Ssequence(Sset _ _) _) _ _ _ _ |- _ =>
      pose proof(@normal_statement_execution fe ge locals _ PREFIX_NORMAL _ _ _ _ _ _ PREFIX); subst end; contradiction.
Qed.

Theorem loaded_affine_scan_transfer_execution source parameters live proposal pointer
  (site : loaded_affine_transfer_site source parameters live proposal pointer) fe ge locals temps memory source_after final after :
  exec_stmt fe ge locals temps memory source E0 source_after final Out_normal ->
  exec_stmt fe ge locals temps memory(loaded_affine_scan_body(loaded_scan_numeric(loaded_transfer_scan site)))
    E0 after memory Out_normal ->
  loaded_affine_scan_entry_relation parameters live proposal pointer(Entry ge locals temps memory)(Entry ge locals after memory).
Proof.
  intros SOURCE CHECK.
  rewrite(loaded_numeric_exact(loaded_scan_numeric(loaded_transfer_scan site))) in SOURCE.
  destruct(@loaded_header_snapshot_read fe ge locals temps memory(affine_proposed_iterator proposal) pointer
    (affine_proposed_body proposal) _ _ _ _ SOURCE) as [upper EVAL].
  destruct(@loaded_affine_scan_capture_and_raw _ _ _ _ _ (loaded_transfer_scan site) fe ge locals temps memory after CHECK)
    as [value [CAPTURE [trace RAW]]].
  pose proof(proj1(expressions_determinate ge locals temps memory) _ _ CAPTURE _ EVAL) as SAME; subst value.
  destruct(signed_load_inv EVAL) as [block [offset [POINTER READ]]].
  assert(PRIVATE:pointer<>affine_proposed_bound proposal).
  { intro SAME; apply(loaded_numeric_private(loaded_scan_numeric(loaded_transfer_scan site))),in_or_app; left.
    rewrite(loaded_numeric_exact(loaded_scan_numeric(loaded_transfer_scan site))); rewrite <-SAME; apply loaded_bound_pointer_in_scope. }
  exists upper; split.
  - exists block,offset,upper; cbn [loaded_affine_scan_prepared entry_temps entry_memory].
    split; [rewrite PTree.gso by exact PRIVATE; exact POINTER|split; [exact READ|apply PTree.gss]].
  - repeat split; try reflexivity.
    exact(@structured_temp_frame fe ge locals _ memory _ trace after memory Out_normal
      (loaded_affine_scan_private_writes proposal)(loaded_affine_scan_ports parameters proposal live)
      (loaded_transfer_writes site)(loaded_affine_scan_private_ports(loaded_transfer_scan site)) RAW).
Qed.

Definition loaded_affine_scan_transfer_certificate source parameters live proposal pointer
  (site : loaded_affine_transfer_site source parameters live proposal pointer) fe O (observe : fragment_observation -> O -> Prop) :
  guard_certificate(materialized_host fe observe)(materialized_source_completion source)
    (loaded_affine_scan_presumption fe parameters proposal pointer)
    (loaded_affine_scan_entry_relation parameters live proposal pointer)
    (loaded_affine_scan_entry_relation parameters live proposal pointer)(loaded_scan_test(loaded_transfer_scan site)).
Proof.
  pose(ordinary:=loaded_affine_scan_site_certificate(loaded_transfer_scan site) fe observe).
  constructor.
  - exact(check_safety ordinary).
  - exact(check_available ordinary).
  - intros entry accepted checked DOMAIN CHECK.
    pose proof(check_sound ordinary entry accepted checked DOMAIN CHECK) as SOUND.
    assert(QUIET:Guard.ClightRegionProgress.quiet_statement source=true).
    { rewrite(loaded_numeric_exact(loaded_scan_numeric(loaded_transfer_scan site)));
        apply affine_loaded_numeric_source_quiet with(package:=loaded_numeric_package(loaded_scan_numeric(loaded_transfer_scan site))). }
    destruct(materialized_source_receipt fe QUIET DOMAIN) as [source_after [final SOURCE]].
    destruct CHECK as [after [RUN [TEST SAME]]]; subst checked.
    destruct(@describe_materialized_check_exact _ _ _ (loaded_scan_describe(loaded_transfer_scan site))) as [BODY CONDITION];
      rewrite BODY in RUN.
    pose proof(@loaded_affine_scan_transfer_execution _ _ _ _ _ site fe (entry_ge entry)(entry_env entry)(entry_temps entry)
      (entry_memory entry) source_after final after SOURCE RUN) as TRANSFER.
    destruct accepted; [split; [exact(proj1 SOUND)|exact TRANSFER]|exact TRANSFER].
Defined.

Print Assumptions check_loaded_affine_transfer_site.
Print Assumptions loaded_affine_scan_private_ports.
Print Assumptions loaded_affine_scan_capture_and_raw.
Print Assumptions loaded_affine_scan_transfer_execution.
Print Assumptions loaded_affine_scan_transfer_certificate.
