From Stdlib Require Import List.
From compcert.lib Require Import Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardAffineNest Require Import AffineNestSyntax AffineNestGuardPackage AffineNestMultiPresumption.
From GuardInterface Require Import GuardInterface ClightNestedConstantSite ClightNestedConstantMultiSite
  ClightNestedConstantMultiExecution ClightNestedConstantMultiCertificate ClightNestedInvariantMulti
  ClightPrivateScanHost ClightSharedGuard ClightMaterializedCheck ClightMaterializedCertificate
  ClightMaterializedEntryCertificate ClightQuietDeterminacy.
Set Implicit Arguments.

Record ncs_invariant_stability_site source parameters live allocated proposal shape := NCSInvariantStabilitySite {
  ncs_invariant_stability_core : ncs_multi_site source parameters live allocated proposal shape;
  ncs_invariant_stability_test : materialized_check;
  ncs_invariant_stability_describe : describe_materialized_check (ncs_invariant_stability_multi_body ncs_invariant_stability_core)
    (shared_guard_choice (affine_proposed_result proposal)) = Some ncs_invariant_stability_test
}.

(** The same checked source/model package is consumed. The choice of a
    sufficient guard is internal; users supply no execution/model callbacks. *)
Definition check_ncs_invariant_stability_site source parameters live allocated proposal shape :
  option (ncs_invariant_stability_site source parameters live allocated proposal shape).
Proof.
  destruct (check_ncs_multi_site source parameters live allocated proposal shape) as [core|]; [|exact None].
  destruct (describe_materialized_check (ncs_invariant_stability_multi_body core)
    (shared_guard_choice (affine_proposed_result proposal))) as [test|] eqn:DESCRIBE; [|exact None].
  exact (Some (@NCSInvariantStabilitySite source parameters live allocated proposal shape core test DESCRIBE)).
Defined.

Section CERTIFICATE.
Variables source : statement.
Variables parameters live allocated : list ident.
Variable proposal : affine_guard_proposal.
Variable shape : nested_constant_shape.
Variable site : ncs_invariant_stability_site source parameters live allocated proposal shape.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Let core := ncs_invariant_stability_core site.
Let ports := ncs_ports source parameters live shape.
Let scope := ncs_scope source live.

Theorem ncs_invariant_stability_anchor ge locals original memory original_after final checked
  (SOURCE : exec_stmt fe ge locals original memory source E0 original_after final Out_normal)
  (receipt : ncs_invariant_stability_multi_receipt core fe ge locals original memory original_after final checked) :
  checked!(affine_proposed_result proposal) = Some (memory_boolean_word true) ->
  ncs_candidate_presumption source parameters live proposal shape fe (Entry ge locals original memory) /\
  ncs_accepted_entry source parameters live proposal shape fe
    (Entry ge locals original memory) (Entry ge locals checked memory).
Proof.
  intro ACCEPT.
  destruct (ncs_invariant_stability_multi_accept receipt ACCEPT) as [reference [model_after [FRAME [ALIAS [MODEL PUBLIC]]]]].
  assert (ANCHOR : ncs_model_anchor source parameters live proposal shape fe
    (Entry ge locals original memory) (Entry ge locals reference memory)).
  { split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [exact ALIAS|]]]].
    intros other_after other_final OTHER.
    destruct (@quiet_execution_determinate fe ge locals original memory source E0 original_after final Out_normal
      SOURCE (ncs_multi_source_quiet core) E0 other_after other_final Out_normal OTHER)
      as [_ [AFTER [FINAL _]]].
    subst other_after other_final; exists model_after; split; assumption. }
  split.
  - exists (Entry ge locals reference memory); exact ANCHOR.
  - split; [repeat split; try reflexivity; exact (ncs_invariant_stability_multi_public receipt)|].
    exists (Entry ge locals reference memory); split; [exact ANCHOR|].
    repeat split; try reflexivity; exact FRAME.
Qed.

Definition ncs_invariant_stability_guard_certificate {O : Type} (observe : fragment_observation -> O -> Prop) :
  guard_certificate (materialized_host fe observe) (materialized_source_completion source)
    (ncs_candidate_presumption source parameters live proposal shape fe)
    (ncs_accepted_entry source parameters live proposal shape fe) (private_scan_entry_frame scope)
    (ncs_invariant_stability_test site).
Proof.
  apply materialized_entry_execution_certificate.
  intros entry DOMAIN.
  destruct (materialized_source_receipt fe (ncs_multi_source_quiet core) DOMAIN) as [original_after [final SOURCE]].
  destruct entry as [ge locals original memory]; cbn [entry_ge entry_env entry_temps entry_memory] in SOURCE.
  destruct (ncs_invariant_stability_multi_execution core SOURCE) as [checked RECEIPT].
  destruct (ncs_invariant_stability_multi_boolean RECEIPT) as [accepted FLAG].
  destruct (@describe_materialized_check_exact _ _ _ (ncs_invariant_stability_describe site)) as [BODY CONDITION].
  exists accepted, checked; split.
  - rewrite BODY; exact (ncs_invariant_stability_multi_run RECEIPT).
  - split.
    + rewrite CONDITION; apply shared_guard_choice_test; exact FLAG.
    + destruct accepted.
      * eapply ncs_invariant_stability_anchor; eassumption.
      * repeat split; try reflexivity; exact (ncs_invariant_stability_multi_public RECEIPT).
Defined.
End CERTIFICATE.

Print Assumptions check_ncs_invariant_stability_site.
Print Assumptions ncs_invariant_stability_anchor.
Print Assumptions ncs_invariant_stability_guard_certificate.
