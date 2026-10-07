From Stdlib Require Import List.
From compcert.lib Require Import Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardAffineNest Require Import AffineNestSyntax AffineNestGuardPackage AffineNestMultiPresumption.
From GuardInterface Require Import GuardInterface ClightNestedConstantSite ClightNestedConstantMultiSite
  ClightNestedConstantMultiExecution ClightPrivateScanHost ClightSharedGuard ClightMaterializedCheck
  ClightMaterializedCertificate ClightMaterializedEntryCertificate ClightQuietDeterminacy.
Set Implicit Arguments.

Section CERTIFICATE.
Variables source : statement.
Variables parameters live allocated : list ident.
Variable proposal : affine_guard_proposal.
Variable shape : nested_constant_shape.
Variable site : ncs_multi_site source parameters live allocated proposal shape.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Let ports:=ncs_ports source parameters live shape.
Let scope:=ncs_scope source live.

(** The private snapshot is a witness produced by actual check execution.
    Its model bridge applies to every normally completed source execution,
    rather than to an optimizer-supplied semantic callback. *)
Definition ncs_model_anchor entry reference :=
  entry_ge reference=entry_ge entry /\ entry_env reference=entry_env entry /\
  entry_memory reference=entry_memory entry /\
  affine_multi_guard_flag parameters proposal reference=true /\
  forall original_after final,
    exec_stmt fe (entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
      source E0 original_after final Out_normal -> exists model_after,
    exec_stmt fe (entry_ge reference)(entry_env reference)(entry_temps reference)(entry_memory reference)
      (ncs_model shape) E0 model_after final Out_normal /\ temp_agree scope original_after model_after.

Definition ncs_candidate_presumption entry := exists reference,ncs_model_anchor entry reference.
Definition ncs_accepted_entry entry checked :=
  private_scan_entry_frame scope entry checked /\ exists reference,
    ncs_model_anchor entry reference /\ private_scan_entry_frame ports reference checked.

Theorem ncs_multi_anchor fe_ge locals original memory original_after final checked
  (SOURCE:exec_stmt fe fe_ge locals original memory source E0 original_after final Out_normal)
  (receipt:ncs_multi_receipt site fe fe_ge locals original memory original_after final checked) :
  checked!(affine_proposed_result proposal)=Some(memory_boolean_word true) ->
  ncs_candidate_presumption(Entry fe_ge locals original memory) /\
  ncs_accepted_entry(Entry fe_ge locals original memory)(Entry fe_ge locals checked memory).
Proof.
  intro ACCEPT.
  destruct(ncs_multi_accept receipt ACCEPT) as [reference [model_after [FRAME [ALIAS [MODEL PUBLIC]]]]].
  assert(ANCHOR:ncs_model_anchor(Entry fe_ge locals original memory)(Entry fe_ge locals reference memory)).
  { split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [exact ALIAS|]]]].
    intros other_after other_final OTHER.
    destruct(@quiet_execution_determinate fe fe_ge locals original memory source E0 original_after final Out_normal
      SOURCE(ncs_multi_source_quiet site) E0 other_after other_final Out_normal OTHER) as [_ [AFTER [FINAL _]]].
    subst other_after other_final; exists model_after; split; assumption. }
  split.
  - exists(Entry fe_ge locals reference memory); exact ANCHOR.
  - split; [repeat split; try reflexivity; exact(ncs_multi_public receipt)|].
    exists(Entry fe_ge locals reference memory); split; [exact ANCHOR|].
    repeat split; try reflexivity; exact FRAME.
Qed.

Definition ncs_multi_guard_certificate {O : Type}(observe:fragment_observation -> O -> Prop) :
  guard_certificate(materialized_host fe observe)(materialized_source_completion source)
    ncs_candidate_presumption ncs_accepted_entry(private_scan_entry_frame scope)(ncs_multi_test site).
Proof.
  apply materialized_entry_execution_certificate.
  intros entry DOMAIN.
  destruct(materialized_source_receipt fe(ncs_multi_source_quiet site) DOMAIN) as [original_after [final SOURCE]].
  destruct entry as [ge locals original memory]; cbn [entry_ge entry_env entry_temps entry_memory] in SOURCE.
  destruct(ncs_multi_guard_execution site SOURCE) as [checked RECEIPT].
  destruct(ncs_multi_boolean RECEIPT) as [accepted FLAG].
  destruct(@describe_materialized_check_exact _ _ _(ncs_multi_describe site)) as [BODY CONDITION].
  exists accepted,checked; split.
  - rewrite BODY; exact(ncs_multi_run RECEIPT).
  - split.
    + rewrite CONDITION; apply shared_guard_choice_test; exact FLAG.
    + destruct accepted.
      * eapply ncs_multi_anchor; eassumption.
      * repeat split; try reflexivity; exact(ncs_multi_public RECEIPT).
Defined.
End CERTIFICATE.

Print Assumptions ncs_multi_anchor.
Print Assumptions ncs_multi_guard_certificate.
