From Stdlib Require Import List ZArith.
From polcert.lib Require Import ImpureAlarmConfig.
From polcert.src Require Import TilingWitness.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryAffineReindex
  GuardMemoryBoundedSourceChecker GuardMemoryBoundedSourceTiling.
From GuardAffineNest Require Import AffineNestBoundedSiteChecker AffineNestDomainSplit AffineNestSplitChecker AffineNestLoopEquality.
Import CoreAlarmed ListNotations.
Set Implicit Arguments.

(** Candidate evidence selects a proved validator. Both descriptions remain
    untrusted: the extracted checks establish the same source certificate. *)
Inductive affine_candidate_evidence :=
  | AffineIndexEvidence (steps : list memory_affine_reindex)
  | AffineSiteEvidence (steps : list memory_affine_reindex)(positions:list nat)
  | AffineSplitEvidence (conditions:list L.test)(steps:list memory_affine_reindex)(positions:list nat)
  | AffineTilingEvidence (witnesses : list statement_tiling_witness)
  | AffineDomainEvidence (conditions:list L.test)(nested:affine_candidate_evidence)
  | AffineChainEvidence (middle:L.stmt)(first second:affine_candidate_evidence)
  | AffinePartitionTargetEvidence (conditions:list L.test)(base:L.stmt)(nested:affine_candidate_evidence).

Fixpoint checked_affine_candidate bounds source context pointers candidate evidence {struct evidence} :=
  match evidence with
  | AffineIndexEvidence steps =>
      checked_memory_bounded_source_candidate bounds source context pointers candidate steps
  | AffineSiteEvidence steps positions=>
      checked_affine_bounded_site_candidate bounds source context pointers candidate steps positions
  | AffineSplitEvidence conditions steps positions=>
      checked_affine_split_candidate bounds source context pointers candidate conditions steps positions
  | AffineTilingEvidence witnesses =>
      checked_memory_bounded_source_tiling bounds source candidate context pointers witnesses
  | AffineDomainEvidence conditions nested=>
      checked_affine_candidate bounds(affine_partitioned_sources conditions source) context pointers candidate nested
  | AffineChainEvidence middle first second=>
      BIND accepted <- checked_affine_candidate bounds source context pointers middle first -;
      if accepted then checked_affine_candidate bounds middle context pointers candidate second else pure false
  | AffinePartitionTargetEvidence conditions base nested=>
      if affine_loop_statement_eq_dec candidate(affine_partitioned_sources conditions base)
      then checked_affine_candidate bounds source context pointers base nested else pure false
  end.

Theorem checked_affine_candidate_correct bounds source context pointers candidate evidence :
  mayReturn(checked_affine_candidate bounds source context pointers candidate evidence) true ->
  memory_bounded_source_certificate bounds source context candidate.
Proof.
  revert bounds source context pointers candidate.
  induction evidence as [steps|steps positions|conditions steps positions|witnesses|conditions nested IH|middle first IH1 second IH2|conditions base nested IH];
    intros bounds source context pointers candidate; cbn [checked_affine_candidate].
  - apply checked_memory_bounded_source_candidate_correct.
  - apply checked_affine_bounded_site_candidate_correct.
  - apply checked_affine_split_candidate_correct.
  - apply checked_memory_bounded_source_tiling_correct.
  - intros CHECK parameters initial final LENGTH WITHIN NONALIAS SOURCE.
    eapply IH; [exact CHECK|exact LENGTH|exact WITHIN|exact NONALIAS|].
    apply affine_partitioned_sources_execution; exact SOURCE.
  - intro CHECK; bind_imp_destruct CHECK accepted FIRST.
    destruct accepted; [|apply mayReturn_pure in CHECK; discriminate].
    intros parameters initial final LENGTH WITHIN NONALIAS SOURCE.
    eapply IH2; [exact CHECK|exact LENGTH|exact WITHIN|exact NONALIAS|].
    eapply IH1; eauto.
  - destruct(affine_loop_statement_eq_dec candidate(affine_partitioned_sources conditions base)) as [EXACT|];
      [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
    subst candidate; intros CHECK parameters initial final LENGTH WITHIN NONALIAS SOURCE.
    apply affine_partitioned_sources_execution.
    eapply IH; eauto.
Qed.
Print Assumptions checked_affine_candidate_correct.
