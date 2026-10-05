From Stdlib Require Import List ZArith.
From compcert.lib Require Import Integers Maps Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame CompCertMemoryEquivalence.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite
  ClightRegionBoundary ClightQuietDeterminacy ClightLoopBridge.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The candidate really changes a hidden temporary. Raw execution results
    differ, while the boundary observes all memory, events, exits, and the
    declared live temporaries. This is a local example, not a compiler pass
    that allocates fresh function temporaries or proves context freshness. *)
Definition public_set public := Sset public (Econst_int (Int.repr 5) type_int32s).
Definition private_candidate public private :=
  Ssequence (Sset private (Econst_int (Int.repr 99) type_int32s)) (public_set public).
Definition private_candidate_ports public private live :=
  {| region_inputs := []; region_stable := []; region_live_out := live;
     region_written := [public]; region_private := [private];
     region_write_bytes := fun _ _ _ => False |}.

Definition public_result public entry := FragmentObservation E0
  (PTree.set public (Vint (Int.repr 5)) (entry_temps entry)) (entry_memory entry) Out_normal.
Definition private_result public private entry := FragmentObservation E0
  (PTree.set public (Vint (Int.repr 5))
    (PTree.set private (Vint (Int.repr 99)) (entry_temps entry)))
  (entry_memory entry) Out_normal.

Lemma public_set_run fe public entry :
  clight_fragment_run fe (public_set public) entry (public_result public entry).
Proof. unfold clight_fragment_run, public_set, public_result; apply exec_Sset; constructor. Qed.

Lemma private_candidate_run fe public private entry :
  clight_fragment_run fe (private_candidate public private) entry (private_result public private entry).
Proof.
  unfold clight_fragment_run, private_candidate, private_result, public_set.
  replace E0 with (E0 ** E0) by reflexivity.
  eapply exec_Sseq_1; apply exec_Sset; constructor.
Qed.

Lemma private_result_observed public private live entry
  (FRESH : ~ In private live) :
  boundary_observe (private_candidate_ports public private live)
    (public_result public entry) (private_result public private entry).
Proof.
  unfold boundary_observe, public_result, private_result; cbn.
  split; [reflexivity|split; [reflexivity|split]].
  - intros id LIVE; repeat rewrite PTree.gsspec.
    destruct (peq id public); [reflexivity|].
    destruct (peq id private); [subst id; contradiction|reflexivity].
  - apply memory_equivalent_refl.
Qed.

Theorem private_candidate_equivalent fe public private live
  (FRESH : ~ In private live) :
  conditional_equivalence
    (readonly_clight_host fe (boundary_observe (private_candidate_ports public private live)))
    (fun _ => True) (fun _ => True) (public_set public) (private_candidate public private).
Proof.
  apply quiet_observed_forward_loop_equivalent.
  - apply boundary_observe_sym.
  - apply boundary_observe_trans.
  - intros entry _ _; exists (public_result public entry); intro other_fe; apply public_set_run.
  - reflexivity.
  - intros entry observed _ _ RUN.
    assert (SAME : observed = public_result public entry).
    { eapply quiet_fragment_determinate with (body := public_set public);
        [reflexivity|exact RUN|apply public_set_run]. }
    subst observed; exists (private_result public private entry); split.
    + apply private_candidate_run.
    + apply private_result_observed; exact FRESH.
Qed.

Definition private_candidate_check fe public private live :
  readonly_condition
    (readonly_clight_host fe (boundary_observe (private_candidate_ports public private live)))
    (fun _ => True) (fun _ => True) (Decision true).
Proof.
  constructor.
  - intros; constructor.
  - intros entry _; exists true, entry; split; [constructor|reflexivity].
  - intros entry accepted checked _ [_ SAME]; split; [exact SAME|auto].
Defined.

Theorem private_candidate_rewrite_equivalent fe public private live
  (FRESH : ~ In private live) :
  local_equivalence
    (readonly_clight_host fe (boundary_observe (private_candidate_ports public private live)))
    (fun _ => True)
    (guarded_rewrite
      (readonly_clight_host fe (boundary_observe (private_candidate_ports public private live)))
      (public_set public) (private_candidate public private) (Decision true)) (public_set public).
Proof.
  apply guarded_rewrite_equivalent with (premise := fun _ => True).
  - apply private_candidate_check.
  - apply private_candidate_equivalent; exact FRESH.
Qed.

(** An explicit witness that full temporary equality cannot justify this
    rewrite. The proof above uses actual Clight executions for both results. *)
Theorem private_candidate_changes_raw_result public private ge locals memory
  (DISTINCT : public <> private) :
  public_result public (Entry ge locals (PTree.empty val) memory) <>
  private_result public private (Entry ge locals (PTree.empty val) memory).
Proof.
  intro SAME.
  assert (TEMP : (fragment_temps (public_result public (Entry ge locals (PTree.empty val) memory))) ! private =
    (fragment_temps (private_result public private (Entry ge locals (PTree.empty val) memory))) ! private)
    by (rewrite SAME; reflexivity).
  cbn [public_result private_result fragment_temps entry_temps] in TEMP.
  repeat rewrite PTree.gso in TEMP by congruence.
  rewrite PTree.gempty, PTree.gss in TEMP; discriminate.
Qed.

Print Assumptions private_candidate_equivalent.
Print Assumptions private_candidate_rewrite_equivalent.
Print Assumptions private_candidate_changes_raw_result.
