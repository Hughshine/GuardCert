From GuardInterface Require Import GuardInterface GuardedRewrite.
Set Implicit Arguments.

(** A forward execution bridge suffices for local equivalence only when the
    source has a result and the candidate has a unique observation. Completion
    and determinacy are explicit language properties, never generic defaults.
    For terminating-fragment observations the host must justify completion at
    the actual placement; this cannot silently exclude diverging source runs. *)
Theorem forward_bridge_equivalent S (H : guard_host S) domain premise source candidate
  (SOURCE_COMPLETES : forall entry, domain entry -> premise entry ->
    exists observed, runs H source entry observed)
  (FORWARD : forall entry observed, domain entry -> premise entry ->
    runs H source entry observed -> runs H candidate entry observed)
  (CANDIDATE_DETERMINATE : forall entry first second, domain entry -> premise entry ->
    runs H candidate entry first -> runs H candidate entry second -> first = second) :
  conditional_equivalence H domain premise source candidate.
Proof.
  intros entry observed [DOMAIN PREMISE]; split.
  - intro CANDIDATE.
    destruct (SOURCE_COMPLETES entry DOMAIN PREMISE) as [original SOURCE].
    pose proof (FORWARD entry original DOMAIN PREMISE SOURCE) as OTHER.
    pose proof (CANDIDATE_DETERMINATE entry observed original DOMAIN PREMISE CANDIDATE OTHER) as SAME.
    subst original; exact SOURCE.
  - intro SOURCE; apply FORWARD; assumption.
Qed.

(** A projected/saturated observation need not be unique, even if the raw
    execution is deterministic. Users supply the exact raw-to-visible bridge
    and transport of all visible observations across the forward result. *)
Theorem saturated_forward_bridge_equivalent S Raw (H : guard_host S) domain premise source candidate
  (raw_runs : code H -> S -> Raw -> Prop)
  (observe : Raw -> observation H -> Prop)
  (SOURCE_BRIDGE : forall entry observed, domain entry -> premise entry ->
    (runs H source entry observed <-> exists raw, raw_runs source entry raw /\ observe raw observed))
  (CANDIDATE_BRIDGE : forall entry observed, domain entry -> premise entry ->
    (runs H candidate entry observed <-> exists raw, raw_runs candidate entry raw /\ observe raw observed))
  (SOURCE_COMPLETES : forall entry, domain entry -> premise entry -> exists raw, raw_runs source entry raw)
  (FORWARD : forall entry original, domain entry -> premise entry -> raw_runs source entry original ->
    exists transformed, raw_runs candidate entry transformed /\
      forall observed, observe original observed <-> observe transformed observed)
  (RAW_DETERMINATE : forall entry first second, domain entry -> premise entry ->
    raw_runs candidate entry first -> raw_runs candidate entry second -> first = second) :
  conditional_equivalence H domain premise source candidate.
Proof.
  intros entry observed [DOMAIN PREMISE]; split.
  - intro TARGET; apply (proj1 (CANDIDATE_BRIDGE entry observed DOMAIN PREMISE)) in TARGET.
    destruct TARGET as [raw [TARGET VISIBLE]].
    destruct (SOURCE_COMPLETES entry DOMAIN PREMISE) as [original SOURCE].
    destruct (FORWARD entry original DOMAIN PREMISE SOURCE) as [transformed [OTHER TRANSPORT]].
    pose proof (RAW_DETERMINATE entry raw transformed DOMAIN PREMISE TARGET OTHER) as SAME; subst transformed.
    apply (proj2 (SOURCE_BRIDGE entry observed DOMAIN PREMISE)); exists original; split; [exact SOURCE|].
    apply (proj2 (TRANSPORT observed)); exact VISIBLE.
  - intro SOURCE; apply (proj1 (SOURCE_BRIDGE entry observed DOMAIN PREMISE)) in SOURCE.
    destruct SOURCE as [original [SOURCE VISIBLE]].
    destruct (FORWARD entry original DOMAIN PREMISE SOURCE) as [transformed [TARGET TRANSPORT]].
    apply (proj2 (CANDIDATE_BRIDGE entry observed DOMAIN PREMISE)); exists transformed; split; [exact TARGET|].
    apply (proj1 (TRANSPORT observed)); exact VISIBLE.
Qed.

Print Assumptions forward_bridge_equivalent.
Print Assumptions saturated_forward_bridge_equivalent.
