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

Print Assumptions forward_bridge_equivalent.
