From GuardInterface Require Import GuardInterface GuardedRewrite.
Set Implicit Arguments.

(** Reconstruction is relational: a local result can represent several raw
    exits differing in private temporaries or in a language's memory relation.
    Each certificate binds an actual command and its exact observation law. *)
Record localized_fragment {S LocalState LocalExit} (H : guard_host S)
  (domain premise : S -> Prop) (view : S -> LocalState)
  (reconstruct : S -> LocalExit -> observation H -> Prop)
  (local_run : LocalState -> LocalExit -> Prop) (actual : code H) := LocalizedFragment {
  localized_execution : forall entry observed, domain entry -> premise entry ->
    (runs H actual entry observed <-> exists result,
      local_run (view entry) result /\ reconstruct entry result observed)
}.

Theorem relational_localization_equivalent S LocalState LocalExit
  (H : guard_host S) domain premise source candidate
  (view : S -> LocalState) (reconstruct : S -> LocalExit -> observation H -> Prop)
  (source_run candidate_run : LocalState -> LocalExit -> Prop)
  (SOURCE : localized_fragment H domain premise view reconstruct source_run source)
  (CANDIDATE : localized_fragment H domain premise view reconstruct candidate_run candidate)
  (LOCAL : forall entry result, domain entry -> premise entry ->
    (candidate_run (view entry) result <-> source_run (view entry) result)) :
  conditional_equivalence H domain premise source candidate.
Proof.
  intros entry observed [DOMAIN PREMISE]; split.
  - intro RUN; apply (proj1 (localized_execution CANDIDATE entry observed DOMAIN PREMISE)) in RUN.
    destruct RUN as [result [RUN MATCH]].
    apply (proj2 (localized_execution SOURCE entry observed DOMAIN PREMISE)); exists result; split; [|exact MATCH].
    apply (proj1 (LOCAL entry result DOMAIN PREMISE)); exact RUN.
  - intro RUN; apply (proj1 (localized_execution SOURCE entry observed DOMAIN PREMISE)) in RUN.
    destruct RUN as [result [RUN MATCH]].
    apply (proj2 (localized_execution CANDIDATE entry observed DOMAIN PREMISE)); exists result; split; [|exact MATCH].
    apply (proj2 (LOCAL entry result DOMAIN PREMISE)); exact RUN.
Qed.

Print Assumptions relational_localization_equivalent.
