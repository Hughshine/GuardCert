From GuardInterface Require Import GuardInterface GuardedRewrite.
Set Implicit Arguments.

Lemma local_equivalence_trans S (H : guard_host S) domain first middle last :
  local_equivalence H domain first middle -> local_equivalence H domain middle last ->
  local_equivalence H domain first last.
Proof.
  intros FIRST SECOND entry observed DOMAIN.
  exact (iff_trans (FIRST entry observed DOMAIN) (SECOND entry observed DOMAIN)).
Qed.

Section COMPOSITION.
Context {S : Type} (H : guard_host S) (C : rewrite_context H).

(** The user supplies the context and evidence for each actual intermediate
    program. No traversal, recognizer, candidate search, or reused premise is
    hidden in this relation. *)
Inductive certified_rewrite_step : rewrite_program C -> rewrite_program C -> Prop :=
| certify_rewrite : forall surrounding source candidate condition domain premise,
    readonly_condition H domain premise condition ->
    conditional_equivalence H domain premise source candidate ->
    rewrite_placement C surrounding source domain ->
    rewrite_admissible C surrounding source (guarded_rewrite H source candidate condition) domain ->
    certified_rewrite_step (rewrite_plug C surrounding source)
      (rewrite_plug C surrounding (guarded_rewrite H source candidate condition)).

Theorem certified_rewrite_step_equivalent before after : certified_rewrite_step before after ->
  forall observed, rewrite_program_runs C before observed <-> rewrite_program_runs C after observed.
Proof.
  intro STEP; destruct STEP as [surrounding source candidate condition domain premise G LOCAL PLACE INSTALL].
  intro observed; apply iff_sym.
  eapply guarded_rewrite_program_equivalent; eassumption.
Qed.

Inductive certified_rewrite_sequence : rewrite_program C -> rewrite_program C -> Prop :=
| rewrite_sequence_refl : forall p, certified_rewrite_sequence p p
| rewrite_sequence_cons : forall first middle last,
    certified_rewrite_step first middle -> certified_rewrite_sequence middle last ->
    certified_rewrite_sequence first last.

Theorem certified_rewrite_sequence_equivalent first last : certified_rewrite_sequence first last ->
  forall observed, rewrite_program_runs C first observed <-> rewrite_program_runs C last observed.
Proof.
  intro SEQUENCE; induction SEQUENCE as [p|first middle last STEP TAIL IH]; intro observed; [apply iff_refl|].
  exact (iff_trans (certified_rewrite_step_equivalent STEP observed) (IH observed)).
Qed.
End COMPOSITION.

Print Assumptions local_equivalence_trans.
Print Assumptions certified_rewrite_step_equivalent.
Print Assumptions certified_rewrite_sequence_equivalent.
