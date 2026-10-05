From Stdlib Require Import Bool.
From GuardInterface Require Import GuardInterface.
Set Implicit Arguments.

(** The user chooses the region and candidate. This constructor only inserts
    an entry check and the original fragment as fallback. *)
Definition guarded_rewrite {S} (H : guard_host S)
  (source candidate : code H) (condition : check H) : code H :=
  select H condition candidate source.

(** Read-only means equality of the declared entry state. The host dispatch
    law must also account for observations; state equality alone cannot hide
    events, faults, or divergence. Safety is interpreted by the language. *)
Record readonly_condition {S} (H : guard_host S)
  (domain premise : S -> Prop) (condition : check H) := ReadonlyCondition {
  readonly_safe : forall entry, domain entry -> check_safe H condition entry;
  readonly_available : forall entry, domain entry ->
    exists accepted checked, checks H condition entry accepted checked;
  readonly_sound : forall entry accepted checked,
    domain entry -> checks H condition entry accepted checked ->
    checked = entry /\ (accepted = true -> premise entry)
}.

Definition local_equivalence {S} (H : guard_host S) (domain : S -> Prop)
  (first second : code H) : Prop :=
  forall entry observed, domain entry ->
    (runs H first entry observed <-> runs H second entry observed).

Definition conditional_equivalence {S} (H : guard_host S)
  (domain premise : S -> Prop) (source candidate : code H) : Prop :=
  local_equivalence H (fun entry => domain entry /\ premise entry) candidate source.

Definition readonly_guard_certificate S (H : guard_host S) domain premise condition
  (G : readonly_condition H domain premise condition) :
  guard_certificate H domain premise eq eq condition.
Proof.
  constructor.
  - exact (readonly_safe G).
  - exact (readonly_available G).
  - intros entry accepted checked DOMAIN CHECK.
    destruct (readonly_sound G entry accepted checked DOMAIN CHECK) as [SAME SOUND].
    subst checked; destruct accepted; cbn; auto.
Defined.

(** An encoding or entry-derivation certificate can discharge a stronger
    semantic obligation without changing the generated check. *)
Definition readonly_condition_entails S (H : guard_host S) domain encoded premise condition
  (G : readonly_condition H domain encoded condition)
  (ENCODING : forall entry, domain entry -> encoded entry -> premise entry) :
  readonly_condition H domain premise condition.
Proof.
  constructor.
  - exact (readonly_safe G).
  - exact (readonly_available G).
  - intros entry accepted checked DOMAIN CHECK.
    destruct (readonly_sound G entry accepted checked DOMAIN CHECK) as [SAME SOUND].
    split; [exact SAME|].
    intro ACCEPT; apply ENCODING; [exact DOMAIN|apply SOUND; exact ACCEPT].
Defined.

(** Placement may provide additional source facts. Restriction strengthens
    the entry domain while preserving the actual runtime check. *)
Definition readonly_condition_restrict S (H : guard_host S) domain smaller premise condition
  (G : readonly_condition H domain premise condition)
  (INCLUDED : forall entry, smaller entry -> domain entry) :
  readonly_condition H smaller premise condition.
Proof.
  constructor.
  - intros entry DOMAIN; apply (readonly_safe G); apply INCLUDED; exact DOMAIN.
  - intros entry DOMAIN; apply (readonly_available G); apply INCLUDED; exact DOMAIN.
  - intros entry accepted checked DOMAIN CHECK; apply (readonly_sound G);
      [apply INCLUDED; exact DOMAIN|exact CHECK].
Defined.

Theorem guarded_rewrite_equivalent S (H : guard_host S) domain premise source candidate condition
  (G : readonly_condition H domain premise condition)
  (LOCAL : conditional_equivalence H domain premise source candidate) :
  local_equivalence H domain (guarded_rewrite H source candidate condition) source.
Proof.
  intros entry observed DOMAIN; unfold guarded_rewrite.
  split.
  - intro RUN; apply (proj1 (select_exact H condition candidate source entry observed)) in RUN.
    destruct RUN as [accepted [checked [CHECK RUN]]].
    destruct (readonly_sound G entry accepted checked DOMAIN CHECK) as [SAME SOUND].
    subst checked; destruct accepted; cbn in RUN; [|exact RUN].
    apply (proj1 (LOCAL entry observed (conj DOMAIN (SOUND eq_refl)))); exact RUN.
  - intro SOURCE; apply (proj2 (select_exact H condition candidate source entry observed)).
    destruct (readonly_available G entry DOMAIN) as [accepted [checked CHECK]].
    destruct (readonly_sound G entry accepted checked DOMAIN CHECK) as [SAME SOUND].
    subst checked; exists accepted, entry; split; [exact CHECK|].
    destruct accepted; cbn; [|exact SOURCE].
    apply (proj2 (LOCAL entry observed (conj DOMAIN (SOUND eq_refl)))); exact SOURCE.
Qed.

(** A language localizes both actual fragments using the same entry view and
    reconstruction of public observations. Reconstruction may retain the
    untouched frame from the original entry. These exact execution bridges
    are where the language proves its effect bounds and representation laws. *)
Theorem localized_conditional_equivalence S LocalState LocalObservation
  (H : guard_host S) domain premise source candidate
  (view : S -> LocalState) (restore : S -> LocalObservation -> observation H)
  (source_local candidate_local : LocalState -> LocalObservation -> Prop)
  (SOURCE : forall entry observed, domain entry -> premise entry ->
    (runs H source entry observed <->
     exists result, source_local (view entry) result /\ observed = restore entry result))
  (CANDIDATE : forall entry observed, domain entry -> premise entry ->
    (runs H candidate entry observed <->
     exists result, candidate_local (view entry) result /\ observed = restore entry result))
  (LOCAL : forall entry result, domain entry -> premise entry ->
    (candidate_local (view entry) result <-> source_local (view entry) result)) :
  conditional_equivalence H domain premise source candidate.
Proof.
  intros entry observed [DOMAIN PREMISE]; split.
  - intro RUN; apply (proj1 (CANDIDATE entry observed DOMAIN PREMISE)) in RUN.
    destruct RUN as [result [RUN SAME]].
    apply (proj2 (SOURCE entry observed DOMAIN PREMISE)); exists result; split; [|exact SAME].
    apply (proj1 (LOCAL entry result DOMAIN PREMISE)); exact RUN.
  - intro RUN; apply (proj1 (SOURCE entry observed DOMAIN PREMISE)) in RUN.
    destruct RUN as [result [RUN SAME]].
    apply (proj2 (CANDIDATE entry observed DOMAIN PREMISE)); exists result; split; [|exact SAME].
    apply (proj2 (LOCAL entry result DOMAIN PREMISE)); exact RUN.
Qed.

(** The language proves which local observations its surrounding programs can
    consume. Placement establishes the domain at every supported entry;
    admissibility checks the actual replacement's interface and progress. *)
Record rewrite_context {S} (H : guard_host S) := RewriteContext {
  rewrite_surrounding : Type;
  rewrite_program : Type;
  rewrite_program_observation : Type;
  rewrite_plug : rewrite_surrounding -> code H -> rewrite_program;
  rewrite_program_runs : rewrite_program -> rewrite_program_observation -> Prop;
  rewrite_placement : rewrite_surrounding -> code H -> (S -> Prop) -> Prop;
  rewrite_admissible : rewrite_surrounding -> code H -> code H -> (S -> Prop) -> Prop;
  rewrite_lift : forall surrounding source target domain,
    rewrite_placement surrounding source domain ->
    rewrite_admissible surrounding source target domain ->
    local_equivalence H domain target source ->
    forall observed,
      rewrite_program_runs (rewrite_plug surrounding target) observed <->
      rewrite_program_runs (rewrite_plug surrounding source) observed
}.

Theorem guarded_rewrite_program_equivalent S (H : guard_host S) domain premise
  source candidate condition
  (G : readonly_condition H domain premise condition)
  (LOCAL : conditional_equivalence H domain premise source candidate)
  (C : rewrite_context H) surrounding :
  rewrite_placement C surrounding source domain ->
  rewrite_admissible C surrounding source (guarded_rewrite H source candidate condition) domain ->
  forall observed,
    rewrite_program_runs C (rewrite_plug C surrounding
      (guarded_rewrite H source candidate condition)) observed <->
    rewrite_program_runs C (rewrite_plug C surrounding source) observed.
Proof.
  intros PLACE ADMISSIBLE observed; apply rewrite_lift with (domain := domain); auto.
  eapply guarded_rewrite_equivalent; eassumption.
Qed.

Print Assumptions readonly_guard_certificate.
Print Assumptions readonly_condition_entails.
Print Assumptions readonly_condition_restrict.
Print Assumptions guarded_rewrite_equivalent.
Print Assumptions localized_conditional_equivalence.
Print Assumptions guarded_rewrite_program_equivalent.
