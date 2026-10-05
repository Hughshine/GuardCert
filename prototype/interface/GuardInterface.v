From Stdlib Require Import Bool.
Set Implicit Arguments.

(** Entry checking with private effects. An instance must justify the exact
    dispatch law for its declared observations, including exceptional or
    divergent behaviors if it claims to cover them. *)
Record guard_host (S : Type) := GuardHost {
  code : Type;
  check : Type;
  observation : Type;
  runs : code -> S -> observation -> Prop;
  checks : check -> S -> bool -> S -> Prop;
  check_safe : check -> S -> Prop;
  select : check -> code -> code -> code;
  select_exact : forall test yes no entry observed,
    runs (select test yes no) entry observed <->
    exists accepted checked, checks test entry accepted checked /\
      runs (if accepted then yes else no) checked observed
}.

Arguments runs {S} _ _ _ _.
Arguments checks {S} _ _ _ _ _.
Arguments select {S} _ _ _ _.

(** The premise is anchored at the original entry. Every check execution must
    establish the appropriate entry relation; refusal has no negative meaning.
    Availability is existential and is not a general termination theorem. *)
Record guard_certificate {S} (H : guard_host S)
  (domain premise : S -> Prop) (accepted_entry refused_entry : S -> S -> Prop)
  (test : check H) := GuardCertificate {
  check_safety : forall entry, domain entry -> check_safe H test entry;
  check_available : forall entry, domain entry ->
    exists accepted checked, checks H test entry accepted checked;
  check_sound : forall entry accepted checked,
    domain entry -> checks H test entry accepted checked ->
    if accepted then premise entry /\ accepted_entry entry checked
    else refused_entry entry checked
}.

(** Source, candidate, and fallback are actual commands. Their proofs compare
    behavior from the checked state with source behavior from the original
    entry, rather than assuming that a check leaves all state unchanged. *)
Record conditional_certificate {S} (H : guard_host S)
  (domain premise : S -> Prop) (accepted_entry refused_entry : S -> S -> Prop)
  (related : observation H -> observation H -> Prop)
  (source candidate fallback : code H) := ConditionalCertificate {
  accepted_refinement : forall entry checked target,
    domain entry -> premise entry -> accepted_entry entry checked ->
    runs H candidate checked target ->
    exists original, runs H source entry original /\ related target original;
  refused_refinement : forall entry checked target,
    domain entry -> refused_entry entry checked ->
    runs H fallback checked target ->
    exists original, runs H source entry original /\ related target original
}.

Definition local_refinement {S} (H : guard_host S) (domain : S -> Prop)
  (related : observation H -> observation H -> Prop) (target source : code H) :=
  forall entry observed, domain entry -> runs H target entry observed ->
    exists original, runs H source entry original /\ related observed original.

(** A reusable adapter for rules already proved at one state. It is suitable
    when checks preserve the source's observations exactly. More general
    representation transport uses the full conditional certificate instead. *)
Definition framed_rule_certificate S (H : guard_host S) domain premise
  accepted_entry refused_entry related source candidate
  (REFLEXIVE : forall observed, related observed observed)
  (DOMAIN_STABLE : forall entry checked,
    domain entry -> accepted_entry entry checked -> domain checked)
  (PREMISE_STABLE : forall entry checked,
    premise entry -> accepted_entry entry checked -> premise checked)
  (SOURCE_TRANSPORT : forall entry checked observed, domain entry ->
    accepted_entry entry checked \/ refused_entry entry checked ->
    runs H source checked observed -> runs H source entry observed)
  (LOCAL : forall checked target, domain checked -> premise checked ->
    runs H candidate checked target ->
    exists original, runs H source checked original /\ related target original) :
  conditional_certificate H domain premise accepted_entry refused_entry
    related source candidate source.
Proof.
  constructor.
  - intros entry checked target DOMAIN PREMISE ENTRY RUN.
    destruct (LOCAL checked target (DOMAIN_STABLE entry checked DOMAIN ENTRY)
      (PREMISE_STABLE entry checked PREMISE ENTRY) RUN) as [original [SOURCE REL]].
    exists original; split; [|exact REL].
    eapply SOURCE_TRANSPORT; [exact DOMAIN|left; exact ENTRY|exact SOURCE].
  - intros entry checked target DOMAIN ENTRY RUN.
    exists target; split; [|apply REFLEXIVE].
    eapply SOURCE_TRANSPORT; [exact DOMAIN|right; exact ENTRY|exact RUN].
Defined.

Theorem guardify_refinement S (H : guard_host S) domain premise accepted_entry refused_entry
  related source candidate fallback test
  (G : guard_certificate H domain premise accepted_entry refused_entry test)
  (T : conditional_certificate H domain premise accepted_entry refused_entry
    related source candidate fallback) :
  local_refinement H domain related (select H test candidate fallback) source.
Proof.
  intros entry target DOMAIN RUN.
  apply (proj1 (select_exact H test candidate fallback entry target)) in RUN.
  destruct RUN as [accepted [checked [CHECK RUN]]].
  pose proof (check_sound G entry accepted checked DOMAIN CHECK) as SOUND.
  destruct accepted; cbn in SOUND, RUN.
  - destruct SOUND as [PREMISE ENTRY].
    eapply accepted_refinement; eassumption.
  - eapply refused_refinement; eassumption.
Qed.

(** Preservation is a separate contract, not an alternative spelling of
    refinement. It also establishes selected-branch availability for each
    source behavior. *)
Record preservation_certificate {S} (H : guard_host S)
  (domain premise : S -> Prop) (accepted_entry refused_entry : S -> S -> Prop)
  (related : observation H -> observation H -> Prop)
  (source candidate fallback : code H) := PreservationCertificate {
  accepted_preservation : forall entry checked original,
    domain entry -> premise entry -> accepted_entry entry checked ->
    runs H source entry original ->
    exists target, runs H candidate checked target /\ related target original;
  refused_preservation : forall entry checked original,
    domain entry -> refused_entry entry checked -> runs H source entry original ->
    exists target, runs H fallback checked target /\ related target original
}.

Theorem guardify_preservation S (H : guard_host S) domain premise accepted_entry refused_entry
  related source candidate fallback test
  (G : guard_certificate H domain premise accepted_entry refused_entry test)
  (T : preservation_certificate H domain premise accepted_entry refused_entry
    related source candidate fallback) :
  forall entry original, domain entry -> runs H source entry original ->
  exists target, runs H (select H test candidate fallback) entry target /\ related target original.
Proof.
  intros entry original DOMAIN SOURCE.
  destruct (check_available G entry DOMAIN) as [accepted [checked CHECK]].
  pose proof (check_sound G entry accepted checked DOMAIN CHECK) as SOUND.
  destruct accepted; cbn in SOUND.
  - destruct SOUND as [PREMISE ENTRY].
    destruct (accepted_preservation T entry checked original DOMAIN PREMISE ENTRY SOURCE)
      as [target [RUN RELATED]].
    exists target; split; [|exact RELATED].
    apply (proj2 (select_exact H test candidate fallback entry target)).
    exists true, checked; split; assumption.
  - destruct (refused_preservation T entry checked original DOMAIN SOUND SOURCE)
      as [target [RUN RELATED]].
    exists target; split; [|exact RELATED].
    apply (proj2 (select_exact H test candidate fallback entry target)).
    exists false, checked; split; assumption.
Qed.

(** The host proves compatibility with actual surrounding control flow. This
    record does not assert that every context respects every local relation. *)
Record context_certificate {S} (H : guard_host S)
  (related : observation H -> observation H -> Prop) := ContextCertificate {
  context : Type;
  program : Type;
  program_observation : Type;
  plug : context -> code H -> program;
  program_runs : program -> program_observation -> Prop;
  program_related : program_observation -> program_observation -> Prop;
  legal_placement : context -> code H -> (S -> Prop) -> Prop;
  admissible_replacement : context -> code H -> code H -> (S -> Prop) -> Prop;
  lift_refinement : forall surrounding source target domain,
    legal_placement surrounding source domain ->
    admissible_replacement surrounding source target domain ->
    local_refinement H domain related target source ->
    forall observed, program_runs (plug surrounding target) observed ->
    exists original, program_runs (plug surrounding source) original /\
      program_related observed original
}.

Theorem guardify_program_refinement S (H : guard_host S) domain premise
  accepted_entry refused_entry related source candidate fallback test
  (G : guard_certificate H domain premise accepted_entry refused_entry test)
  (T : conditional_certificate H domain premise accepted_entry refused_entry
    related source candidate fallback)
  (C : context_certificate H related) surrounding :
  legal_placement C surrounding source domain ->
  admissible_replacement C surrounding source (select H test candidate fallback) domain ->
  forall observed,
    program_runs C (plug C surrounding (select H test candidate fallback)) observed ->
    exists original, program_runs C (plug C surrounding source) original /\
      program_related C observed original.
Proof.
  intros PLACE ADMISSIBLE observed RUN.
  eapply lift_refinement; [exact PLACE|exact ADMISSIBLE| |exact RUN].
  eapply guardify_refinement; eassumption.
Qed.

Print Assumptions guardify_refinement.
Print Assumptions guardify_preservation.
Print Assumptions guardify_program_refinement.
Print Assumptions framed_rule_certificate.
