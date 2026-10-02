From Stdlib Require Import List ZArith.
From Guard Require Import AbstractGuard SemanticFacts PolCertLoopGuard.
From polcert.polygen Require Import InstrTy Loop.
Import ListNotations.
Set Implicit Arguments.

(** The program wrapper keeps the real Loop context and variable metadata.
    Entry facts must follow from its actual Compat/NonAlias/InitEnv premises. *)
Module PolCertLoopProgram (I : INSTR).
Module G := PolCertLoopGuard I.
Module L := G.L.

Definition body (p : L.t) : L.stmt := fst (fst p).
Definition context (p : L.t) : list I.ident := snd (fst p).
Definition variables (p : L.t) : list (I.ident * I.Ty.t) := snd p.

Definition admissible (p : L.t) (s : G.entry) : Prop :=
  I.Compat (variables p) (G.memory s) /\
  I.NonAlias (G.memory s) /\
  I.InitEnv (context p) (rev (G.parameters s)) (G.memory s).

Lemma semantics_entry p m result :
  L.semantics p m result <->
  exists env, admissible p (G.Entry env m) /\
    L.loop_semantics (body p) env m result.
Proof.
  destruct p as [[c ctxt] vars]. split.
  - intro RUN. inversion RUN; subst.
    match goal with EQ : (_, _, _) = (_, _, _) |- _ =>
      inversion EQ; subst end.
    eexists. split; [repeat split; eassumption | eassumption].
  - intros [env [[COMPAT [ALIAS INIT]] RUN]].
    econstructor; simpl in *; eauto.
Qed.

Definition same_metadata (source candidate : L.t) : Prop :=
  context source = context candidate /\ variables source = variables candidate.

Definition version_program {A} (domain : G.entry -> Prop)
  (P : A -> G.entry -> Prop) (atoms : forall a, G.encoded_atom domain (P a))
  (condition : formula A) (source candidate : L.t) : L.t :=
  (G.version domain P atoms condition (body source) (body candidate),
   context source, variables source).

Arguments version_program {A} domain P atoms condition source candidate.

Lemma version_execution {A} (domain : G.entry -> Prop)
  (P : A -> G.entry -> Prop) (atoms : forall a, G.encoded_atom domain (P a))
  condition source candidate s result :
  domain s ->
  (L.loop_semantics (G.version domain P atoms condition source candidate)
    (G.parameters s) (G.memory s) result <->
   L.loop_semantics
    (@selected_command G.entry G.loop_language
      (formula_execute (decide_atom (G.dimension domain P atoms)) condition s)
      candidate source source) (G.parameters s) (G.memory s) result).
Proof.
  intro DOMAIN.
  exact (@compile_condition_correct G.entry A G.loop_language domain
    (decide_atom (G.dimension domain P atoms)) (G.primitives domain P atoms)
    condition candidate source source s result DOMAIN).
Qed.

Arguments version_execution {A domain P} atoms condition source candidate s result _.

Lemma accepted_property {A} (domain : G.entry -> Prop)
  (P : A -> G.entry -> Prop) (atoms : forall a, G.encoded_atom domain (P a))
  condition s :
  domain s ->
  formula_execute (decide_atom (G.dimension domain P atoms)) condition s = Some true ->
  formula_property P condition s.
Proof.
  intros DOMAIN ACCEPT.
  exact (@formula_property_decision G.entry A domain
    (G.dimension domain P atoms) condition s true DOMAIN ACCEPT).
Qed.

Arguments accepted_property {A domain P} atoms condition {s} _ _.

Theorem version_program_preserves {A} (domain : G.entry -> Prop)
  (P : A -> G.entry -> Prop) (atoms : forall a, G.encoded_atom domain (P a))
  condition source candidate (R : I.State.t -> I.State.t -> Prop) :
  (forall result, R result result) ->
  (forall s, admissible source s -> domain s) ->
  (forall s result, admissible source s -> formula_property P condition s ->
    L.loop_semantics (body source) (G.parameters s) (G.memory s) result ->
    exists result',
      L.loop_semantics (body candidate) (G.parameters s) (G.memory s) result' /\
      R result result') ->
  forall m result, L.semantics source m result ->
  exists result', L.semantics (version_program domain P atoms condition source candidate)
    m result' /\ R result result'.
Proof.
  intros REFL DOMAIN LOCAL m result RUN.
  apply semantics_entry in RUN. destruct RUN as [env [ENTRY RUN]].
  pose proof (DOMAIN _ ENTRY) as INV.
  destruct (formula_execute (decide_atom (G.dimension domain P atoms))
    condition (G.Entry env m)) as [[|]|] eqn:CHECK.
  - destruct (LOCAL _ _ ENTRY (accepted_property atoms condition INV CHECK) RUN)
      as [result' [CAND REL]].
    exists result'. split; auto.
    apply semantics_entry. exists env. split; [exact ENTRY |].
    apply (proj2 (version_execution atoms condition (body source) (body candidate)
      (G.Entry env m) result' INV)). rewrite CHECK. exact CAND.
  - exists result. split; auto. apply semantics_entry. exists env.
    split; [exact ENTRY |].
    apply (proj2 (version_execution atoms condition (body source) (body candidate)
      (G.Entry env m) result INV)). rewrite CHECK. exact RUN.
  - exists result. split; auto. apply semantics_entry. exists env.
    split; [exact ENTRY |].
    apply (proj2 (version_execution atoms condition (body source) (body candidate)
      (G.Entry env m) result INV)). rewrite CHECK. exact RUN.
Qed.

(** The optimizer's wrapped backward endpoint can be consumed directly.
    Matching metadata makes the selected candidate body a valid execution of
    the actual candidate program, with this same parameter environment. *)
Theorem version_program_refines_endpoint {A} (domain : G.entry -> Prop)
  (P : A -> G.entry -> Prop) (atoms : forall a, G.encoded_atom domain (P a))
  condition source candidate (R : I.State.t -> I.State.t -> Prop) :
  same_metadata source candidate ->
  (forall result, R result result) ->
  (forall s, admissible source s -> domain s) ->
  (forall s result, admissible source s -> formula_property P condition s ->
    L.semantics candidate (G.memory s) result ->
    exists result', L.semantics source (G.memory s) result' /\ R result result') ->
  forall m result,
  L.semantics (version_program domain P atoms condition source candidate) m result ->
  exists result', L.semantics source m result' /\ R result result'.
Proof.
  intros [CONTEXT VARIABLES] REFL DOMAIN LOCAL m result RUN.
  apply semantics_entry in RUN. destruct RUN as [env [ENTRY RUN]].
  change (admissible source (G.Entry env m)) in ENTRY.
  pose proof (DOMAIN _ ENTRY) as INV.
  apply (proj1 (version_execution atoms condition (body source) (body candidate)
    (G.Entry env m) result INV)) in RUN.
  destruct (formula_execute (decide_atom (G.dimension domain P atoms))
    condition (G.Entry env m)) as [[|]|] eqn:CHECK; cbn [selected_command] in RUN.
  - apply (LOCAL _ _ ENTRY (accepted_property atoms condition INV CHECK)).
    apply semantics_entry. exists env. split; auto.
    unfold admissible in *. rewrite <- CONTEXT, <- VARIABLES. exact ENTRY.
  - exists result. split; auto. apply semantics_entry. exists env; auto.
  - exists result. split; auto. apply semantics_entry. exists env; auto.
Qed.

Corollary version_program_refines_unconditional {A} (domain : G.entry -> Prop)
  (P : A -> G.entry -> Prop) (atoms : forall a, G.encoded_atom domain (P a))
  condition source candidate :
  same_metadata source candidate ->
  (forall s, admissible source s -> domain s) ->
  (forall m result, L.semantics candidate m result ->
    exists result', L.semantics source m result' /\ I.State.eq result result') ->
  forall m result,
  L.semantics (version_program domain P atoms condition source candidate) m result ->
  exists result', L.semantics source m result' /\ I.State.eq result result'.
Proof.
  intros META DOMAIN LOCAL.
  eapply version_program_refines_endpoint; eauto using I.State.eq_refl.
Qed.

Theorem impossible_program source candidate m result :
  L.semantics (version_program (fun _ => True) G.zero_property G.zero_atom
    G.impossible source candidate) m result <-> L.semantics source m result.
Proof.
  rewrite !semantics_entry. split; intros [env [ENTRY RUN]]; exists env;
    split; [exact ENTRY | | exact ENTRY |].
  - apply (proj1 (G.impossible_version (body source) (body candidate)
      (G.Entry env m) result)). exact RUN.
  - apply (proj2 (G.impossible_version (body source) (body candidate)
      (G.Entry env m) result)). exact RUN.
Qed.

Print Assumptions semantics_entry.
Print Assumptions version_program_preserves.
Print Assumptions version_program_refines_endpoint.
Print Assumptions version_program_refines_unconditional.
Print Assumptions impossible_program.

End PolCertLoopProgram.
