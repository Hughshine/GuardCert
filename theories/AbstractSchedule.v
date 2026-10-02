From Stdlib Require Import List RelationClasses.
Import ListNotations.
Set Implicit Arguments.

(** Property-based scheduling interface, motivated by PolCert INSTR.  Neither
    NonAlias nor read/write footprints are interpreted by this proof. An
    instance proves [independent] sufficient for commutation on its invariant.
    Non-aliasing alone is not a sufficient independence test. *)
Record scheduling_model (S Instruction : Type) := SchedulingModel {
  schedule_invariant : S -> Prop;
  state_equivalent : S -> S -> Prop;
  state_equivalence : Equivalence state_equivalent;
  instruction_run : Instruction -> S -> S -> Prop;
  independent : Instruction -> Instruction -> Prop;
  instruction_preserves : forall i s t,
    schedule_invariant s -> instruction_run i s t -> schedule_invariant t;
  instruction_transport : forall i s t s',
    state_equivalent s s' -> instruction_run i s t ->
    exists t', instruction_run i s' t' /\ state_equivalent t t';
  instruction_commutes : forall a b s t u,
    schedule_invariant s -> independent a b ->
    instruction_run a s t -> instruction_run b t u ->
    exists t' u', instruction_run b s t' /\ instruction_run a t' u' /\
      state_equivalent u u'
}.
Arguments scheduling_model S Instruction : clear implicits.

Section SCHEDULING.
Context {S Instruction} (M : scheduling_model S Instruction).

Inductive schedule_run : list Instruction -> S -> S -> Prop :=
| schedule_nil : forall s, schedule_run [] s s
| schedule_cons : forall i rest s t u,
    instruction_run M i s t -> schedule_run rest t u -> schedule_run (i :: rest) s u.

Lemma schedule_transport : forall is s t,
  schedule_run is s t -> forall s', state_equivalent M s s' ->
  exists t', schedule_run is s' t' /\ state_equivalent M t t'.
Proof.
  intros is s t RUN; induction RUN; intros s' EQ.
  - exists s'; split; auto; constructor.
  - destruct (@instruction_transport S Instruction M i s t s' EQ H) as [middle [HEAD REL]].
    destruct (IHRUN middle REL) as [final [TAIL REL']].
    exists final; split; auto; econstructor; eauto.
Qed.

(** A certificate records a finite chain of justified adjacent swaps. More
    general affine schedules need their own correspondence/order certificates;
    this interface is not a polyhedral validator. *)
Inductive schedule_certificate : list Instruction -> list Instruction -> Prop :=
| certificate_refl : forall is, schedule_certificate is is
| certificate_head : forall i source target,
    schedule_certificate source target -> schedule_certificate (i :: source) (i :: target)
| certificate_swap : forall a b rest,
    independent M a b -> schedule_certificate (a :: b :: rest) (b :: a :: rest)
| certificate_trans : forall source middle target,
    schedule_certificate source middle -> schedule_certificate middle target ->
    schedule_certificate source target.

Lemma equivalent_transitive : forall a b c,
  state_equivalent M a b -> state_equivalent M b c -> state_equivalent M a c.
Proof. exact (@Equivalence_Transitive S (state_equivalent M) (state_equivalence M)). Qed.

Theorem certified_schedule_preserves : forall source target,
  schedule_certificate source target -> forall s t,
  schedule_invariant M s -> schedule_run source s t ->
  exists t', schedule_run target s t' /\ state_equivalent M t t'.
Proof.
  intros source target CERT; induction CERT; intros s t INV RUN.
  - exists t; split; auto.
    exact (@Equivalence_Reflexive S (state_equivalent M) (state_equivalence M) t).
  - inversion RUN; subst.
    match goal with
    | HEAD : instruction_run M i s ?middle,
      TAIL : schedule_run source ?middle t |- _ =>
      destruct (IHCERT middle t (@instruction_preserves S Instruction M i s middle INV HEAD) TAIL)
        as [final [EXEC REL]] end.
    exists final; split; auto; econstructor; eauto.
  - inversion RUN; subst.
    match goal with TAIL : schedule_run (b :: rest) ?middle t |- _ =>
      inversion TAIL; subst end.
    match goal with
    | HA : instruction_run M a s ?first,
      HB : instruction_run M b ?first ?second,
      REST : schedule_run rest ?second t |- _ =>
      destruct (@instruction_commutes S Instruction M a b s first second INV H HA HB)
        as [first' [second' [HB' [HA' EQ]]]];
      destruct (@schedule_transport rest second t REST second' EQ) as [final [TAIL REL]] end.
    exists final; split; auto; econstructor; eauto; econstructor; eauto.
  - destruct (IHCERT1 s t INV RUN) as [mid [EXEC REL]].
    destruct (IHCERT2 s mid INV EXEC) as [final [EXEC' REL']].
    exists final; split; auto; eapply equivalent_transitive; eauto.
Qed.
End SCHEDULING.

Print Assumptions certified_schedule_preserves.
