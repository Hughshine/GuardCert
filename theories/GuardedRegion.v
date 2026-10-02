From Stdlib Require Import List Bool Arith Streams.
Import ListNotations.
Set Implicit Arguments.

(** Prototype semantics: a region is a total, finite macro-transition.
    All externally relevant state, its trace, and its control exit are explicit.
    Divergence inside a region and actual CompCert guard lowering are outside
    this model. Infinite execution of the surrounding CFG is modeled below. *)
Section Framework.
Context {State Event : Type}.

Inductive exit :=
| Jump (destination : nat)
| Return (value : nat)
| Trap.

Record transfer := Transfer {
  events : list Event;
  destination : exit;
  final_state : State
}.

Definition region := State -> transfer.

Record guarded_rewrite := GuardedRewrite {
  original : region;
  optimized : region;
  assumption : State -> Prop;
  check : State -> bool;
  check_sound : forall s, check s = true -> assumption s;
  conditional_correct : forall s, assumption s -> optimized s = original s
}.

Definition versioned (r : guarded_rewrite) : region :=
  fun s => if check r s then optimized r s else original r s.

Theorem versioned_correct :
  forall r s, versioned r s = original r s.
Proof.
  intros r s. unfold versioned.
  destruct (check r s) eqn:Hcheck.
  - apply conditional_correct. apply check_sound. exact Hcheck.
  - reflexivity.
Qed.

(** The interface forces the original and optimized versions to expose the
    same control exits and complete state. A weaker state relation requires a
    host compatibility proof; equality is the deliberate first prototype. *)
Definition program := nat -> option region.
Definition plan := nat -> option guarded_rewrite.

Definition plan_matches (p : program) (rs : plan) : Prop :=
  forall pc r, rs pc = Some r -> p pc = Some (original r).

Definition apply_plan (p : program) (rs : plan) : program :=
  fun pc => match rs pc with
            | Some r => Some (versioned r)
            | None => p pc
            end.

Inductive configuration :=
| Running (pc : nat) (state : State)
| Halted (value : nat) (state : State)
| Faulted (state : State).

Definition leave (t : transfer) : configuration :=
  match destination t with
  | Jump pc => Running pc (final_state t)
  | Return value => Halted value (final_state t)
  | Trap => Faulted (final_state t)
  end.

Definition step (p : program) (c : configuration)
  : option (list Event * configuration) :=
  match c with
  | Running pc s =>
      match p pc with
      | Some block => let t := block s in Some (events t, leave t)
      | None => Some ([], Faulted s)
      end
  | Halted _ _ | Faulted _ => None
  end.

Theorem apply_plan_step :
  forall p rs, plan_matches p rs ->
  forall c, step (apply_plan p rs) c = step p c.
Proof.
  intros p rs Hmatch c. destruct c as [pc s | value s | s]; try reflexivity.
  unfold step, apply_plan.
  destruct (rs pc) as [r |] eqn:Hlookup.
  - rewrite (Hmatch pc r Hlookup). rewrite versioned_correct. reflexivity.
  - reflexivity.
Qed.

Inductive execution (p : program)
  : configuration -> list Event -> configuration -> Prop :=
| execution_refl : forall c, execution p c [] c
| execution_step : forall c c' c'' t ts,
    step p c = Some (t, c') ->
    execution p c' ts c'' ->
    execution p c (t ++ ts) c''.

Lemma execution_transport :
  forall p q, (forall c, step p c = step q c) ->
  forall c t c', execution p c t c' -> execution q c t c'.
Proof.
  intros p q Heq c t c' Hexec. induction Hexec.
  - constructor.
  - econstructor; eauto. rewrite <- Heq. exact H.
Qed.

Theorem whole_program_finite :
  forall p rs, plan_matches p rs ->
  forall c t c',
    execution (apply_plan p rs) c t c' <-> execution p c t c'.
Proof.
  intros p rs Hmatch c t c'. split; intro Hexec.
  - eapply execution_transport; [| exact Hexec].
    apply apply_plan_step. exact Hmatch.
  - eapply execution_transport; [| exact Hexec].
    intro s. symmetry. apply apply_plan_step. exact Hmatch.
Qed.

(** Stream entries are finite event lists, one per region transition.
    Empty entries preserve silent divergence rather than discarding it. *)
CoInductive infinite_execution (p : program)
  : configuration -> Stream (list Event) -> Prop :=
| infinite_step : forall c c' t ts,
    step p c = Some (t, c') ->
    infinite_execution p c' ts ->
    infinite_execution p c (Cons t ts).

Lemma infinite_execution_transport :
  forall p q, (forall c, step p c = step q c) ->
  forall c ts, infinite_execution p c ts -> infinite_execution q c ts.
Proof.
  intros p q Heq. cofix CIH. intros c ts Hinf.
  inversion Hinf as [c0 c' t ts' Hstep Htail]; subst.
  econstructor.
  - rewrite <- Heq. exact Hstep.
  - apply CIH. exact Htail.
Qed.

Theorem whole_program_infinite :
  forall p rs, plan_matches p rs ->
  forall c ts,
    infinite_execution (apply_plan p rs) c ts <-> infinite_execution p c ts.
Proof.
  intros p rs Hmatch c ts. split; intro Hinf.
  - eapply infinite_execution_transport; [| exact Hinf].
    apply apply_plan_step. exact Hmatch.
  - eapply infinite_execution_transport; [| exact Hinf].
    intro s. symmetry. apply apply_plan_step. exact Hmatch.
Qed.

Definition install (p : program) (pc : nat) (body : region) : program :=
  fun location => if Nat.eqb location pc then Some body else p location.

Definition single_plan (pc : nat) (r : guarded_rewrite) : plan :=
  fun location => if Nat.eqb location pc then Some r else None.

Lemma single_plan_matches :
  forall context pc r,
    plan_matches (install context pc (original r)) (single_plan pc r).
Proof.
  intros context pc r location r' H.
  unfold single_plan in H. unfold install.
  destruct (Nat.eqb location pc); inversion H; reflexivity.
Qed.

(** An arbitrary surrounding CFG is quantified here, including back-edges
    and multiple outgoing edges. Entry into region interiors is impossible
    by construction and must be checked when adapting this to a real IR. *)
Theorem contextual_replacement :
  forall context pc r c t c',
    execution (apply_plan (install context pc (original r)) (single_plan pc r))
              c t c' <->
    execution (install context pc (original r)) c t c'.
Proof.
  intros. apply whole_program_finite. apply single_plan_matches.
Qed.

Theorem contextual_replacement_infinite :
  forall context pc r c ts,
    infinite_execution
      (apply_plan (install context pc (original r)) (single_plan pc r)) c ts <->
    infinite_execution (install context pc (original r)) c ts.
Proof.
  intros. apply whole_program_infinite. apply single_plan_matches.
Qed.
End Framework.
