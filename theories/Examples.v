From Stdlib Require Import ZArith List Bool Lia Arith Streams.
From Guard Require Import GuardedRegion CheckedGuard.
Import ListNotations.
Open Scope Z_scope.
Set Implicit Arguments.

Record store := Store {
  input_value : Z;
  result_value : Z;
  left_address : nat;
  right_address : nat;
  memory : list Z
}.

Definition with_result (s : store) (z : Z) : store :=
  Store (input_value s) z (left_address s) (right_address s) (memory s).
Definition with_memory (s : store) (m : list Z) : store :=
  Store (input_value s) (result_value s) (left_address s) (right_address s) m.

(** Unsigned-word comparison can be folded only when the increment does
    not wrap. At 255 the original comparison is true and the fast path is
    false, so unconditional replacement is observably incorrect. *)
Definition overflow_original (next : nat) (s : store) : @transfer store Z :=
  Transfer [] (Jump next)
    (with_result s (if ((input_value s + 1) mod 256 <? input_value s)
                    then 1 else 0)).
Definition overflow_optimized (next : nat) (s : store) : @transfer store Z :=
  Transfer [] (Jump next) (with_result s 0).
Definition no_overflow (s : store) : Prop := 0 <= input_value s < 255.
Definition overflow_predicate :=
  Conjunction (LessEqual (Constant 0) (Input 0))
              (LessEqual (Add (Input 0) (Constant 1)) (Constant 255)).
Definition overflow_check (s : store) :=
  accepts (fun _ => input_value s) overflow_predicate.

Lemma overflow_check_sound : forall s,
  overflow_check s = true -> no_overflow s.
Proof.
  intros s H. unfold overflow_check in H.
  apply accepts_sound in H. unfold overflow_predicate in H.
  simpl in H. apply andb_true_iff in H as [Hlower Hupper].
  apply Z.leb_le in Hlower. apply Z.leb_le in Hupper.
  unfold no_overflow. lia.
Qed.

Lemma overflow_conditional_correct : forall next s,
  no_overflow s -> overflow_optimized next s = overflow_original next s.
Proof.
  intros next s H. unfold no_overflow in H.
  unfold overflow_optimized, overflow_original.
  rewrite Z.mod_small by lia.
  assert (Hcmp : (input_value s + 1 <? input_value s) = false).
  { apply Z.ltb_ge. lia. }
  rewrite Hcmp. reflexivity.
Qed.

Definition overflow_rewrite (next : nat) : @guarded_rewrite store Z.
Proof.
  refine {| original := overflow_original next;
            optimized := overflow_optimized next;
            assumption := no_overflow;
            check := overflow_check |}.
  - apply overflow_check_sound.
  - apply overflow_conditional_correct.
Defined.

Fixpoint write (address : nat) (value : Z) (m : list Z) : list Z :=
  match m, address with
  | [], _ => []
  | _ :: tail, O => value :: tail
  | head :: tail, S i => head :: write i value tail
  end.

Lemma writes_commute : forall m p q v w,
  p <> q -> write p v (write q w m) = write q w (write p v m).
Proof.
  induction m as [| head tail IH]; intros p q v w Hneq;
    destruct p, q; simpl; try reflexivity; try lia.
  f_equal. apply IH. lia.
Qed.

(** The guard includes bounds checks as well as distinct addresses. The toy
    heap is a list, not CompCert memory; no permissions or pointer provenance
    are claimed. All accepted writes are within the list. *)
Definition alias_original (next : nat) (s : store) : @transfer store Z :=
  Transfer [] (Jump next)
    (with_memory s (write (right_address s) 2
                    (write (left_address s) 1 (memory s)))).
Definition alias_optimized (next : nat) (s : store) : @transfer store Z :=
  Transfer [] (Jump next)
    (with_memory s (write (left_address s) 1
                    (write (right_address s) 2 (memory s)))).
Definition no_alias (s : store) : Prop :=
  (left_address s < length (memory s))%nat /\
  (right_address s < length (memory s))%nat /\
  left_address s <> right_address s.
Definition alias_check (s : store) : bool :=
  Nat.ltb (left_address s) (length (memory s)) &&
  Nat.ltb (right_address s) (length (memory s)) &&
  negb (Nat.eqb (left_address s) (right_address s)).

Lemma alias_check_sound : forall s, alias_check s = true -> no_alias s.
Proof.
  intros s H. unfold alias_check in H.
  apply andb_true_iff in H as [Hbounds Hneq].
  apply andb_true_iff in Hbounds as [Hp Hq].
  apply Nat.ltb_lt in Hp. apply Nat.ltb_lt in Hq.
  apply negb_true_iff in Hneq. apply Nat.eqb_neq in Hneq.
  unfold no_alias. auto.
Qed.

Lemma alias_conditional_correct : forall next s,
  no_alias s -> alias_optimized next s = alias_original next s.
Proof.
  intros next s [_ [_ Hneq]].
  unfold alias_optimized, alias_original.
  rewrite writes_commute by exact Hneq. reflexivity.
Qed.

Definition alias_rewrite (next : nat) : @guarded_rewrite store Z.
Proof.
  refine {| original := alias_original next;
            optimized := alias_optimized next;
            assumption := no_alias;
            check := alias_check |}.
  - apply alias_check_sound.
  - apply alias_conditional_correct.
Defined.

Definition demo_program (pc : nat) : option (@region store Z) :=
  match pc with
  | O => Some (fun s => Transfer [100] (Jump 1) s)
  | S O => Some (overflow_original 2)
  | S (S O) => Some (alias_original 3)
  | S (S (S O)) => Some (fun s => Transfer [result_value s] (Return 0) s)
  | _ => None
  end.

Definition demo_plan (pc : nat) : option (@guarded_rewrite store Z) :=
  match pc with
  | S O => Some (overflow_rewrite 2)
  | S (S O) => Some (alias_rewrite 3)
  | _ => None
  end.

Lemma demo_plan_matches : plan_matches demo_program demo_plan.
Proof.
  intros pc r H. destruct pc as [| [| [| pc]]];
    simpl in H; try discriminate; inversion H; reflexivity.
Qed.

Theorem demo_whole_program_correct : forall c t c',
  execution (apply_plan demo_program demo_plan) c t c' <->
  execution demo_program c t c'.
Proof.
  intros. apply whole_program_finite. apply demo_plan_matches.
Qed.

Definition safe_input := Store 254 99 0 1 [0; 0].
Definition wrapping_input := Store 255 99 0 1 [0; 0].
Definition aliasing_input := Store 12 99 0 0 [0; 0].

Example overflow_fast_path_selected : overflow_check safe_input = true.
Proof. reflexivity. Qed.
Example overflow_fallback_selected : overflow_check wrapping_input = false.
Proof. reflexivity. Qed.
Example alias_fast_path_selected : alias_check safe_input = true.
Proof. reflexivity. Qed.
Example alias_fallback_selected : alias_check aliasing_input = false.
Proof. reflexivity. Qed.

Example overflow_without_guard_is_wrong :
  final_state (overflow_original 2 wrapping_input) <>
  final_state (overflow_optimized 2 wrapping_input).
Proof. discriminate. Qed.
Example alias_without_guard_is_wrong :
  final_state (alias_original 3 aliasing_input) <>
  final_state (alias_optimized 3 aliasing_input).
Proof. discriminate. Qed.

(** The naive modular check accepts a wrapping input. The checked expression
    rejects it even though the mathematical comparison is false. *)
Example naive_guard_accepts_bad_input :
  (((255 + 1) mod 256) <=? 255) = true.
Proof. reflexivity. Qed.
Example checked_guard_rejects_bad_input :
  checked_test (fun _ => 255)
    (LessEqual (Add (Input 0) (Constant 1)) (Constant 255)) = None.
Proof. reflexivity. Qed.

Fixpoint run (fuel : nat) (p : @program store Z)
  (c : @configuration store) : list Z * @configuration store :=
  match fuel with
  | O => ([], c)
  | S n => match step p c with
           | None => ([], c)
           | Some (t, c') => let '(ts, c'') := run n p c' in (t ++ ts, c'')
           end
  end.

Example whole_program_safe_run :
  run 4 (apply_plan demo_program demo_plan) (Running 0 safe_input) =
  ([100; 0], Halted 0 (Store 254 0 0 1 [1; 2])).
Proof. reflexivity. Qed.
Example whole_program_wrapping_run :
  run 4 (apply_plan demo_program demo_plan) (Running 0 wrapping_input) =
  ([100; 1], Halted 0 (Store 255 1 0 1 [1; 2])).
Proof. reflexivity. Qed.
Example whole_program_aliasing_run :
  run 4 (apply_plan demo_program demo_plan) (Running 0 aliasing_input) =
  ([100; 0], Halted 0 (Store 12 0 0 0 [2; 0])).
Proof. reflexivity. Qed.

Definition silent_loop : @program store Z :=
  fun _ => Some (fun s => Transfer [] (Jump 0) s).

Lemma silent_loop_diverges : forall s,
  infinite_execution silent_loop (Running 0 s) (Streams.const []).
Proof.
  cofix CIH. intro s.
  rewrite (unfold_Stream (Streams.const [])). simpl.
  econstructor.
  - reflexivity.
  - apply CIH.
Qed.

Print Assumptions contextual_replacement.
Print Assumptions whole_program_infinite.
Print Assumptions checked_add_sound.
Print Assumptions accepts_sound.
Print Assumptions overflow_conditional_correct.
Print Assumptions alias_conditional_correct.
Print Assumptions demo_whole_program_correct.
