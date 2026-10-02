From Stdlib Require Import ZArith Bool List Lia.
From Guard Require Import GuardedRegion Examples Presumption Synthesis.
Import ListNotations.
Open Scope Z_scope.
Set Implicit Arguments.

Module P := Presumption.
Module G := Synthesis.

Definition view (s : store) : P.state :=
  P.State (fun _ => input_value s)
    (fun i => P.Pointer 0 (Z.of_nat
      (if Nat.eqb i 0 then left_address s else right_address s)))
    (fun _ => Z.of_nat (length (memory s))).

Definition no_wrap : P.presumption :=
  P.Atomic (P.NoOverflow (P.Sum (P.Scalar 0) (P.Literal 1))).

Lemma no_wrap_implies_range : forall s,
  P.holds 256 (view s) no_wrap -> 0 <= input_value s < 255.
Proof.
  intros s H. unfold P.holds, no_wrap in H. simpl in H.
  apply andb_true_iff in H as [Hinputs Hsum].
  apply andb_true_iff in Hinputs as [Hx _].
  apply P.word_range_spec in Hx. apply P.word_range_spec in Hsum. lia.
Qed.

Definition no_wrap_encoding : @G.presumption_encoding store 256 view no_overflow.
Proof.
  refine {| G.encoded_presumption := no_wrap |}.
  intro s. split.
  - apply no_wrap_implies_range.
  - intro H. unfold no_overflow in H.
    unfold P.holds, no_wrap. simpl.
    repeat rewrite andb_true_iff. repeat split;
      apply P.word_range_spec; lia.
Defined.

(** The branch is unreachable only under the synthesized no-wrap condition.
    On wrapping input the original emits an event and traps, making an
    unconditional rewrite observably incorrect in control and trace. *)
Definition conditional_branch_source (next : nat) (s : store)
  : @transfer store Z :=
  if ((input_value s + 1) mod 256 <? input_value s)
  then Transfer [900] Trap (with_result s 1)
  else Transfer [] (Jump next) (with_result s 0).

Definition conditional_branch_candidate (next : nat) (s : store)
  : @transfer store Z := Transfer [] (Jump next) (with_result s 0).

Lemma conditional_branch_correct : forall next s,
  P.holds 256 (view s) no_wrap ->
  conditional_branch_candidate next s = conditional_branch_source next s.
Proof.
  intros next s H. apply no_wrap_implies_range in H.
  unfold conditional_branch_source, conditional_branch_candidate.
  rewrite Z.mod_small by lia.
  assert (Hfalse : (input_value s + 1 <? input_value s) = false).
  { apply Z.ltb_ge. lia. }
  rewrite Hfalse. reflexivity.
Qed.

Definition conditional_branch_rewrite (next : nat) : @guarded_rewrite store Z.
Proof.
  refine (@G.encoded_rewrite store Z 256 view no_overflow no_wrap_encoding
    (conditional_branch_source next) (conditional_branch_candidate next) _).
  intros s H. apply conditional_branch_correct.
  apply (proj2 (G.encoding_correct no_wrap_encoding s)). exact H.
Defined.

(** In this example the branch condition is false for every state, so the
    optimization presumption is Truth, rather than an impossible presumption. *)
Definition always_dead_source (next : nat) (s : store) : @transfer store Z :=
  if input_value s <? input_value s
  then Transfer [901] Trap s
  else Transfer [] (Jump next) (with_result s 7).

Definition always_dead_candidate (next : nat) (s : store) : @transfer store Z :=
  Transfer [] (Jump next) (with_result s 7).

Lemma always_dead_correct : forall next s,
  P.holds 256 (view s) P.Truth ->
  always_dead_candidate next s = always_dead_source next s.
Proof.
  intros. unfold always_dead_source, always_dead_candidate.
  rewrite Z.ltb_irrefl. reflexivity.
Qed.

Definition always_dead_rewrite (next : nat) : @guarded_rewrite store Z :=
  @G.synthesized_rewrite store Z 256 view P.Truth
    (always_dead_source next) (always_dead_candidate next)
    (always_dead_correct next).

(** A contradictory optimization presumption must also be supported. It
    licenses no fast-path execution, even if a local proof is vacuous. *)
Definition impossible_presumption : P.presumption :=
  P.Both (P.Atomic (P.LessEqual (P.Scalar 0) (P.Literal 5)))
         (P.Atomic (P.LessEqual (P.Literal 10) (P.Scalar 0))).

Lemma impossible_never_holds : forall modulus s,
  ~ P.holds modulus s impossible_presumption.
Proof.
  intros modulus s H. unfold P.holds, impossible_presumption in H. simpl in H.
  apply andb_true_iff in H as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. lia.
Qed.

Theorem impossible_guard_never_accepts : forall modulus s,
  G.accepts modulus s (G.synthesize impossible_presumption) = false.
Proof.
  intros modulus s.
  destruct (G.accepts modulus s (G.synthesize impossible_presumption)) eqn:H;
    try reflexivity.
  apply G.synthesized_accepts_sound in H.
  exfalso. eapply impossible_never_holds. exact H.
Qed.

Definition impossible_rewrite (next : nat) : @guarded_rewrite store Z.
Proof.
  refine (@G.synthesized_rewrite store Z 256 view impossible_presumption
    (always_dead_source next) (fun s => Transfer [999] Trap s) _).
  intros s H. exfalso. eapply impossible_never_holds. exact H.
Defined.

Definition memory_presumption : P.presumption :=
  P.Both (P.Atomic (P.InBounds 0 (P.Literal 1)))
  (P.Both (P.Atomic (P.InBounds 1 (P.Literal 1)))
          (P.Atomic (P.Disjoint 0 (P.Literal 1) 1 (P.Literal 1)))).

Lemma memory_presumption_implies_no_alias : forall s,
  P.holds 256 (view s) memory_presumption -> no_alias s.
Proof.
  intros s H. unfold P.holds, memory_presumption in H. simpl in H.
  apply andb_true_iff in H as [Hp Hrest].
  apply andb_true_iff in Hrest as [Hq Hsep].
  unfold P.bounds_meaning, P.disjoint_meaning, view in Hp, Hq, Hsep.
  simpl in Hp, Hq, Hsep.
  repeat rewrite andb_true_iff in Hp, Hq.
  destruct Hp as [[_ _] Hp]. destruct Hq as [[_ _] Hq].
  apply Z.leb_le in Hp. apply Z.leb_le in Hq.
  assert (Hneq : left_address s <> right_address s).
  { intro Heq. rewrite Heq in Hsep.
    rewrite orb_true_iff in Hsep. destruct Hsep as [Hsep | Hsep];
      apply Z.leb_le in Hsep; lia. }
  unfold no_alias. repeat split; try exact Hneq; lia.
Qed.

Lemma no_alias_implies_memory_presumption : forall s,
  no_alias s -> P.holds 256 (view s) memory_presumption.
Proof.
  intros s [Hp [Hq Hneq]].
  unfold P.holds, memory_presumption. simpl.
  unfold P.bounds_meaning, P.disjoint_meaning, view. simpl.
  repeat rewrite andb_true_iff. repeat split; try (apply Z.leb_le; lia).
  rewrite orb_true_iff.
  destruct (Nat.lt_ge_cases (left_address s) (right_address s)).
  - left. apply Z.leb_le. lia.
  - right. apply Z.leb_le. lia.
Qed.

Definition alias_encoding : @G.presumption_encoding store 256 view no_alias.
Proof.
  refine {| G.encoded_presumption := memory_presumption |}.
  intro s. split.
  - apply memory_presumption_implies_no_alias.
  - apply no_alias_implies_memory_presumption.
Defined.

Definition synthesized_alias_rewrite (next : nat) : @guarded_rewrite store Z.
Proof.
  refine (@G.encoded_rewrite store Z 256 view no_alias alias_encoding
    (alias_original next) (alias_optimized next) _).
  apply alias_conditional_correct.
Defined.

Definition source_program (pc : nat) : option (@region store Z) :=
  match pc with
  | O => Some (fun s => Transfer [100] (Jump 1) s)
  | S O => Some (conditional_branch_source 2)
  | S (S O) => Some (alias_original 3)
  | S (S (S O)) => Some (always_dead_source 4)
  | S (S (S (S O))) =>
      Some (fun s => Transfer [result_value s] (Return 0) s)
  | _ => None
  end.

Definition synthesized_plan (pc : nat) : option (@guarded_rewrite store Z) :=
  match pc with
  | S O => Some (conditional_branch_rewrite 2)
  | S (S O) => Some (synthesized_alias_rewrite 3)
  | S (S (S O)) => Some (always_dead_rewrite 4)
  | _ => None
  end.

Lemma synthesized_plan_matches : plan_matches source_program synthesized_plan.
Proof.
  intros pc r H. destruct pc as [| [| [| [| pc]]]];
    simpl in H; try discriminate; inversion H; reflexivity.
Qed.

Theorem synthesized_whole_program_correct : forall c t c',
  execution (apply_plan source_program synthesized_plan) c t c' <->
  execution source_program c t c'.
Proof.
  intros. apply whole_program_finite. apply synthesized_plan_matches.
Qed.

Theorem synthesized_whole_program_infinite : forall c ts,
  infinite_execution (apply_plan source_program synthesized_plan) c ts <->
  infinite_execution source_program c ts.
Proof.
  intros. apply whole_program_infinite. apply synthesized_plan_matches.
Qed.

Example flag_records_wrapping_value :
  G.evaluate 256 (view wrapping_input) (P.Sum (P.Scalar 0) (P.Literal 1)) =
  G.ArithmeticResult 0 false.
Proof. reflexivity. Qed.

Example failed_comparison_is_not_false :
  G.execute 256 (view wrapping_input)
    (G.synthesize (P.Negation
      (P.Atomic (P.LessEqual (P.Sum (P.Scalar 0) (P.Literal 1)) (P.Literal 255)))))
  = None.
Proof. reflexivity. Qed.

Example explicit_overflow_predicate_can_be_negated :
  G.execute 256 (view wrapping_input)
    (G.synthesize (P.Negation no_wrap)) = Some true.
Proof. reflexivity. Qed.

Example disjunction_skips_unneeded_failing_check :
  G.execute 256 (view wrapping_input)
    (G.synthesize (P.Either P.Truth
      (P.Atomic (P.LessEqual (P.Sum (P.Scalar 0) (P.Literal 1)) (P.Literal 255)))))
  = Some true.
Proof. reflexivity. Qed.

Example conditional_dead_branch_fast_path :
  check (conditional_branch_rewrite 2) safe_input = true.
Proof. reflexivity. Qed.

Example conditional_dead_branch_fallback :
  check (conditional_branch_rewrite 2) wrapping_input = false.
Proof. reflexivity. Qed.

Example always_dead_branch_fast_path :
  check (always_dead_rewrite 4) wrapping_input = true.
Proof. reflexivity. Qed.

Example dead_branch_safe_complete_run :
  run 5 (apply_plan source_program synthesized_plan) (Running 0 safe_input) =
  ([100; 7], Halted 0 (Store 254 7 0 1 [1; 2])).
Proof. reflexivity. Qed.

Example dead_branch_wrapping_complete_run :
  run 5 (apply_plan source_program synthesized_plan) (Running 0 wrapping_input) =
  ([100; 900], Faulted (Store 255 1 0 1 [0; 0])).
Proof. reflexivity. Qed.

Print Assumptions impossible_guard_never_accepts.
Print Assumptions conditional_branch_correct.
Print Assumptions no_wrap_encoding.
Print Assumptions alias_encoding.
Print Assumptions synthesized_whole_program_correct.
Print Assumptions synthesized_whole_program_infinite.
