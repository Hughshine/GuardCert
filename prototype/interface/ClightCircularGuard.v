From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts ClightGuard ClightCondition ClightSameAddress
  ClightNoWrap ClightDecisionRule ClightMatrixGuard ClightPositiveCheck.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyTreeSynthesis
  ClightReadonlyLoadedTreeSynthesis ClightStableLoadGuard ClightReadonlyCellSwap ClightCircularMachine.
Set Implicit Arguments.

Definition circular_head_entry iterator bound entry := exists word upper b ofs,
  (entry_temps entry) ! iterator = Some (Vint word) /\
  (entry_temps entry) ! bound = Some (Vptr b ofs) /\
  Mem.loadv Mint32 (entry_memory entry) (Vptr b ofs) = Some (Vint upper).
Definition circular_guard_domain iterator out bound entry :=
  circular_head_entry iterator bound entry /\
  (expression_test (circular_loaded_test iterator bound) entry true -> address_domain out bound entry).
Definition circular_guard_property iterator out bound (_ : unit) entry :=
  expression_test (circular_loaded_test iterator bound) entry true /\ cell_pair_apart out bound entry.
Definition circular_head_flag iterator bound entry :=
  match (entry_temps entry) ! iterator, (entry_temps entry) ! bound with
  | Some (Vint word), Some (Vptr b ofs) =>
    match Mem.loadv Mint32 (entry_memory entry) (Vptr b ofs) with
    | Some (Vint upper) => negb (Int.eq word upper)
    | _ => false end
  | _, _ => false end.
Definition circular_guard_accept iterator out bound (_ : unit) entry :=
  circular_head_flag iterator bound entry && negb (address_accept out bound entry).
Definition circular_guard iterator out bound :=
  Test (circular_loaded_test iterator bound)
    (Test (same_address_guard out bound) (Decision false) (Decision true)) (Decision false).

Lemma circular_head_entry_test iterator bound entry : circular_head_entry iterator bound entry ->
  expression_test (circular_loaded_test iterator bound) entry (circular_head_flag iterator bound entry).
Proof.
  intros [word [upper [b [ofs [ITER [BOUND READ]]]]]].
  unfold circular_head_flag; rewrite ITER, BOUND, READ.
  exists (Val.of_bool (negb (Int.eq word upper))); split; [|apply bool_of_bool].
  eapply eval_Ebinop with (v1 := Vint word) (v2 := Vint upper).
  - constructor; exact ITER.
  - apply circular_word_load_eval with (b := b) (ofs := ofs); assumption.
  - reflexivity.
Qed.
Lemma circular_guard_run iterator out bound entry : circular_guard_domain iterator out bound entry ->
  decision_run entry (circular_guard iterator out bound) (circular_guard_accept iterator out bound tt entry).
Proof.
  intros [DOMAIN ADDRESSES]; pose proof (circular_head_entry_test DOMAIN) as TEST.
  unfold circular_guard, circular_guard_accept; eapply run_test; [exact TEST |].
  destruct (circular_head_flag iterator bound entry) eqn:ACTIVE; cbn; [|constructor].
  eapply run_test.
  - apply (proj2 (@address_guard_correct out bound entry _ (ADDRESSES TEST))); reflexivity.
  - destruct (address_accept out bound entry); constructor.
Qed.
Lemma circular_guard_sound iterator out bound a entry : circular_guard_domain iterator out bound entry ->
  circular_guard_accept iterator out bound a entry = true -> circular_guard_property iterator out bound a entry.
Proof.
  intros [DOMAIN ADDRESSES] ACCEPT; unfold circular_guard_accept in ACCEPT.
  apply andb_true_iff in ACCEPT as [ACTIVE APART].
  pose proof (circular_head_entry_test DOMAIN) as TEST; rewrite ACTIVE in TEST.
  split; [exact TEST | apply stable_addresses_apart; [apply ADDRESSES; exact TEST | exact APART]].
Qed.
Definition circular_dimension iterator out bound :=
  @positive_dimension clight_entry unit (circular_guard_domain iterator out bound)
    (circular_guard_property iterator out bound) (circular_guard_accept iterator out bound)
    (@circular_guard_sound iterator out bound).
Definition circular_primitives iterator out bound :=
  @positive_readonly_tree_primitives unit (circular_guard_domain iterator out bound)
    (circular_guard_property iterator out bound) (circular_guard_accept iterator out bound)
    (@circular_guard_sound iterator out bound) (fun _ => circular_guard iterator out bound)
    (fun a entry DOMAIN => match a with tt => circular_guard_run DOMAIN end).
Definition circular_condition fe O (observe : fragment_observation -> O -> Prop) iterator out bound :
  readonly_condition (readonly_clight_host fe observe) (circular_guard_domain iterator out bound)
    (circular_guard_property iterator out bound tt)
    (synthesize_decision_tree (circular_primitives iterator out bound) (Fact tt)).
Proof.
  change (readonly_condition (readonly_clight_host fe observe) (circular_guard_domain iterator out bound)
    (fun entry => formula_property (atom_property (circular_dimension iterator out bound)) (Fact tt) entry)
    (synthesize_decision_tree (circular_primitives iterator out bound) (Fact tt))).
  apply synthesized_loaded_tree_condition with (D := circular_dimension iterator out bound).
Defined.

Lemma circular_guard_synthesized iterator out bound :
  synthesize_decision_tree (circular_primitives iterator out bound) (Fact tt) = circular_guard iterator out bound.
Proof. reflexivity. Qed.

(** Defined guard comparisons come from one actual source store, rather than
    a completed execution of the enclosing loop. No progress premise occurs. *)
Theorem circular_domain_from_prefix temps ge locals iterator out bound le m final :
  expression_test (circular_loaded_test iterator bound) (Entry ge locals le m) true ->
  exec_stmt (adapter_entry temps) ge locals le m (circular_store out iterator) E0 le final Out_normal ->
  circular_guard_domain iterator out bound (Entry ge locals le m).
Proof.
  intros TEST STORE.
  destruct (circular_loaded_test_facts TEST) as [word [upper [b [ofs [ITER [BOUND [READ FLAG]]]]]]].
  destruct (circular_store_facts STORE) as [p [off [value [OUT WRITE]]]].
  split; [exists word, upper, b, ofs; auto | intros _].
  exists p, off, b, ofs; split; [exact OUT | split; [exact BOUND | split]].
  - apply writable_word_valid_pointer; exact (proj1 (@storev_word_facts _ _ _ _ _ WRITE)).
  - eapply loaded_address_valid; exact READ.
Qed.

Definition guarded_circular_candidate iterator out bound cache :=
  Ssequence (Sset cache (word_load bound))
    (circular_memory_loop iterator out (circular_cached_test iterator cache)).
Definition guarded_circular_region iterator out bound cache :=
  tree_statement (synthesize_decision_tree (circular_primitives iterator out bound) (Fact tt))
    (guarded_circular_candidate iterator out bound cache)
    (circular_memory_loop iterator out (circular_loaded_test iterator bound)).

Print Assumptions circular_guard_run.
Print Assumptions circular_guard_sound.
Print Assumptions circular_condition.
Print Assumptions circular_guard_synthesized.
Print Assumptions circular_domain_from_prefix.
