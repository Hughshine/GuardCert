(** Count expression-test executions, not instructions or elapsed time. Each
    retained test stays at its original decision prefix. The cost argument
    therefore uses the same partial, readonly Clight semantics as correctness. *)
From Stdlib Require Import List Arith Lia.
From Guard Require Import ClightCondition.
From GuardInterface Require Import ClightReadonlyProbeMemo ClightReadonlyLoadedTreeSynthesis.
Import ListNotations.
Set Implicit Arguments.

Inductive readonly_tree_work entry : decision_tree -> bool -> nat -> Prop :=
| work_decision answer : readonly_tree_work entry (Decision answer) answer 0
| work_test expression yes no choice answer count :
    expression_test expression entry choice ->
    readonly_tree_work entry (if choice then yes else no) answer count ->
    readonly_tree_work entry (Test expression yes no) answer (S count).

Lemma readonly_tree_work_run entry tree answer count :
  readonly_tree_work entry tree answer count -> decision_run entry tree answer.
Proof. intro WORK; induction WORK; [constructor|eapply run_test; eassumption]. Qed.

Lemma readonly_tree_run_work entry tree answer : decision_run entry tree answer ->
  exists count, readonly_tree_work entry tree answer count.
Proof.
  intro RUN; induction RUN.
  - exists 0; constructor.
  - destruct IHRUN as [count WORK]; exists (S count); eapply work_test; eassumption.
Qed.

Theorem memo_readonly_tree_work_bound tree : forall facts entry answer count,
  readonly_probe_facts entry facts -> readonly_tree_work entry tree answer count ->
  exists optimized_count,
    readonly_tree_work entry (memo_readonly_tree facts tree) answer optimized_count /\
    optimized_count <= count.
Proof.
  induction tree as [known|expression yes YES no NO]; intros facts entry answer count FACTS WORK.
  - inversion WORK; subst; exists 0; split; [constructor|lia].
  - inversion WORK as [|probe first second choice result steps TEST CHILD]; subst.
    cbn [memo_readonly_tree].
    destruct (readonly_probe_lookup expression facts) as [known|] eqn:LOOKUP.
    + pose proof (@readonly_probe_lookup_sound expression facts entry known FACTS LOOKUP) as EARLIER.
      assert (SAME : choice=known) by (eapply readonly_test_determinate; eassumption).
      subst choice; destruct known.
      * destruct (YES facts entry answer steps FACTS CHILD) as [optimized [RUN BOUND]].
        exists optimized; split; [exact RUN|lia].
      * destruct (NO facts entry answer steps FACTS CHILD) as [optimized [RUN BOUND]].
        exists optimized; split; [exact RUN|lia].
    + destruct choice.
      * destruct (YES ((expression,true)::facts) entry answer steps
          ltac:(constructor; assumption) CHILD) as [optimized [RUN BOUND]].
        exists (S optimized); split; [eapply work_test; eassumption|lia].
      * destruct (NO ((expression,false)::facts) entry answer steps
          ltac:(constructor; assumption) CHILD) as [optimized [RUN BOUND]].
        exists (S optimized); split; [eapply work_test; eassumption|lia].
Qed.

Corollary memo_readonly_empty_work_bound tree entry answer count :
  readonly_tree_work entry tree answer count -> exists optimized_count,
  readonly_tree_work entry (memo_readonly_tree [] tree) answer optimized_count /\
  optimized_count <= count.
Proof. intro WORK; eapply memo_readonly_tree_work_bound; [constructor|exact WORK]. Qed.

Print Assumptions readonly_tree_work_run.
Print Assumptions readonly_tree_run_work.
Print Assumptions memo_readonly_tree_work_bound.
Print Assumptions memo_readonly_empty_work_bound.
