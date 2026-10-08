(** Reuse only facts obtained on the same readonly decision path. Clight
    expression determinacy includes loads at this unchanged entry state. No
    observation is moved earlier and no mutable-state cache is introduced. *)
From Stdlib Require Import List Bool.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightSyntaxEquality.
From GuardInterface Require Import ClightReadonlyLoadedTreeSynthesis.
Import ListNotations.
Set Implicit Arguments.

Fixpoint readonly_probe_lookup expression (facts : list (expr*bool)) :=
  match facts with
  | []=>None
  | (probe,answer)::rest=>
    if expression_eq expression probe then Some answer else readonly_probe_lookup expression rest
  end.
Definition readonly_probe_facts entry facts :=
  Forall (fun fact=>expression_test (fst fact) entry (snd fact)) facts.

Lemma readonly_probe_lookup_sound expression facts entry answer :
  readonly_probe_facts entry facts -> readonly_probe_lookup expression facts=Some answer ->
  expression_test expression entry answer.
Proof.
  induction facts as [|[probe known] rest IH]; intros FACTS LOOKUP; [discriminate|].
  inversion FACTS; subst; cbn [readonly_probe_lookup] in LOOKUP.
  destruct (expression_eq expression probe) as [SAME|DIFFERENT].
  - injection LOOKUP as <-; subst expression; assumption.
  - apply IH; assumption.
Qed.

Fixpoint memo_readonly_tree facts tree :=
  match tree with
  | Decision answer=>Decision answer
  | Test expression yes no=>
    match readonly_probe_lookup expression facts with
    | Some true=>memo_readonly_tree facts yes
    | Some false=>memo_readonly_tree facts no
    | None=>Test expression
        (memo_readonly_tree ((expression,true)::facts) yes)
        (memo_readonly_tree ((expression,false)::facts) no)
    end
  end.

Theorem memo_readonly_tree_exact tree : forall facts entry answer,
  readonly_probe_facts entry facts ->
  (decision_run entry (memo_readonly_tree facts tree) answer <-> decision_run entry tree answer).
Proof.
  induction tree as [known|expression yes YES no NO]; intros facts entry answer FACTS;
    cbn [memo_readonly_tree]; [reflexivity|].
  destruct (readonly_probe_lookup expression facts) as [known|] eqn:LOOKUP.
  - pose proof (@readonly_probe_lookup_sound expression facts entry known FACTS LOOKUP) as TEST.
    split.
    + intro RUN; eapply run_test with (b:=known); [exact TEST|].
      destruct known; [apply (proj1 (YES facts entry answer FACTS))|
        apply (proj1 (NO facts entry answer FACTS))]; exact RUN.
    + intro RUN; inversion RUN as [|probe first second choice result CHECK CHILD]; subst.
      assert (SAME : choice=known) by (eapply readonly_test_determinate; [exact CHECK|exact TEST]).
      subst choice; destruct known; [apply (proj2 (YES facts entry answer FACTS))|
        apply (proj2 (NO facts entry answer FACTS))]; exact CHILD.
  - split; intro RUN; inversion RUN as [|probe first second choice result CHECK CHILD]; subst;
      eapply run_test; [exact CHECK| |exact CHECK|].
    + destruct choice.
      * apply (proj1 (YES ((expression,true)::facts) entry answer ltac:(constructor; assumption))); exact CHILD.
      * apply (proj1 (NO ((expression,false)::facts) entry answer ltac:(constructor; assumption))); exact CHILD.
    + destruct choice.
      * apply (proj2 (YES ((expression,true)::facts) entry answer ltac:(constructor; assumption))); exact CHILD.
      * apply (proj2 (NO ((expression,false)::facts) entry answer ltac:(constructor; assumption))); exact CHILD.
Qed.

Corollary memo_readonly_empty_exact tree entry answer :
  decision_run entry (memo_readonly_tree [] tree) answer <-> decision_run entry tree answer.
Proof. apply memo_readonly_tree_exact; constructor. Qed.

Print Assumptions readonly_probe_lookup_sound.
Print Assumptions memo_readonly_tree_exact.
Print Assumptions memo_readonly_empty_exact.
