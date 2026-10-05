From Stdlib Require Import Bool List.
From compcert.common Require Import Values Memory Events Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts ClightGuard ClightCondition.
From GuardInterface Require Import GuardInterface GuardedRewrite.
Set Implicit Arguments.

(** Every test that may be reached is defined. The finite tree and atomic,
    read-only Clight expression semantics then describe a safe dispatch.
    This is stronger than merely exhibiting one completed check path. *)
Fixpoint readonly_tree_safe (entry : clight_entry) (tree : decision_tree) : Prop :=
  match tree with
  | Decision _ => True
  | Test a yes no =>
      (exists accepted, expression_test a entry accepted) /\
      forall accepted, expression_test a entry accepted ->
        readonly_tree_safe entry (if accepted then yes else no)
  end.

Lemma readonly_tree_available tree : forall entry, readonly_tree_safe entry tree ->
  exists accepted, decision_run entry tree accepted.
Proof.
  induction tree as [answer|a yes YES no NO]; intros entry SAFE.
  - exists answer; constructor.
  - destruct SAFE as [[choice TEST] SAFE].
    destruct choice.
    + destruct (YES entry (SAFE true TEST)) as [answer RUN].
      exists answer; econstructor; [exact TEST|exact RUN].
    + destruct (NO entry (SAFE false TEST)) as [answer RUN].
      exists answer; econstructor; [exact TEST|exact RUN].
Qed.

Lemma compiled_tree_safe A I E
  (P : @check_primitives clight_entry A decision_language I E) premise :
  forall yes no unknown entry, I entry ->
  readonly_tree_safe entry yes -> readonly_tree_safe entry no -> readonly_tree_safe entry unknown ->
  readonly_tree_safe entry (compile_condition P premise yes no unknown).
Proof.
  induction premise; intros yes no unknown entry DOMAIN YES NO UNKNOWN;
    cbn [compile_condition decision_language conditional].
  - destruct value; assumption.
  - destruct (E atom entry) as [value|] eqn:VALUE.
    + split.
      * exists true; apply (proj2 (validity_test_correct P atom entry true DOMAIN)).
        rewrite VALUE; reflexivity.
      * intros accepted CHECK; apply (proj1 (validity_test_correct P atom entry accepted DOMAIN)) in CHECK.
        rewrite VALUE in CHECK; cbn in CHECK; subst accepted; cbn; split.
        -- exists value; apply (proj2 (value_test_correct P atom entry value DOMAIN VALUE)); reflexivity.
        -- intros accepted CHECK; apply (proj1 (value_test_correct P atom entry accepted DOMAIN VALUE)) in CHECK.
           subst accepted; destruct value; assumption.
    + split.
      * exists false; apply (proj2 (validity_test_correct P atom entry false DOMAIN)).
        rewrite VALUE; reflexivity.
      * intros accepted CHECK; apply (proj1 (validity_test_correct P atom entry accepted DOMAIN)) in CHECK.
        rewrite VALUE in CHECK; cbn in CHECK; subst accepted; exact UNKNOWN.
  - apply IHpremise1; auto; apply IHpremise2; assumption.
  - apply IHpremise1; auto; apply IHpremise2; assumption.
  - apply IHpremise; assumption.
Qed.

Definition clight_fragment_run fe (body : statement) entry observed :=
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    body (fragment_trace observed) (fragment_temps observed)
    (fragment_memory observed) (fragment_outcome observed).

Lemma readonly_tree_execution_exact fe tree yes no entry observed :
  clight_fragment_run fe (tree_statement tree yes no) entry observed <->
  exists accepted, decision_run entry tree accepted /\
    clight_fragment_run fe (if accepted then yes else no) entry observed.
Proof.
  induction tree as [answer|a left LEFT right RIGHT].
  - cbn [tree_statement]; split.
    + intro RUN; exists answer; split; [constructor|exact RUN].
    + intros [accepted [CHECK RUN]]; inversion CHECK; subst; exact RUN.
  - cbn [tree_statement]; split.
    + intro RUN; unfold clight_fragment_run in RUN; inversion RUN; subst.
      match goal with
      | BOOL : bool_val ?value (typeof a) (entry_memory entry) = Some ?choice,
        EVAL : eval_expr _ _ _ _ a ?value,
        BRANCH : exec_stmt _ _ _ _ _ (if ?choice then _ else _) _ _ _ _ |- _ =>
          assert (CHECK : expression_test a entry choice) by (exists value; auto);
          destruct choice;
          [destruct (proj1 LEFT BRANCH) as [accepted [PATH LEAF]];
           exists accepted; split; [eapply run_test with (b := true); eauto|exact LEAF] |
           destruct (proj1 RIGHT BRANCH) as [accepted [PATH LEAF]];
           exists accepted; split; [eapply run_test with (b := false); eauto|exact LEAF]]
      end.
    + intros [accepted [CHECK RUN]]; unfold clight_fragment_run in *.
      destruct entry as [ge locals temps memory]; cbn in CHECK, RUN |- *.
      eapply decision_fragment_run with (t := Test a left right) (b := accepted); eassumption.
Qed.

Section HOST.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Context {O : Type} (observe : fragment_observation -> O -> Prop).

(** Observation saturation avoids requiring equality of private temporaries
    or of the implementation representation of CompCert memories. The language
    still owes its context compatibility proof for the selected observation. *)
Definition readonly_clight_runs body entry observed :=
  exists raw, clight_fragment_run fe body entry raw /\ observe raw observed.
Definition readonly_clight_checks tree entry accepted checked :=
  decision_run entry tree accepted /\ checked = entry.

Definition readonly_clight_host : guard_host clight_entry.
Proof.
  refine {| code := statement; check := decision_tree; observation := O;
    runs := readonly_clight_runs; checks := readonly_clight_checks;
    check_safe := fun tree entry => readonly_tree_safe entry tree;
    select := tree_statement |}.
  intros tree yes no entry observed; split.
  - intros [raw [EXEC OBSERVE]]; apply readonly_tree_execution_exact in EXEC.
    destruct EXEC as [accepted [CHECK RUN]].
    exists accepted, entry; split; [split; [exact CHECK|reflexivity]|].
    exists raw; auto.
  - intros [accepted [checked [[CHECK SAME] [raw [RUN OBSERVE]]]]]; subst checked.
    exists raw; split; [|exact OBSERVE].
    apply readonly_tree_execution_exact; exists accepted; auto.
Defined.

Definition synthesized_readonly_condition A I
  (D : property_dimension clight_entry A I)
  (P : check_primitives decision_language I (decide_atom D)) premise :
  readonly_condition readonly_clight_host I
    (fun entry => formula_property (atom_property D) premise entry) (synthesize_tree P premise).
Proof.
  constructor.
  - intros entry DOMAIN; unfold synthesize_tree; apply compiled_tree_safe;
      [exact DOMAIN|constructor|constructor|constructor].
  - intros entry DOMAIN.
    assert (SAFE : readonly_tree_safe entry (synthesize_tree P premise)).
    { unfold synthesize_tree; apply compiled_tree_safe;
        [exact DOMAIN|constructor|constructor|constructor]. }
    destruct (@readonly_tree_available (synthesize_tree P premise) entry SAFE) as [accepted RUN].
    exists accepted, entry; split; [exact RUN|reflexivity].
  - intros entry accepted checked DOMAIN [RUN SAME]; split; [exact SAME|].
    intro ACCEPT; subst accepted; eapply synthesized_tree_property; eassumption.
Defined.
End HOST.

Print Assumptions readonly_tree_available.
Print Assumptions compiled_tree_safe.
Print Assumptions readonly_tree_execution_exact.
Print Assumptions readonly_clight_host.
Print Assumptions synthesized_readonly_condition.
