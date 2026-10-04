From Stdlib Require Import List Bool ZArith Lia.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_complement_test condition := match condition with
  | L.LE first second=>L.LE(L.Sum second(L.Constant 1)) first
  | other=>L.Not other end.
Lemma affine_complement_test_value condition environment :
  L.eval_test environment(affine_complement_test condition)=negb(L.eval_test environment condition).
Proof.
  destruct condition; cbn [affine_complement_test L.eval_test L.eval_expr]; try reflexivity.
  destruct(L.eval_expr environment e <=? L.eval_expr environment e0) eqn:FIRST;
    destruct(L.eval_expr environment e0+1 <=? L.eval_expr environment e) eqn:SECOND;
    try reflexivity; apply Z.leb_le in FIRST || apply Z.leb_gt in FIRST;
    apply Z.leb_le in SECOND || apply Z.leb_gt in SECOND; lia.
Qed.
Print Assumptions affine_complement_test_value.

Definition affine_split_pair condition body :=
  L.Seq(L.SCons(L.Guard condition body)
    (L.SCons(L.Guard(affine_complement_test condition) body)L.SNil)).

Lemma affine_two_statements first second environment before after :
  L.loop_semantics(L.Seq(L.SCons first(L.SCons second L.SNil))) environment before after <->
  exists middle, L.loop_semantics first environment before middle /\
                 L.loop_semantics second environment middle after.
Proof.
  split.
  - intro RUN; inversion RUN; subst.
    match goal with H:L.loop_semantics(L.Seq(L.SCons _ _)) _ _ _ |- _ => inversion H; subst end.
    match goal with H:L.loop_semantics(L.Seq L.SNil) _ _ _ |- _ => inversion H; subst end.
    eauto.
  - intros [middle [FIRST SECOND]]; eapply L.LSeq; [exact FIRST|].
    eapply L.LSeq; [exact SECOND|constructor].
Qed.

Lemma affine_guard_execution condition body environment before after :
  L.loop_semantics(L.Guard condition body) environment before after <->
  if L.eval_test environment condition then L.loop_semantics body environment before after else before=after.
Proof.
  destruct(L.eval_test environment condition) eqn:VALUE; split; intro RUN.
  - inversion RUN; subst; congruence || assumption.
  - apply L.LGuardTrue; assumption.
  - inversion RUN; subst; congruence || reflexivity.
  - subst after; apply L.LGuardFalse; exact VALUE.
Qed.

Theorem affine_split_pair_execution condition body environment before after :
  L.loop_semantics(affine_split_pair condition body) environment before after <->
  L.loop_semantics body environment before after.
Proof.
  unfold affine_split_pair; rewrite affine_two_statements.
  setoid_rewrite affine_guard_execution.
  rewrite affine_complement_test_value; destruct(L.eval_test environment condition); cbn;
    split; [intros [middle [RUN SAME]]; subst; exact RUN|intro RUN; eauto|
            intros [middle [SAME RUN]]; subst; exact RUN|intro RUN; eauto].
Qed.

Fixpoint affine_partitioned_source condition source := match source with
  | L.Loop lower upper body=>L.Loop lower upper(affine_partitioned_source condition body)
  | body=>affine_split_pair condition body end.

Theorem affine_partitioned_source_execution condition source : forall environment before after,
  L.loop_semantics(affine_partitioned_source condition source) environment before after <->
  L.loop_semantics source environment before after.
Proof.
  induction source as [lower upper body IH|instruction arguments|statements|test body IH];
    intros environment before after; cbn [affine_partitioned_source].
  - split.
    + intro RUN; inversion RUN; subst; apply L.LLoop.
      eapply Iter.iter_semantics_map; [|eassumption].
      intros value first final MEMBER STEP; apply(proj1(IH(value::environment) first final)); exact STEP.
    + intro RUN; inversion RUN; subst; apply L.LLoop.
      eapply Iter.iter_semantics_map; [|eassumption].
      intros value first final MEMBER STEP; apply(proj2(IH(value::environment) first final)); exact STEP.
  - apply affine_split_pair_execution.
  - apply affine_split_pair_execution.
  - apply affine_split_pair_execution.
Qed.
Print Assumptions affine_partitioned_source_execution.

Definition affine_partitioned_sources conditions source :=
  fold_right affine_partitioned_source source conditions.
Theorem affine_partitioned_sources_execution conditions source : forall environment before after,
  L.loop_semantics(affine_partitioned_sources conditions source) environment before after <->
  L.loop_semantics source environment before after.
Proof.
  induction conditions; intros environment before after; [reflexivity|].
  unfold affine_partitioned_sources; cbn [fold_right].
  rewrite affine_partitioned_source_execution; apply IHconditions.
Qed.
Print Assumptions affine_partitioned_sources_execution.
