From Stdlib Require Import List Bool ZArith Lia.
From polcert.polygen Require Import InstrTy Loop.
From Guard Require Import PolCertLoopGuard.
Import ListNotations.
Set Implicit Arguments.

(** Insert a private derived parameter after the active iterator prefix.
    Instruction operands retain their values, so neither memory effects nor
    the instruction semantics need to change. *)
Module PolCertParameterExtensionFor (I : INSTR) (M : LOOP_MODEL I).
Module L := M.
Fixpoint lift_expression cut expression :=
  match expression with
  | L.Constant value => L.Constant value
  | L.Var index => L.Var (if Nat.leb cut index then S index else index)
  | L.Sum a b => L.Sum (lift_expression cut a) (lift_expression cut b)
  | L.Mult factor a => L.Mult factor (lift_expression cut a)
  | L.Div a divisor => L.Div (lift_expression cut a) divisor
  | L.Mod a divisor => L.Mod (lift_expression cut a) divisor
  | L.Max a b => L.Max (lift_expression cut a) (lift_expression cut b)
  | L.Min a b => L.Min (lift_expression cut a) (lift_expression cut b) end.
Fixpoint lift_test cut test :=
  match test with
  | L.LE a b => L.LE (lift_expression cut a) (lift_expression cut b)
  | L.EQ a b => L.EQ (lift_expression cut a) (lift_expression cut b)
  | L.And a b => L.And (lift_test cut a) (lift_test cut b)
  | L.Or a b => L.Or (lift_test cut a) (lift_test cut b)
  | L.Not a => L.Not (lift_test cut a)
  | L.TConstantTest value => L.TConstantTest value end.
Fixpoint lift_statement cut statement :=
  match statement with
  | L.Loop lower upper body => L.Loop (lift_expression cut lower)
      (lift_expression cut upper) (lift_statement (S cut) body)
  | L.Instr instruction arguments => L.Instr instruction (map (lift_expression cut) arguments)
  | L.Guard test body => L.Guard (lift_test cut test) (lift_statement cut body)
  | L.Seq statements => L.Seq (lift_statements cut statements) end
with lift_statements cut statements :=
  match statements with
  | L.SNil => L.SNil
  | L.SCons head tail => L.SCons (lift_statement cut head) (lift_statements cut tail) end.

Lemma inserted_nth prefix environment value index :
  nth (if Nat.leb (length prefix) index then S index else index)
    (prefix ++ value::environment) 0%Z = nth index (prefix ++ environment) 0%Z.
Proof.
  revert index; induction prefix as [|head tail IH]; intros [|index]; cbn; auto.
  specialize (IH index).
  destruct (Nat.leb (length tail) index); cbn in *; exact IH.
Qed.
Lemma lift_expression_exact expression : forall prefix environment value,
  L.eval_expr (prefix ++ value::environment) (lift_expression (length prefix) expression) =
  L.eval_expr (prefix ++ environment) expression.
Proof.
  induction expression; intros; cbn [lift_expression L.eval_expr];
    try rewrite IHexpression; try rewrite IHexpression1; try rewrite IHexpression2;
    try reflexivity.
  apply inserted_nth.
Qed.
Lemma lift_test_exact test : forall prefix environment value,
  L.eval_test (prefix ++ value::environment) (lift_test (length prefix) test) =
  L.eval_test (prefix ++ environment) test.
Proof.
  induction test; intros; cbn [lift_test L.eval_test];
    try rewrite !lift_expression_exact; try rewrite IHtest;
    try rewrite IHtest1; try rewrite IHtest2; reflexivity.
Qed.
Lemma lifted_arguments_exact arguments prefix environment value :
  map (L.eval_expr (prefix ++ value::environment)) (map (lift_expression (length prefix)) arguments) =
  map (L.eval_expr (prefix ++ environment)) arguments.
Proof. rewrite map_map; apply map_ext; intro expression; apply lift_expression_exact. Qed.

Scheme extension_statement_ind := Induction for L.stmt Sort Prop
with extension_statements_ind := Induction for L.stmt_list Sort Prop.
Combined Scheme extension_ind from extension_statement_ind, extension_statements_ind.
Definition statement_contract statement := forall prefix environment value before after,
  L.loop_semantics statement (prefix ++ environment) before after <->
  L.loop_semantics (lift_statement (length prefix) statement)
    (prefix ++ value::environment) before after.
Definition statements_contract statements := forall prefix environment value before after,
  L.loop_semantics (L.Seq statements) (prefix ++ environment) before after <->
  L.loop_semantics (L.Seq (lift_statements (length prefix) statements))
    (prefix ++ value::environment) before after.

Theorem parameter_extension_contracts :
  (forall statement, statement_contract statement) /\
  (forall statements, statements_contract statements).
Proof.
  apply extension_ind.
  - intros lower upper body IH prefix environment value before after.
    cbn [lift_statement]; split; intro RUN; inversion RUN; subst.
    + apply L.LLoop; rewrite !lift_expression_exact.
      eapply I.IterSem.iter_semantics_map; [|eassumption].
      intros iterator first last _ STEP.
      apply (proj1 (IH (iterator::prefix) environment value first last)); exact STEP.
    + apply L.LLoop.
      match goal with ITER : I.IterSem.iter_semantics _ _ _ _ |- _ =>
        rewrite !lift_expression_exact in ITER end.
      eapply I.IterSem.iter_semantics_map; [|eassumption].
      intros iterator first last _ STEP.
      apply (proj2 (IH (iterator::prefix) environment value first last)); exact STEP.
  - intros instruction arguments prefix environment value before after.
    cbn [lift_statement]; split; intro RUN; inversion RUN; subst;
      eapply L.LInstr; rewrite lifted_arguments_exact in *; eassumption.
  - intros statements IH; exact IH.
  - intros test body IH prefix environment value before after.
    cbn [lift_statement]; split; intro RUN; inversion RUN; subst.
    + apply L.LGuardTrue; [apply (proj1 (IH prefix environment value before after)); assumption|].
      rewrite lift_test_exact; assumption.
    + apply L.LGuardFalse; rewrite lift_test_exact; assumption.
    + apply L.LGuardTrue; [apply (proj2 (IH prefix environment value before after)); assumption|].
      rewrite lift_test_exact in *; assumption.
    + apply L.LGuardFalse; rewrite lift_test_exact in *; assumption.
  - intros prefix environment value before after.
    cbn [lift_statements]; split; intro RUN; inversion RUN; constructor.
  - intros head HEAD tail TAIL prefix environment value before after.
    cbn [lift_statements]; split; intro RUN; inversion RUN; subst; eapply L.LSeq.
    + apply (proj1 (HEAD prefix environment value _ _)); eassumption.
    + apply (proj1 (TAIL prefix environment value _ _)); eassumption.
    + apply (proj2 (HEAD prefix environment value _ _)); eassumption.
    + apply (proj2 (TAIL prefix environment value _ _)); eassumption.
Qed.
Theorem parameter_extension_exact statement environment value before after :
  L.loop_semantics (lift_statement 0 statement) (value::environment) before after <->
  L.loop_semantics statement environment before after.
Proof.
  symmetry; exact (proj1 parameter_extension_contracts statement [] environment value before after).
Qed.
End PolCertParameterExtensionFor.
