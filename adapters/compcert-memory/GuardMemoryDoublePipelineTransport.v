From Stdlib Require Import List ZArith Bool.
From GuardMemory Require Import GuardMemoryDoubleAssignment GuardMemoryDoubleMatmulInstr GuardMemoryDoubleMatmulLoopModel
  GuardMemoryDoublePolyhedral.
Import ListNotations.
Set Implicit Arguments.
Module SourceLoop := DoubleAssignmentLoop.
Module PipelineLoop := DoubleAssignmentIRs.Loop.

(** Bridge the existing generative Loop instances, retaining instructions.
    This is syntax transport into the actual extractor/codegen interface. *)
Fixpoint double_pipeline_expression expression : PipelineLoop.expr := match expression with
  | SourceLoop.Constant value => PipelineLoop.Constant value
  | SourceLoop.Sum first second => PipelineLoop.Sum (double_pipeline_expression first) (double_pipeline_expression second)
  | SourceLoop.Mult coefficient child => PipelineLoop.Mult coefficient (double_pipeline_expression child)
  | SourceLoop.Div child divisor => PipelineLoop.Div (double_pipeline_expression child) divisor
  | SourceLoop.Mod child divisor => PipelineLoop.Mod (double_pipeline_expression child) divisor
  | SourceLoop.Var index => PipelineLoop.Var index
  | SourceLoop.Max first second => PipelineLoop.Max (double_pipeline_expression first) (double_pipeline_expression second)
  | SourceLoop.Min first second => PipelineLoop.Min (double_pipeline_expression first) (double_pipeline_expression second) end.
Lemma double_pipeline_expression_value expression environment :
  PipelineLoop.eval_expr environment (double_pipeline_expression expression)=SourceLoop.eval_expr environment expression.
Proof. induction expression; cbn [double_pipeline_expression PipelineLoop.eval_expr SourceLoop.eval_expr]; congruence. Qed.
Fixpoint double_pipeline_test condition : PipelineLoop.test := match condition with
  | SourceLoop.LE first second => PipelineLoop.LE (double_pipeline_expression first) (double_pipeline_expression second)
  | SourceLoop.EQ first second => PipelineLoop.EQ (double_pipeline_expression first) (double_pipeline_expression second)
  | SourceLoop.And first second => PipelineLoop.And (double_pipeline_test first) (double_pipeline_test second)
  | SourceLoop.Or first second => PipelineLoop.Or (double_pipeline_test first) (double_pipeline_test second)
  | SourceLoop.Not child => PipelineLoop.Not (double_pipeline_test child)
  | SourceLoop.TConstantTest value => PipelineLoop.TConstantTest value end.
Lemma double_pipeline_test_value condition environment :
  PipelineLoop.eval_test environment (double_pipeline_test condition)=SourceLoop.eval_test environment condition.
Proof.
  induction condition; cbn [double_pipeline_test PipelineLoop.eval_test SourceLoop.eval_test];
    rewrite ?double_pipeline_expression_value; congruence.
Qed.
Fixpoint double_pipeline_statement source : PipelineLoop.stmt := match source with
  | SourceLoop.Loop lower upper body => PipelineLoop.Loop (double_pipeline_expression lower)
      (double_pipeline_expression upper) (double_pipeline_statement body)
  | SourceLoop.Instr instruction arguments => PipelineLoop.Instr instruction (map double_pipeline_expression arguments)
  | SourceLoop.Seq statements => PipelineLoop.Seq (double_pipeline_statements statements)
  | SourceLoop.Guard condition body => PipelineLoop.Guard (double_pipeline_test condition) (double_pipeline_statement body) end
with double_pipeline_statements sources : PipelineLoop.stmt_list := match sources with
  | SourceLoop.SNil => PipelineLoop.SNil
  | SourceLoop.SCons first rest => PipelineLoop.SCons (double_pipeline_statement first) (double_pipeline_statements rest) end.
Scheme double_source_statement_ind := Induction for SourceLoop.stmt Sort Prop
  with double_source_statements_ind := Induction for SourceLoop.stmt_list Sort Prop.
Combined Scheme double_source_syntax_ind from double_source_statement_ind,double_source_statements_ind.

Lemma double_pipeline_arguments_value arguments environment :
  map (PipelineLoop.eval_expr environment) (map double_pipeline_expression arguments)=
    map (SourceLoop.eval_expr environment) arguments.
Proof. rewrite map_map; apply map_ext; intro expression; apply double_pipeline_expression_value. Qed.
Lemma double_pipeline_execution_mutual :
  (forall source environment before after,
    SourceLoop.loop_semantics source environment before after <->
    PipelineLoop.loop_semantics (double_pipeline_statement source) environment before after) /\
  (forall sources environment before after,
    SourceLoop.loop_semantics (SourceLoop.Seq sources) environment before after <->
    PipelineLoop.loop_semantics (PipelineLoop.Seq (double_pipeline_statements sources)) environment before after).
Proof.
  apply double_source_syntax_ind.
  - intros lower upper body IH environment before after; cbn [double_pipeline_statement].
    split; intro RUN; inversion RUN; subst.
    + apply PipelineLoop.LLoop; rewrite !double_pipeline_expression_value.
      eapply DoubleAssignmentInstr.IterSem.iter_semantics_map; [|eassumption].
      intros value first final MEMBER POINT; apply IH; exact POINT.
    + apply SourceLoop.LLoop.
      match goal with ITER : DoubleAssignmentInstr.IterSem.iter_semantics _ _ _ _ |- _ =>
        rewrite !double_pipeline_expression_value in ITER;
        eapply DoubleAssignmentInstr.IterSem.iter_semantics_map; [|exact ITER] end.
      intros value first final MEMBER POINT; apply IH; exact POINT.
  - intros instruction arguments environment before after; cbn [double_pipeline_statement].
    split; intro RUN; inversion RUN; subst.
    + eapply PipelineLoop.LInstr; rewrite double_pipeline_arguments_value; eassumption.
    + eapply SourceLoop.LInstr.
      match goal with EXEC : PipelineLoop.instr_semantics _ _ _ _ _ _ |- _ =>
        rewrite double_pipeline_arguments_value in EXEC; exact EXEC end.
  - intros statements IH environment before after; exact (IH environment before after).
  - intros condition body IH environment before after; cbn [double_pipeline_statement].
    split; intro RUN; inversion RUN; subst.
    + apply PipelineLoop.LGuardTrue; [apply IH; assumption|rewrite double_pipeline_test_value; assumption].
    + apply PipelineLoop.LGuardFalse; rewrite double_pipeline_test_value; assumption.
    + apply SourceLoop.LGuardTrue; [apply IH; assumption|rewrite <- double_pipeline_test_value; assumption].
    + apply SourceLoop.LGuardFalse; rewrite <- double_pipeline_test_value; assumption.
  - intros environment before after; cbn [double_pipeline_statements]; split; intro RUN; inversion RUN; subst; constructor.
  - intros first IH rest TAIL environment before after; cbn [double_pipeline_statements].
    split; intro RUN; inversion RUN; subst; eapply PipelineLoop.LSeq || eapply SourceLoop.LSeq;
      [apply IH|apply TAIL|apply IH|apply TAIL]; eassumption.
Qed.
Theorem double_pipeline_execution source environment before after :
  SourceLoop.loop_semantics source environment before after <->
  PipelineLoop.loop_semantics (double_pipeline_statement source) environment before after.
Proof. apply (proj1 double_pipeline_execution_mutual). Qed.

Print Assumptions double_pipeline_expression_value.
Print Assumptions double_pipeline_test_value.
Print Assumptions double_pipeline_execution.
