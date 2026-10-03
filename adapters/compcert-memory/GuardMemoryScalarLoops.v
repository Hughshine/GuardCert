From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Misc.
From Guard Require Import ClightCountedLoop RectangularIteration.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles
  GuardMemoryPolyhedral GuardMemoryLoops GuardMemoryNaryCompute GuardMemoryNaryLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Count parameters precede stable scalar parameters.  The instruction receives
    original coordinates followed by the scalar values; loop bounds only read
    the count prefix, so negative scalar values do not restrict the domain. *)
Fixpoint memory_variables_from offset count : list L.expr :=
  match count with
  | O => []
  | S rest => L.Var offset::memory_variables_from (S offset) rest
  end.
Lemma memory_variables_from_values values : forall front,
  map (L.eval_expr (front++values)) (memory_variables_from (length front) (length values)) = values.
Proof.
  induction values as [|value values IH]; intro front; [reflexivity|].
  cbn [length memory_variables_from map L.eval_expr].
  rewrite nth_middle; f_equal.
  replace (S (length front)) with (length (front++[value])) by (rewrite length_app; cbn; lia).
  replace (front++value::values) with ((front++[value])++values) by (rewrite <- app_assoc; reflexivity).
  apply IH.
Qed.
Definition memory_scalar_arguments dimensions scalars :=
  memory_nary_arguments dimensions++memory_variables_from (2*dimensions)%nat scalars.
Lemma memory_scalar_arguments_value prefix counts values : length prefix = length counts ->
  map (L.eval_expr (rev prefix++counts++values))
    (memory_scalar_arguments (length prefix) (length values)) = prefix++values.
Proof.
  intro LENGTH; unfold memory_scalar_arguments; rewrite map_app,memory_nary_arguments_value.
  rewrite app_assoc.
  replace (2*length prefix)%nat with (length (rev prefix++counts)) by (rewrite length_app,length_rev; lia).
  rewrite memory_variables_from_values; reflexivity.
Qed.
Definition memory_scalar_sequence_point instructions coordinates values :=
  memory_nary_sequence_point instructions (coordinates++values).
Lemma memory_scalar_instruction_execution instruction prefix counts values before after :
  length prefix = length counts ->
  (L.loop_semantics (L.Instr instruction (memory_scalar_arguments (length prefix) (length values)))
    (rev prefix++counts++values) before after <-> memory_nary_point instruction (prefix++values) before after).
Proof.
  intro LENGTH; split.
  - intro RUN; inversion RUN as [inst args env' first final writes reads EXEC| | | | | ]; subst.
    rewrite memory_scalar_arguments_value in EXEC by exact LENGTH.
    change (GuardMemoryInstr.instr_semantics instruction (prefix++values) writes reads before after) in EXEC.
    destruct EXEC as [WRITES [READS EXEC]]; subst; repeat split; assumption || reflexivity.
  - intro RUN; apply L.LInstr with (wcs := memory_write_cells instruction (prefix++values))
      (rcs := memory_read_cells instruction (prefix++values)).
    rewrite memory_scalar_arguments_value by exact LENGTH; exact RUN.
Qed.
Fixpoint memory_scalar_instruction_sequence dimensions scalars instructions : L.stmt_list :=
  match instructions with
  | [] => L.SNil
  | instruction::rest => L.SCons (L.Instr instruction (memory_scalar_arguments dimensions scalars))
      (memory_scalar_instruction_sequence dimensions scalars rest)
  end.
Lemma memory_scalar_sequence_execution instructions prefix counts values before after :
  length prefix = length counts ->
  (L.loop_semantics (L.Seq (memory_scalar_instruction_sequence (length prefix) (length values) instructions))
    (rev prefix++counts++values) before after <-> memory_scalar_sequence_point instructions prefix values before after).
Proof.
  intro LENGTH; unfold memory_scalar_sequence_point,memory_nary_sequence_point.
  revert before after; induction instructions; intros before after; cbn; split; intro RUN.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; econstructor.
    + apply (proj1 (@memory_scalar_instruction_execution a prefix counts values before _ LENGTH)); eassumption.
    + apply IHinstructions; eassumption.
  - inversion RUN; subst; eapply L.LSeq.
    + apply (proj2 (@memory_scalar_instruction_execution a prefix counts values before _ LENGTH)); eassumption.
    + apply IHinstructions; eassumption.
Qed.
Fixpoint memory_scalar_rectangle depth dimensions scalars instructions : L.stmt :=
  match dimensions with
  | O => L.Seq (memory_scalar_instruction_sequence depth scalars instructions)
  | S rest => L.Loop (L.Constant 0) (L.Var (2*depth)%nat)
      (memory_scalar_rectangle (S depth) rest scalars instructions)
  end.
Lemma memory_scalar_bound_value prefix previous count counts values :
  length prefix = length previous ->
  nth (2*length prefix)%nat (rev prefix++map Z.of_nat (previous++count::counts)++values) 0 = Z.of_nat count.
Proof.
  intro LENGTH; rewrite map_app.
  change (nth (2*length prefix)%nat (rev prefix++(map Z.of_nat previous++Z.of_nat count::map Z.of_nat counts)++values) 0 = Z.of_nat count).
  rewrite !app_assoc.
  replace (2*length prefix)%nat with (length (rev prefix++map Z.of_nat previous)) by
    (rewrite length_app,length_rev,length_map; lia).
  rewrite <- app_assoc; apply nth_middle.
Qed.
Theorem memory_scalar_rectangle_iterations counts instructions values :
  forall prefix previous before after, length prefix = length previous ->
  (L.loop_semantics (memory_scalar_rectangle (length prefix) (length counts) (length values) instructions)
    (rev prefix++map Z.of_nat (previous++counts)++values) before after <->
   memory_nary_iterations (fun coordinates => memory_scalar_sequence_point instructions coordinates values)
     counts prefix before after).
Proof.
  induction counts as [|count counts IH]; intros prefix previous before after LENGTH;
    cbn [length memory_scalar_rectangle memory_nary_iterations].
  - rewrite app_nil_r; apply memory_scalar_sequence_execution; rewrite length_map; exact LENGTH.
  - split; intro RUN.
    + inversion RUN as [| | | | | env' lower upper code first final ITER]; subst.
      change (Iter.iter_semantics (fun value => L.loop_semantics
        (memory_scalar_rectangle (S (length prefix)) (length counts) (length values) instructions)
        (value::rev prefix++map Z.of_nat (previous++count::counts)++values))
        (Zrange 0 (nth (2*length prefix)%nat (rev prefix++map Z.of_nat (previous++count::counts)++values) 0)) before after) in ITER.
      rewrite memory_scalar_bound_value in ITER by exact LENGTH.
      apply (proj1 (@memory_range_iterations count _ 0 (Z.of_nat count) before after ltac:(lia))) in ITER.
      eapply counted_iterations_map; [|exact ITER]; intros value first final POINT.
      replace (S (length prefix)) with (length (prefix++[value])) in POINT by (rewrite length_app; cbn; lia).
      replace (value::rev prefix++map Z.of_nat (previous++count::counts)++values) with
        (rev (prefix++[value])++map Z.of_nat ((previous++[count])++counts)++values) in POINT by
        (rewrite rev_app_distr; cbn; rewrite <- app_assoc; reflexivity).
      apply (proj1 (IH (prefix++[value]) (previous++[count]) first final ltac:(rewrite !length_app; cbn; lia))); exact POINT.
    + apply L.LLoop.
      change (Iter.iter_semantics (fun value => L.loop_semantics
        (memory_scalar_rectangle (S (length prefix)) (length counts) (length values) instructions)
        (value::rev prefix++map Z.of_nat (previous++count::counts)++values))
        (Zrange 0 (nth (2*length prefix)%nat (rev prefix++map Z.of_nat (previous++count::counts)++values) 0)) before after).
      rewrite memory_scalar_bound_value by exact LENGTH.
      apply (proj2 (@memory_range_iterations count _ 0 (Z.of_nat count) before after ltac:(lia))).
      eapply counted_iterations_map; [|exact RUN]; intros value first final POINT.
      replace (S (length prefix)) with (length (prefix++[value])) by (rewrite length_app; cbn; lia).
      replace (value::rev prefix++map Z.of_nat (previous++count::counts)++values) with
        (rev (prefix++[value])++map Z.of_nat ((previous++[count])++counts)++values) by
        (rewrite rev_app_distr; cbn; rewrite <- app_assoc; reflexivity).
      apply (proj2 (IH (prefix++[value]) (previous++[count]) first final ltac:(rewrite !length_app; cbn; lia))); exact POINT.
Qed.
Print Assumptions memory_scalar_arguments_value.
Print Assumptions memory_scalar_rectangle_iterations.
