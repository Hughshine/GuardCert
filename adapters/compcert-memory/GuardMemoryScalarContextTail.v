From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Misc.
From Guard Require Import ClightCountedLoop RectangularIteration.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles
  GuardMemoryPolyhedral GuardMemoryLoops GuardMemoryNaryCompute GuardMemoryNaryLoops GuardMemoryScalarLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_variables_from_prefix values : forall front tail,
  map (L.eval_expr (front++values++tail)) (memory_variables_from (length front) (length values)) = values.
Proof.
  induction values as [|value values IH]; intros front tail; [reflexivity|].
  cbn [length memory_variables_from map L.eval_expr app].
  rewrite nth_middle; f_equal.
  replace (S (length front)) with (length (front++[value])) by (rewrite length_app; cbn; lia).
  replace (front++value::values++tail) with ((front++[value])++values++tail) by (rewrite <- app_assoc; reflexivity).
  apply IH.
Qed.
Lemma memory_scalar_arguments_value_tail prefix counts values tail : length prefix = length counts ->
  map (L.eval_expr (rev prefix++counts++(values++tail)))
    (memory_scalar_arguments (length prefix) (length values)) = prefix++values.
Proof.
  intro LENGTH; unfold memory_scalar_arguments; rewrite map_app,memory_nary_arguments_value.
  rewrite app_assoc.
  replace (2*length prefix)%nat with (length (rev prefix++counts)) by (rewrite length_app,length_rev; lia).
  apply f_equal; apply memory_variables_from_prefix.
Qed.
Lemma memory_scalar_instruction_execution_tail instruction prefix counts values tail before after :
  length prefix = length counts ->
  (L.loop_semantics (L.Instr instruction (memory_scalar_arguments (length prefix) (length values)))
    (rev prefix++counts++(values++tail)) before after <-> memory_nary_point instruction (prefix++values) before after).
Proof.
  intro LENGTH; split.
  - intro RUN; inversion RUN as [inst args env' first final writes reads EXEC| | | | | ]; subst.
    rewrite memory_scalar_arguments_value_tail in EXEC by exact LENGTH.
    change (GuardMemoryInstr.instr_semantics instruction (prefix++values) writes reads before after) in EXEC.
    destruct EXEC as [WRITES [READS EXEC]]; subst; repeat split; assumption || reflexivity.
  - intro RUN; apply L.LInstr with (wcs := memory_write_cells instruction (prefix++values))
      (rcs := memory_read_cells instruction (prefix++values)).
    rewrite memory_scalar_arguments_value_tail by exact LENGTH; exact RUN.
Qed.
Lemma memory_scalar_sequence_execution_tail instructions prefix counts values tail before after :
  length prefix = length counts ->
  (L.loop_semantics (L.Seq (memory_scalar_instruction_sequence (length prefix) (length values) instructions))
    (rev prefix++counts++(values++tail)) before after <-> memory_scalar_sequence_point instructions prefix values before after).
Proof.
  intro LENGTH; unfold memory_scalar_sequence_point,memory_nary_sequence_point.
  revert before after; induction instructions; intros before after; cbn; split; intro RUN.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; econstructor.
    + apply (proj1 (@memory_scalar_instruction_execution_tail a prefix counts values tail before _ LENGTH)); eassumption.
    + apply IHinstructions; eassumption.
  - inversion RUN; subst; eapply L.LSeq.
    + apply (proj2 (@memory_scalar_instruction_execution_tail a prefix counts values tail before _ LENGTH)); eassumption.
    + apply IHinstructions; eassumption.
Qed.
Theorem memory_scalar_rectangle_iterations_tail counts instructions values tail :
  forall prefix previous before after, length prefix = length previous ->
  (L.loop_semantics (memory_scalar_rectangle (length prefix) (length counts) (length values) instructions)
    (rev prefix++map Z.of_nat (previous++counts)++(values++tail)) before after <->
   memory_nary_iterations (fun coordinates => memory_scalar_sequence_point instructions coordinates values)
     counts prefix before after).
Proof.
  induction counts as [|count counts IH]; intros prefix previous before after LENGTH;
    cbn [length memory_scalar_rectangle memory_nary_iterations].
  - rewrite app_nil_r; apply memory_scalar_sequence_execution_tail; rewrite length_map; exact LENGTH.
  - split; intro RUN.
    + inversion RUN as [| | | | | env' lower upper code first final ITER]; subst.
      change (Iter.iter_semantics (fun value => L.loop_semantics
        (memory_scalar_rectangle (S (length prefix)) (length counts) (length values) instructions)
        (value::rev prefix++map Z.of_nat (previous++count::counts)++(values++tail)))
        (Zrange 0 (nth (2*length prefix)%nat (rev prefix++map Z.of_nat (previous++count::counts)++(values++tail)) 0)) before after) in ITER.
      rewrite memory_scalar_bound_value in ITER by exact LENGTH.
      apply (proj1 (@memory_range_iterations count _ 0 (Z.of_nat count) before after ltac:(lia))) in ITER.
      eapply counted_iterations_map; [|exact ITER]; intros value first final POINT.
      replace (S (length prefix)) with (length (prefix++[value])) in POINT by (rewrite length_app; cbn; lia).
      replace (value::rev prefix++map Z.of_nat (previous++count::counts)++(values++tail)) with
        (rev (prefix++[value])++map Z.of_nat ((previous++[count])++counts)++(values++tail)) in POINT by
        (rewrite rev_app_distr; cbn; rewrite <- app_assoc; reflexivity).
      apply (proj1 (IH (prefix++[value]) (previous++[count]) first final ltac:(rewrite !length_app; cbn; lia))); exact POINT.
    + apply L.LLoop.
      change (Iter.iter_semantics (fun value => L.loop_semantics
        (memory_scalar_rectangle (S (length prefix)) (length counts) (length values) instructions)
        (value::rev prefix++map Z.of_nat (previous++count::counts)++(values++tail)))
        (Zrange 0 (nth (2*length prefix)%nat (rev prefix++map Z.of_nat (previous++count::counts)++(values++tail)) 0)) before after).
      rewrite memory_scalar_bound_value by exact LENGTH.
      apply (proj2 (@memory_range_iterations count _ 0 (Z.of_nat count) before after ltac:(lia))).
      eapply counted_iterations_map; [|exact RUN]; intros value first final POINT.
      replace (S (length prefix)) with (length (prefix++[value])) by (rewrite length_app; cbn; lia).
      replace (value::rev prefix++map Z.of_nat (previous++count::counts)++(values++tail)) with
        (rev (prefix++[value])++map Z.of_nat ((previous++[count])++counts)++(values++tail)) by
        (rewrite rev_app_distr; cbn; rewrite <- app_assoc; reflexivity).
      apply (proj2 (IH (prefix++[value]) (previous++[count]) first final ltac:(rewrite !length_app; cbn; lia))); exact POINT.
Qed.
Print Assumptions memory_scalar_rectangle_iterations_tail.
