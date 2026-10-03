From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Misc.
From Guard Require Import ClightCountedLoop RectangularIteration.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles GuardMemoryPolyhedral
  GuardMemoryLoops GuardMemoryNaryCompute.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_nary_arguments dimensions : list L.expr :=
  match dimensions with O => [] | S rest => L.Var rest::memory_nary_arguments rest end.
Lemma memory_nary_arguments_value prefix parameters :
  map (L.eval_expr (rev prefix++parameters)) (memory_nary_arguments (length prefix)) = prefix.
Proof.
  revert parameters; induction prefix as [|value rest IH]; intro parameters; cbn; [reflexivity|].
  rewrite <- app_assoc; cbn [app].
  rewrite <- (length_rev rest) at 1.
  rewrite nth_middle; f_equal; apply IH.
Qed.
Lemma memory_nary_instruction_execution instruction prefix parameters before after :
  L.loop_semantics (L.Instr instruction (memory_nary_arguments (length prefix)))
    (rev prefix++parameters) before after <-> memory_nary_point instruction prefix before after.
Proof.
  split.
  - intro RUN; inversion RUN as [inst args env' first final writes reads EXEC| | | | | ]; subst.
    rewrite memory_nary_arguments_value in EXEC.
    change (GuardMemoryInstr.instr_semantics instruction prefix writes reads before after) in EXEC.
    destruct EXEC as [WRITES [READS EXEC]]; subst; repeat split; assumption || reflexivity.
  - intro RUN; apply L.LInstr with (wcs := memory_write_cells instruction prefix) (rcs := memory_read_cells instruction prefix).
    rewrite memory_nary_arguments_value; exact RUN.
Qed.
Fixpoint memory_nary_instruction_sequence dimensions instructions : L.stmt_list :=
  match instructions with
  | [] => L.SNil
  | instruction::rest => L.SCons (L.Instr instruction (memory_nary_arguments dimensions))
      (memory_nary_instruction_sequence dimensions rest)
  end.
Definition memory_nary_sequence_point instructions values :=
  Iter.iter_semantics (fun instruction => memory_nary_point instruction values) instructions.
Lemma memory_nary_sequence_execution instructions prefix parameters before after :
  L.loop_semantics (L.Seq (memory_nary_instruction_sequence (length prefix) instructions))
    (rev prefix++parameters) before after <-> memory_nary_sequence_point instructions prefix before after.
Proof.
  unfold memory_nary_sequence_point; revert before after; induction instructions; intros before after; cbn; split; intro RUN.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; econstructor.
    + apply (proj1 (memory_nary_instruction_execution a prefix parameters before _)); eassumption.
    + apply IHinstructions; eassumption.
  - inversion RUN; subst; eapply L.LSeq.
    + apply (proj2 (memory_nary_instruction_execution a prefix parameters before _)); eassumption.
    + apply IHinstructions; eassumption.
Qed.
Fixpoint memory_nary_rectangle depth dimensions instructions : L.stmt :=
  match dimensions with
  | O => L.Seq (memory_nary_instruction_sequence depth instructions)
  | S rest => L.Loop (L.Constant 0) (L.Var (2*depth)%nat)
      (memory_nary_rectangle (S depth) rest instructions)
  end.
Fixpoint memory_nary_iterations {State} (point : list Z -> State -> State -> Prop) counts prefix : State -> State -> Prop :=
  match counts with
  | [] => point prefix
  | count::rest => counted_iterations (fun value => memory_nary_iterations point rest (prefix++[value])) count 0
  end.
Lemma memory_nary_bound_value prefix previous count counts :
  length prefix = length previous ->
  nth (2*length prefix)%nat (rev prefix++map Z.of_nat (previous++count::counts)) 0 = Z.of_nat count.
Proof.
  intro LENGTH; rewrite map_app,app_assoc.
  replace (2*length prefix)%nat with (length (rev prefix++map Z.of_nat previous)) by
    (rewrite length_app,length_rev,length_map; lia).
  apply nth_middle.
Qed.
Theorem memory_nary_rectangle_iterations counts instructions :
  forall prefix previous before after, length prefix = length previous ->
  (L.loop_semantics (memory_nary_rectangle (length prefix) (length counts) instructions)
    (rev prefix++map Z.of_nat (previous++counts)) before after <->
   memory_nary_iterations (memory_nary_sequence_point instructions) counts prefix before after).
Proof.
  induction counts as [|count counts IH]; intros prefix previous before after LENGTH; cbn [length memory_nary_rectangle memory_nary_iterations].
  - rewrite app_nil_r; apply memory_nary_sequence_execution.
  - split; intro RUN.
    + inversion RUN as [| | | | | env' lower upper code first final ITER]; subst.
      change (Iter.iter_semantics (fun value => L.loop_semantics
        (memory_nary_rectangle (S (length prefix)) (length counts) instructions)
        (value::rev prefix++map Z.of_nat (previous++count::counts)))
        (Zrange 0 (nth (2*length prefix)%nat (rev prefix++map Z.of_nat (previous++count::counts)) 0)) before after) in ITER.
      rewrite memory_nary_bound_value in ITER by exact LENGTH.
      apply (proj1 (@memory_range_iterations count _ 0 (Z.of_nat count) before after ltac:(lia))) in ITER.
      eapply counted_iterations_map; [|exact ITER]; intros value first final POINT.
      replace (S (length prefix)) with (length (prefix++[value])) in POINT by (rewrite length_app; cbn; lia).
      replace (value::rev prefix++map Z.of_nat (previous++count::counts)) with
        (rev (prefix++[value])++map Z.of_nat ((previous++[count])++counts)) in POINT by
        (rewrite rev_app_distr; cbn; rewrite <- app_assoc; reflexivity).
      apply (proj1 (IH (prefix++[value]) (previous++[count]) first final ltac:(rewrite !length_app; cbn; lia))); exact POINT.
    + apply L.LLoop.
      change (Iter.iter_semantics (fun value => L.loop_semantics
        (memory_nary_rectangle (S (length prefix)) (length counts) instructions)
        (value::rev prefix++map Z.of_nat (previous++count::counts)))
        (Zrange 0 (nth (2*length prefix)%nat (rev prefix++map Z.of_nat (previous++count::counts)) 0)) before after).
      rewrite memory_nary_bound_value by exact LENGTH.
      apply (proj2 (@memory_range_iterations count _ 0 (Z.of_nat count) before after ltac:(lia))).
      eapply counted_iterations_map; [|exact RUN]; intros value first final POINT.
      replace (S (length prefix)) with (length (prefix++[value])) by (rewrite length_app; cbn; lia).
      replace (value::rev prefix++map Z.of_nat (previous++count::counts)) with
        (rev (prefix++[value])++map Z.of_nat ((previous++[count])++counts)) by
        (rewrite rev_app_distr; cbn; rewrite <- app_assoc; reflexivity).
      apply (proj2 (IH (prefix++[value]) (previous++[count]) first final ltac:(rewrite !length_app; cbn; lia))); exact POINT.
Qed.
Print Assumptions memory_nary_rectangle_iterations.

Lemma memory_nary_first {State} (point : list Z -> State -> State -> Prop) counts :
  Forall (fun count => count <> O) counts -> forall prefix before after,
  memory_nary_iterations point counts prefix before after ->
  exists middle, point (prefix++repeat 0 (length counts)) before middle.
Proof.
  intro NONEMPTY; induction NONEMPTY as [|count counts HEAD NONEMPTY IH]; intros prefix before after RUN.
  - cbn in *; rewrite app_nil_r; exists after; exact RUN.
  - destruct count as [|count]; [contradiction|].
    cbn [memory_nary_iterations] in RUN; inversion RUN; subst.
    match goal with INNER : memory_nary_iterations _ counts _ _ _ |- _ =>
      destruct (IH _ _ _ INNER) as [middle POINT] end.
    exists middle; cbn [length repeat]; rewrite <- app_assoc in POINT; exact POINT.
Qed.
Print Assumptions memory_nary_first.
