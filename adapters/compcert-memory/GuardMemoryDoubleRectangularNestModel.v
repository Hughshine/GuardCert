From Stdlib Require Import List ZArith Lia.
From compcert.common Require Import AST Memory Values Globalenvs.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryValueInstr GuardMemoryDoubleLocations
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceTransport GuardMemoryDoubleSourceLoopModel
  GuardMemoryDoubleInitializedNestModel GuardMemoryDoubleMatmulLoopModel GuardMemoryLoops GuardMemoryDoubleNestControl.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Parameters retain all axis bounds. At depth k, k iterator values have also
    been pushed. The next bound is therefore at dimensions + parameter_slot. *)
Fixpoint double_rectangular_nest_model instruction depth parameter_slot dimensions :=
  match depth with
  | O => SL.Instr instruction (double_source_arguments dimensions)
  | S rest => SL.Loop (SL.Constant 0) (SL.Var (dimensions+parameter_slot)%nat)
      (double_rectangular_nest_model instruction rest (S parameter_slot) (S dimensions)) end.
Lemma double_rectangular_nth_after_append (prefix parameters : list Z) slot :
  nth (length prefix+slot)%nat (prefix++parameters) 0=nth slot parameters 0.
Proof. induction prefix; cbn; [reflexivity|exact IHprefix]. Qed.
Lemma double_rectangular_parameter_head slot : forall parameters count counts,
  skipn slot parameters=Z.of_nat count::map Z.of_nat counts -> nth slot parameters 0=Z.of_nat count.
Proof.
  induction slot as [|slot IH]; intros [|parameter parameters] count counts CHECK;
    cbn [skipn nth] in *; try discriminate; [congruence|eapply IH; exact CHECK].
Qed.
Lemma double_rectangular_parameter_tail slot : forall parameters count counts,
  skipn slot parameters=Z.of_nat count::map Z.of_nat counts ->
  skipn (S slot) parameters=map Z.of_nat counts.
Proof.
  induction slot as [|slot IH]; intros [|parameter parameters] count counts CHECK;
    cbn [skipn] in *; try discriminate; [congruence|eapply IH; exact CHECK].
Qed.
Lemma double_rectangular_nest_iterations instruction depth slot prefix parameters count before after :
  nth slot parameters 0=Z.of_nat count ->
  (SL.loop_semantics (double_rectangular_nest_model instruction (S depth) slot (length prefix))
    (rev prefix++parameters) before after <->
   counted_iterations (fun value => SL.loop_semantics
     (double_rectangular_nest_model instruction depth (S slot) (S (length prefix)))
     (value::rev prefix++parameters)) count 0 before after).
Proof.
  intro PARAMETER.
  assert (BOUND : nth (length prefix+slot)%nat (rev prefix++parameters) 0=Z.of_nat count).
  { rewrite <- (length_rev prefix); rewrite double_rectangular_nth_after_append; exact PARAMETER. }
  cbn [double_rectangular_nest_model]; split.
  - intro RUN; inversion RUN as [| | | | | env lower upper body first final ITER]; subst.
    cbn [SL.eval_expr] in ITER; rewrite BOUND in ITER.
    apply (proj1 (@double_matmul_range_iterations count _ 0 (Z.of_nat count) before after ltac:(lia))); exact ITER.
  - intro ITER; apply SL.LLoop; cbn [SL.eval_expr]; rewrite BOUND.
    apply (proj2 (@double_matmul_range_iterations count _ 0 (Z.of_nat count) before after ltac:(lia))); exact ITER.
Qed.
Lemma double_rectangular_nest_frame instruction counts : forall slot prefix parameters before after,
  skipn slot parameters=map Z.of_nat counts ->
  SL.loop_semantics (double_rectangular_nest_model instruction (length counts) slot (length prefix))
    (rev prefix++parameters) before after -> runtime_locations after=runtime_locations before.
Proof.
  induction counts as [|count counts IH]; intros slot prefix parameters before after PARAMETER RUN.
  - cbn [double_rectangular_nest_model length] in RUN; eapply double_source_instruction_Loop_frame; exact RUN.
  - apply (proj1 (@double_rectangular_nest_iterations instruction (length counts) slot prefix parameters count
      before after (@double_rectangular_parameter_head slot parameters count counts PARAMETER))) in RUN.
    eapply counted_locations; [|exact RUN].
    intros value first final CHILD.
    replace (S (length prefix)) with (length (prefix++[value])) in CHILD by (rewrite app_length; cbn [length]; lia).
    rewrite <- double_source_extended_environment in CHILD; eapply IH;
      [eapply double_rectangular_parameter_tail; exact PARAMETER|exact CHILD].
Qed.
Theorem double_rectangular_nest_memory instruction count counts slot prefix parameters locations before after :
  skipn slot parameters=Z.of_nat count::map Z.of_nat counts ->
  (SL.loop_semantics (double_rectangular_nest_model instruction (S (length counts)) slot (length prefix))
    (rev prefix++parameters) (RuntimeState locations before) (RuntimeState locations after) <->
   counted_iterations (fun value first final => SL.loop_semantics
     (double_rectangular_nest_model instruction (length counts) (S slot) (length (prefix++[value])))
     (rev (prefix++[value])++parameters)
     (RuntimeState locations first) (RuntimeState locations final)) count 0 before after).
Proof.
  intro PARAMETER; rewrite double_rectangular_nest_iterations
    by (eapply double_rectangular_parameter_head; exact PARAMETER); symmetry.
  apply counted_memory_lift with (floor:=0) (upper:=Z.of_nat count); try lia.
  - intros value first final RANGE; rewrite app_length; cbn [length]; rewrite Nat.add_1_r.
    rewrite double_source_extended_environment; reflexivity.
  - intros value first final RUN.
    replace (S (length prefix)) with (length (prefix++[value])) in RUN by (rewrite app_length; cbn [length]; lia).
    rewrite <- double_source_extended_environment in RUN; eapply double_rectangular_nest_frame;
      [eapply double_rectangular_parameter_tail; exact PARAMETER|exact RUN].
Qed.
Theorem double_rectangular_nest_preserves_global counts description slot prefix parameters (ge : genv) layouts
  before after header header_block chunk offset :
  skipn slot parameters=map Z.of_nat counts ->
  Genv.find_symbol ge header=Some header_block ->
  fst (value_instruction_write (double_source_instruction_model description))<>header ->
  SL.loop_semantics (double_rectangular_nest_model (double_source_instruction_model description)
    (length counts) slot (length prefix)) (rev prefix++parameters)
    (RuntimeState (global_double_locations ge layouts) before)
    (RuntimeState (global_double_locations ge layouts) after) ->
  Mem.load chunk after header_block offset=Mem.load chunk before header_block offset.
Proof.
  revert slot prefix parameters before after; induction counts as [|count counts IH];
    intros slot prefix parameters before after PARAMETER HEADER WRITE RUN.
  - cbn [double_rectangular_nest_model length] in RUN; apply double_source_instruction_Loop in RUN.
    unfold double_source_model_point in RUN; eapply double_source_model_preserves_global; eassumption.
  - apply (proj1 (@double_rectangular_nest_memory (double_source_instruction_model description) count counts slot
      prefix parameters (global_double_locations ge layouts) before after PARAMETER)) in RUN.
    eapply counted_memory_load_frame; [|exact RUN].
    intros value first final CHILD; eapply IH;
      [eapply double_rectangular_parameter_tail; exact PARAMETER|exact HEADER|exact WRITE|exact CHILD].
Qed.

Print Assumptions double_rectangular_parameter_head.
Print Assumptions double_rectangular_parameter_tail.
Print Assumptions double_rectangular_nest_iterations.
Print Assumptions double_rectangular_nest_frame.
Print Assumptions double_rectangular_nest_memory.
Print Assumptions double_rectangular_nest_preserves_global.
