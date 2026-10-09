From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Memory Values Globalenvs.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import Misc.
From Guard Require Import ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryValueInstr GuardMemoryDoubleLocations
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceTransport GuardMemoryDoubleSourceLoopModel
  GuardMemoryDoubleInitializedNestModel GuardMemoryDoubleInitializedNestExit
  GuardMemoryDoubleMatmulLoopModel GuardMemoryLoops GuardMemoryLongLoopSettle GuardMemoryDoubleNestControl.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint double_reduction_nest_model instruction depth dimensions :=
  match depth with
  | O => SL.Instr instruction (double_source_arguments dimensions)
  | S rest => SL.Loop (SL.Constant 0) (SL.Var dimensions)
      (double_reduction_nest_model instruction rest (S dimensions)) end.
Lemma double_reduction_nest_iterations instruction depth prefix count before after :
  SL.loop_semantics (double_reduction_nest_model instruction (S depth) (length prefix))
    (rev prefix++[Z.of_nat count]) before after <->
  counted_iterations (fun value => SL.loop_semantics
    (double_reduction_nest_model instruction depth (S (length prefix)))
    (value::rev prefix++[Z.of_nat count])) count 0 before after.
Proof.
  assert (BOUND : nth (length prefix) (rev prefix++[Z.of_nat count]) 0=Z.of_nat count)
    by (rewrite <- (length_rev prefix); apply nth_middle).
  cbn [double_reduction_nest_model]; split.
  - intro RUN; inversion RUN as [| | | | | env lower upper body first final ITER]; subst.
    cbn [SL.eval_expr] in ITER; rewrite BOUND in ITER.
    apply (proj1 (@double_matmul_range_iterations count _ 0 (Z.of_nat count) before after ltac:(lia))); exact ITER.
  - intro ITER; apply SL.LLoop; cbn [SL.eval_expr]; rewrite BOUND.
    apply (proj2 (@double_matmul_range_iterations count _ 0 (Z.of_nat count) before after ltac:(lia))); exact ITER.
Qed.
Lemma double_reduction_nest_frame instruction depth : forall prefix count before after,
  SL.loop_semantics (double_reduction_nest_model instruction depth (length prefix))
    (rev prefix++[Z.of_nat count]) before after -> runtime_locations after=runtime_locations before.
Proof.
  induction depth as [|depth IH]; intros prefix count before after.
  - cbn [double_reduction_nest_model]; apply double_source_instruction_Loop_frame.
  - rewrite double_reduction_nest_iterations; intro RUN; eapply counted_locations; [|exact RUN].
    intros value first final CHILD.
    replace (S (length prefix)) with (length (prefix++[value])) in CHILD
      by (rewrite app_length; cbn [length]; lia).
    rewrite <- double_source_extended_environment in CHILD; eapply IH; exact CHILD.
Qed.
Theorem double_reduction_nest_memory instruction depth prefix count locations before after :
  SL.loop_semantics (double_reduction_nest_model instruction (S depth) (length prefix))
    (rev prefix++[Z.of_nat count]) (RuntimeState locations before) (RuntimeState locations after) <->
  counted_iterations (fun value first final => SL.loop_semantics
    (double_reduction_nest_model instruction depth (length (prefix++[value])))
    (rev (prefix++[value])++[Z.of_nat count])
    (RuntimeState locations first) (RuntimeState locations final)) count 0 before after.
Proof.
  rewrite double_reduction_nest_iterations; symmetry.
  apply counted_memory_lift with (floor:=0) (upper:=Z.of_nat count); try lia.
  - intros value first final RANGE; rewrite app_length; cbn [length]; rewrite Nat.add_1_r.
    rewrite double_source_extended_environment; reflexivity.
  - intros value first final RUN.
    replace (S (length prefix)) with (length (prefix++[value])) in RUN
      by (rewrite app_length; cbn [length]; lia).
    rewrite <- double_source_extended_environment in RUN; eapply double_reduction_nest_frame; exact RUN.
Qed.
Theorem double_reduction_nest_preserves_global depth description prefix count (ge : genv) layouts
  before after header header_block chunk offset :
  Genv.find_symbol ge header=Some header_block ->
  fst (value_instruction_write (double_source_instruction_model description))<>header ->
  SL.loop_semantics (double_reduction_nest_model (double_source_instruction_model description) depth (length prefix))
    (rev prefix++[Z.of_nat count]) (RuntimeState (global_double_locations ge layouts) before)
    (RuntimeState (global_double_locations ge layouts) after) ->
  Mem.load chunk after header_block offset=Mem.load chunk before header_block offset.
Proof.
  revert prefix before after; induction depth as [|depth IH]; intros prefix before after HEADER WRITE RUN.
  - cbn [double_reduction_nest_model] in RUN; apply double_source_instruction_Loop in RUN.
    unfold double_source_model_point in RUN; eapply double_source_model_preserves_global; eassumption.
  - rewrite double_reduction_nest_memory in RUN; eapply counted_memory_load_frame; [|exact RUN].
    intros value first final CHILD; exact (@IH (prefix++[value]) first final HEADER WRITE CHILD).
Qed.

Definition double_reduction_exit_ids (iterators : list ident) count :=
  match count,iterators with O,iterator::_ => [iterator] | _,_ => iterators end.
Definition double_reduction_nest_exit iterators count temps :=
  double_source_set_words (double_reduction_exit_ids iterators count) (Vlong (Int64.repr (Z.of_nat count))) temps.
Lemma double_reduction_exit_ids_subset iterators count : forall key,
  In key (double_reduction_exit_ids iterators count) -> In key iterators.
Proof.
  destruct count,iterators; cbn [double_reduction_exit_ids]; intros key MEMBER; try exact MEMBER.
  cbn in MEMBER; destruct MEMBER as [SAME|EMPTY]; [subst; cbn; auto|contradiction].
Qed.
Lemma double_reduction_nest_exit_nil count temps : double_reduction_nest_exit [] count temps=temps.
Proof. destruct count; reflexivity. Qed.
Lemma double_reduction_nest_exit_cons iterator rest count temps :
  double_reduction_nest_exit (iterator::rest) count temps=
  PTree.set iterator (Vlong (Int64.repr (Z.of_nat count)))
    (match count with O=>temps | S _=>double_reduction_nest_exit rest count temps end).
Proof. destruct count; reflexivity. Qed.
Lemma double_reduction_nest_exit_idempotent iterators count temps :
  double_reduction_nest_exit iterators count (double_reduction_nest_exit iterators count temps)=
  double_reduction_nest_exit iterators count temps.
Proof. apply double_source_set_words_idempotent. Qed.
Lemma double_reduction_nest_exit_frame iterators count temps key :
  ~ In key iterators -> (double_reduction_nest_exit iterators count temps) ! key=temps ! key.
Proof.
  intro FRESH; apply double_source_set_words_frame; intro MEMBER; apply FRESH;
    eapply double_reduction_exit_ids_subset; exact MEMBER.
Qed.
Lemma double_reduction_nest_exit_commute iterators count temps iterator word : ~ In iterator iterators ->
  double_reduction_nest_exit iterators count (PTree.set iterator word temps)=
  PTree.set iterator word (double_reduction_nest_exit iterators count temps).
Proof.
  intro FRESH; apply double_source_set_words_commute; intro MEMBER; apply FRESH;
    eapply double_reduction_exit_ids_subset; exact MEMBER.
Qed.
Theorem double_reduction_nest_settled_exit iterator rest count temps : ~ In iterator rest ->
  memory_long_settled_exit iterator (fun _ => double_reduction_nest_exit rest count) count 0
    (PTree.set iterator (Vlong Int64.zero) temps)=double_reduction_nest_exit (iterator::rest) count temps.
Proof.
  intro FRESH; destruct count as [|count]; [reflexivity|].
  rewrite (@memory_long_constant_settle_exit iterator (double_reduction_nest_exit rest (S count))
    ltac:(intro le; apply double_reduction_nest_exit_idempotent)
    ltac:(intros le word; apply double_reduction_nest_exit_commute; exact FRESH) count 0).
  rewrite Z.add_0_l,double_reduction_nest_exit_commute by exact FRESH.
  rewrite PTree.set2,double_reduction_nest_exit_cons; reflexivity.
Qed.

Print Assumptions double_reduction_nest_frame.
Print Assumptions double_reduction_nest_memory.
Print Assumptions double_reduction_nest_preserves_global.
Print Assumptions double_reduction_nest_exit_frame.
Print Assumptions double_reduction_nest_settled_exit.
