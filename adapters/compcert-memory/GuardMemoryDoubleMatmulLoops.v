From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import CompCertMemoryActions ClightCondition ClightCountedLoop.
From GuardMemory Require Import GuardMemoryDoubleValue GuardMemoryDoubleLocations GuardMemoryDoubleAssignment
  GuardMemoryDoubleMatmul GuardMemoryDoubleHeaderFrame GuardMemoryLongControl GuardMemoryLongLoopControl
  GuardMemoryObservationDeterminism.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record double_matmul_static ge locals site blocks : Prop := {
  matmul_static_A : double_global_binding ge locals (matmul_A site) (matmul_A_block blocks);
  matmul_static_B : double_global_binding ge locals (matmul_B site) (matmul_B_block blocks);
  matmul_static_C : double_global_binding ge locals (matmul_C site) (matmul_C_block blocks);
  matmul_static_alpha : double_global_binding ge locals (matmul_alpha site) (matmul_alpha_block blocks);
  matmul_static_beta : double_global_binding ge locals (matmul_beta site) (matmul_beta_block blocks);
  matmul_static_padding : Int.min_signed<=matmul_padding site<=Int.max_signed;
  matmul_static_span : 8*(matmul_extent site*matmul_extent site)<=Ptrofs.modulus
}.
Lemma double_matmul_point_entry ge locals temps site blocks i j k :
  double_matmul_static ge locals site blocks ->
  temps ! (matmul_i site)=Some (Vlong (Int64.repr i)) -> temps ! (matmul_j site)=Some (Vlong (Int64.repr j)) ->
  temps ! (matmul_k site)=Some (Vlong (Int64.repr k)) ->
  0<=i+matmul_padding site<matmul_extent site -> 0<=j+matmul_padding site<matmul_extent site ->
  0<=k+matmul_padding site<matmul_extent site -> double_matmul_entry ge locals temps site blocks i j k.
Proof. intros [A B C ALPHA BETA PAD SPAN] I J K IB JB KB; constructor; assumption. Qed.
Definition double_matmul_long_condition iterator bound :=
  Ebinop Olt (Etempvar iterator memory_long_type) (Evar bound memory_long_type) memory_signed_int_type.
Definition double_matmul_inner_source site bound :=
  memory_long_initialized_loop (matmul_k site) (double_matmul_long_condition (matmul_k site) bound) (double_matmul_body site).
Definition double_matmul_inner_action site blocks i j k :=
  memory_action_run (MemoryAction (double_matmul_locations site blocks i j k)
    (double_matmul_location site (matmul_C_block blocks) i j)
    (fun values => compute_double_assignment values double_matmul_expression)).

Lemma memory_long_temp_set_existing (temps : temp_env) iterator (value : val) :
  temps ! iterator=Some value -> PTree.set iterator value temps=temps.
Proof.
  intro VALUE; apply PTree.extensionality; intro key; rewrite PTree.gsspec.
  destruct (peq key iterator); subst; [symmetry; exact VALUE|reflexivity].
Qed.
Lemma memory_long_initialization_exact fe ge locals temps memory iterator trace after final outcome :
  exec_stmt fe ge locals temps memory (Sset iterator memory_long_zero) trace after final outcome ->
  trace=E0 /\ after=PTree.set iterator (Vlong Int64.zero) temps /\ final=memory /\ outcome=Out_normal.
Proof.
  intro RUN; pose proof (@memory_long_zero_execution ge locals temps memory) as EXPECTED.
  inversion RUN; subst; match goal with EVAL : eval_expr _ _ _ _ memory_long_zero ?actual |- _ =>
    pose proof (memory_expression_unique EVAL EXPECTED) as SAME; subst actual end;
    repeat split; reflexivity.
Qed.
Lemma memory_long_initialized_decode fe ge locals temps memory iterator condition body after final :
  exec_stmt fe ge locals temps memory (memory_long_initialized_loop iterator condition body) E0 after final Out_normal ->
  exec_stmt fe ge locals (PTree.set iterator (Vlong Int64.zero) temps) memory
    (memory_long_frontend_loop iterator condition body) E0 after final Out_normal.
Proof.
  intro RUN; inversion RUN; subst.
  all: match goal with INIT : exec_stmt _ _ _ _ _ (Sset _ memory_long_zero) _ _ _ _ |- _ =>
    destruct (memory_long_initialization_exact INIT) as [TRACE [TEMPS [MEMORY OUTCOME]]]; subst end.
  - cbn in *; assumption.
  - contradiction.
Qed.

Section INNER.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable site : double_matmul_site.
Variable blocks : double_matmul_blocks.
Variable bound : ident.
Variable bound_block : block.
Variable i j upper : Z.
Hypothesis STATIC : double_matmul_static ge locals site blocks.
Hypothesis BOUND : double_global_binding ge locals bound bound_block.
Hypothesis OTHER_GLOBAL : matmul_C site<>bound.
Hypothesis OTHER_I : matmul_k site<>matmul_i site.
Hypothesis OTHER_J : matmul_k site<>matmul_j site.
Hypothesis I_BOUNDS : 0<=i+matmul_padding site<matmul_extent site.
Hypothesis J_BOUNDS : 0<=j+matmul_padding site<matmul_extent site.
Hypothesis K_BOUNDS : 0<=matmul_padding site /\ upper+matmul_padding site<=matmul_extent site.
Hypothesis RANGE : 0<=upper<=Int64.max_signed.

Definition matmul_inner_invariant temps memory :=
  temps ! (matmul_i site)=Some (Vlong (Int64.repr i)) /\
  temps ! (matmul_j site)=Some (Vlong (Int64.repr j)) /\
  Mem.load Mint64 memory bound_block 0=Some (Vlong (Int64.repr upper)).
Lemma matmul_inner_entry temps memory value : matmul_inner_invariant temps memory ->
  temps ! (matmul_k site)=Some (Vlong (Int64.repr value)) -> 0<=value<upper ->
  double_matmul_entry ge locals temps site blocks i j value.
Proof.
  intros [I [J LOAD]] VALUE LIMIT; eapply double_matmul_point_entry; eauto; lia.
Qed.
Lemma matmul_inner_test temps memory value : matmul_inner_invariant temps memory ->
  temps ! (matmul_k site)=Some (Vlong (Int64.repr value)) -> 0<=value<=upper ->
  expression_test (double_matmul_long_condition (matmul_k site) bound) (Entry ge locals temps memory) (value <? upper).
Proof.
  intros [_ [_ LOAD]] VALUE LIMIT; exists (Val.of_bool (value <? upper)); split.
  - eapply memory_long_test_execution; try reflexivity.
    + pose proof Int64.min_signed_neg; lia.
    + pose proof Int64.min_signed_neg; lia.
    + constructor; exact VALUE.
    + eapply memory_global_long_execution; eauto.
  - destruct (value <? upper); reflexivity.
Qed.
Lemma matmul_inner_increment_invariant temps memory value : matmul_inner_invariant temps memory ->
  matmul_inner_invariant (PTree.set (matmul_k site) (Vlong (Int64.repr value)) temps) memory.
Proof. intros [I [J LOAD]]; unfold matmul_inner_invariant; rewrite !PTree.gso by congruence; auto. Qed.
Lemma matmul_inner_action_invariant temps memory value final : matmul_inner_invariant temps memory ->
  temps ! (matmul_k site)=Some (Vlong (Int64.repr value)) -> 0<=value<upper ->
  double_matmul_inner_action site blocks i j value memory final -> matmul_inner_invariant temps final.
Proof.
  intros INV VALUE LIMIT ACTION; destruct INV as [I [J LOAD]]; repeat split; try assumption.
  rewrite (@double_matmul_action_preserves_global ge locals temps memory site blocks i j value final
    bound bound_block Mint64 0 ltac:(eapply matmul_inner_entry; [repeat split; eassumption|exact VALUE|exact LIMIT])
    (proj2 BOUND) OTHER_GLOBAL ACTION); exact LOAD.
Qed.

Theorem double_matmul_inner_loop_decode count : forall value temps memory after final,
  upper=value+Z.of_nat count -> 0<=value -> matmul_inner_invariant temps memory ->
  temps ! (matmul_k site)=Some (Vlong (Int64.repr value)) ->
  exec_stmt fe ge locals temps memory
    (memory_long_frontend_loop (matmul_k site) (double_matmul_long_condition (matmul_k site) bound)
      (double_matmul_body site)) E0 after final Out_normal ->
  counted_iterations (double_matmul_inner_action site blocks i j) count value memory final /\
    after=PTree.set (matmul_k site) (Vlong (Int64.repr upper)) temps.
Proof.
  induction count as [|count IH]; intros value temps memory after final LENGTH LOWER INV VALUE RUN.
  - assert (SAME : value=upper) by (cbn in LENGTH; lia); subst value.
    pose proof (@matmul_inner_test temps memory upper INV VALUE ltac:(lia)) as TEST; rewrite Z.ltb_irrefl in TEST.
    destruct (memory_long_loop_stop_decode TEST RUN) as [_ [TEMPS [MEMORY _]]]; subst after final.
    split; [constructor|symmetry; apply memory_long_temp_set_existing; exact VALUE].
  - rewrite Nat2Z.inj_succ in LENGTH; assert (LT : value<upper) by (pose proof (Nat2Z.is_nonneg count); lia).
    pose proof (@matmul_inner_test temps memory value INV VALUE ltac:(lia)) as TEST;
      rewrite (proj2 (Z.ltb_lt value upper) LT) in TEST.
    assert (NORMAL : forall le m tr le' m' out,
      exec_stmt fe ge locals le m (double_matmul_body site) tr le' m' out -> out=Out_normal)
      by (intros; inversion H; reflexivity).
    assert (FRAME : forall le m tr le' m',
      exec_stmt fe ge locals le m (double_matmul_body site) tr le' m' Out_normal -> le' ! (matmul_k site)=le ! (matmul_k site))
      by (intros; inversion H; reflexivity).
    destruct (@memory_long_iteration_decode fe ge locals temps memory (matmul_k site)
      (double_matmul_long_condition (matmul_k site) bound) (double_matmul_body site) value after final
      TEST VALUE NORMAL FRAME RUN) as [body_temps [body_memory [BODY REST]]].
    destruct (double_matmul_source_decode (matmul_inner_entry INV VALUE ltac:(lia)) BODY)
      as [_ [SAME [_ ACTION]]]; subst body_temps.
    assert (NEXT : matmul_inner_invariant
      (PTree.set (matmul_k site) (Vlong (Int64.repr (value+1))) temps) body_memory).
    { apply matmul_inner_increment_invariant; eapply matmul_inner_action_invariant; eauto; lia. }
    destruct (@IH (value+1) _ body_memory after final ltac:(lia) ltac:(lia) NEXT (PTree.gss _ _ _) REST) as [ITER EXIT].
    split; [eapply iterations_next; eauto|rewrite EXIT,PTree.set2; reflexivity].
Qed.

Theorem double_matmul_inner_loop_encode count : forall value temps memory final,
  upper=value+Z.of_nat count -> 0<=value -> matmul_inner_invariant temps memory ->
  temps ! (matmul_k site)=Some (Vlong (Int64.repr value)) ->
  counted_iterations (double_matmul_inner_action site blocks i j) count value memory final ->
  exec_stmt fe ge locals temps memory
    (memory_long_frontend_loop (matmul_k site) (double_matmul_long_condition (matmul_k site) bound)
      (double_matmul_body site)) E0 (PTree.set (matmul_k site) (Vlong (Int64.repr upper)) temps) final Out_normal.
Proof.
  induction count as [|count IH]; intros value temps memory final LENGTH LOWER INV VALUE ITER.
  - assert (SAME : value=upper) by (cbn in LENGTH; lia); subst value.
    inversion ITER as [x state|]; subst x state final.
    rewrite (@memory_long_temp_set_existing temps (matmul_k site) (Vlong (Int64.repr upper)) VALUE).
    apply memory_long_loop_stop_execution; pose proof (@matmul_inner_test temps memory upper INV VALUE ltac:(lia)) as TEST;
      rewrite Z.ltb_irrefl in TEST; exact TEST.
  - rewrite Nat2Z.inj_succ in LENGTH; assert (LT : value<upper) by (pose proof (Nat2Z.is_nonneg count); lia).
    inversion ITER as [|n x first middle last ACTION REST]; subst n x first last.
    pose proof (@matmul_inner_test temps memory value INV VALUE ltac:(lia)) as TEST;
      rewrite (proj2 (Z.ltb_lt value upper) LT) in TEST.
    assert (BODY : exec_stmt fe ge locals temps memory (double_matmul_body site) E0 temps middle Out_normal).
    { eapply double_matmul_lowered_execution; [eapply matmul_inner_entry; eauto; lia|exact ACTION]. }
    assert (NEXT : matmul_inner_invariant (PTree.set (matmul_k site) (Vlong (Int64.repr (value+1))) temps) middle).
    { apply matmul_inner_increment_invariant; eapply matmul_inner_action_invariant; eauto; lia. }
    pose proof (@IH (value+1) _ middle final ltac:(lia) ltac:(lia) NEXT (PTree.gss _ _ _) REST) as TAIL.
    rewrite PTree.set2 in TAIL; eapply memory_long_iteration_encode; eauto.
Qed.

Theorem double_matmul_initialized_inner_equivalence count temps memory after final :
  upper=Z.of_nat count -> matmul_inner_invariant temps memory ->
  (exec_stmt fe ge locals temps memory (double_matmul_inner_source site bound) E0 after final Out_normal <->
   counted_iterations (double_matmul_inner_action site blocks i j) count 0 memory final /\
   after=PTree.set (matmul_k site) (Vlong (Int64.repr upper)) temps).
Proof.
  intros LENGTH INV; split.
  - intro RUN; apply memory_long_initialized_decode in RUN.
    assert (INIT : matmul_inner_invariant (PTree.set (matmul_k site) (Vlong Int64.zero) temps) memory)
      by (apply matmul_inner_increment_invariant; exact INV).
    destruct (@double_matmul_inner_loop_decode count 0 _ memory after final ltac:(lia) ltac:(lia) INIT (PTree.gss _ _ _) RUN)
      as [ITER EXIT]; split; [exact ITER|rewrite EXIT,PTree.set2; reflexivity].
  - intros [ITER EXIT]; subst after; unfold double_matmul_inner_source, memory_long_initialized_loop.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [apply memory_long_initialization_execution|].
    assert (INIT : matmul_inner_invariant (PTree.set (matmul_k site) (Vlong Int64.zero) temps) memory)
      by (apply matmul_inner_increment_invariant; exact INV).
    pose proof (@double_matmul_inner_loop_encode count 0 _ memory final ltac:(lia) ltac:(lia) INIT (PTree.gss _ _ _) ITER) as LOOP.
    rewrite PTree.set2 in LOOP; exact LOOP.
Qed.
End INNER.

Print Assumptions double_matmul_point_entry.
Print Assumptions memory_long_initialized_decode.
Print Assumptions double_matmul_inner_loop_decode.
Print Assumptions double_matmul_inner_loop_encode.
Print Assumptions double_matmul_initialized_inner_equivalence.
