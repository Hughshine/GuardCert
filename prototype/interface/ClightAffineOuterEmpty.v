From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightPureExpr ClightTempFrame
  ClightRedundantSet ClightMatrixGuard ClightRegionProgress ClightFrontendLoopProtocol ClightCountedLoop
  ClightCountedProtocol ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryPointerSequence.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyCompletedCondition
  ClightReadonlyLoadedTreeSynthesis ClightAffineSnapshotSyntax ClightAffineSnapshotRows
  ClightAffineSnapshotSourceInputs ClightAffineSnapshotPreparation ClightAffineHeaderSnapshots
  ClightAffineEmptyExecution ClightQuietDeterminacy ClightLoadedBoundSyntax ClightStrictLoopProgress.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_outer_empty_test bound:=
  Ebinop Ole(Etempvar bound type_int32s)(Econst_int Int.zero type_int32s)type_int32s.
Definition affine_outer_empty_flag bound entry:=negb(Int.lt Int.zero(temp_word bound(entry_temps entry))).
Definition affine_outer_empty_tree row bound:=decision_bind(register_tree row Int.zero)
  (Test(affine_outer_empty_test bound)(Decision true)(Decision false))(Decision false).
Definition affine_outer_empty_fact row bound entry:=
  (entry_temps entry)!row=Some(Vint Int.zero) /\ affine_outer_empty_flag bound entry=true.

Lemma affine_outer_empty_test_run bound entry : register_domain bound entry ->
  expression_test(affine_outer_empty_test bound)entry(affine_outer_empty_flag bound entry).
Proof.
  intros [word LOOK]; unfold affine_outer_empty_flag,temp_word; rewrite LOOK.
  exists(Val.of_bool(negb(Int.lt Int.zero word))); split; [|apply bool_of_bool].
  unfold affine_outer_empty_test; eapply eval_Ebinop with(v1:=Vint word)(v2:=Vint Int.zero);
    [constructor; exact LOOK|constructor|reflexivity].
Qed.

Definition affine_outer_empty_condition fe O(observe:fragment_observation->O->Prop)row bound :
  readonly_condition(readonly_clight_host fe observe)
    (fun entry=>register_domain row entry /\ register_domain bound entry)
    (affine_outer_empty_fact row bound)(affine_outer_empty_tree row bound).
Proof.
  apply readonly_completed_tree_condition.
  - intros entry[ROW BOUND].
    exists(if register_flag row Int.zero entry then affine_outer_empty_flag bound entry else false).
    unfold affine_outer_empty_tree; eapply decision_bind_run; [apply register_tree_run; exact ROW|].
    destruct(register_flag row Int.zero entry); [|constructor].
    eapply run_test; [apply affine_outer_empty_test_run; exact BOUND|].
    destruct(affine_outer_empty_flag bound entry); constructor.
  - intros entry[ROW BOUND]RUN.
    unfold affine_outer_empty_tree in RUN; apply decision_bind_inv in RUN as [choice[PREFIX LEAF]].
    assert(CHOICE:choice=register_flag row Int.zero entry).
    { eapply readonly_decision_determinate; [exact PREFIX|apply register_tree_run; exact ROW]. }
    destruct choice; [|inversion LEAF].
    split; [eapply register_flag_evidence; [exact ROW|symmetry; exact CHOICE]|].
    assert(PATH:decision_run entry(Test(affine_outer_empty_test bound)(Decision true)(Decision false))
      (affine_outer_empty_flag bound entry)).
    { eapply run_test; [apply affine_outer_empty_test_run; exact BOUND|].
      destruct(affine_outer_empty_flag bound entry); constructor. }
    eapply readonly_decision_determinate; [exact PATH|exact LEAF].
Defined.

Section SOURCE.
Variable original : statement.
Variable site : affine_snapshot_source_package original.
Let package:=snapshot_cached_package site.
Let shape:=affine_inner_pointer_shape package.
Let row:=affine_inner_pointer_row shape.
Let bound:=affine_inner_pointer_bound shape.
Variable fe : genv->function->list val->mem->env->temp_env->mem->Prop.
Variable entry : clight_entry.

Theorem affine_outer_empty_source_complete :
  affine_snapshot_original_domain package(snapshot_root site)(snapshot_child site)
    (snapshot_child_cache site)(snapshot_original_header site)fe entry ->
  affine_outer_empty_fact row bound entry ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)original E0
    (entry_temps entry)(entry_memory entry)Out_normal.
Proof.
  intros [[block[offset[word[POINTER[CACHE READ]]]]][CHILD COMPLETE]][ZERO EMPTY].
  change((entry_temps entry)!bound=Some(Vint word))in CACHE.
  unfold affine_outer_empty_flag,temp_word in EMPTY; rewrite CACHE in EMPTY.
  apply negb_true_iff in EMPTY.
  rewrite(snapshot_source_exact site); unfold affine_snapshot_source.
  apply strict_empty_false_execution.
  rewrite <-EMPTY; eapply loaded_bound_test_eval; eassumption.
Qed.

Theorem affine_outer_empty_source_exit after final :
  affine_snapshot_original_domain package(snapshot_root site)(snapshot_child site)
    (snapshot_child_cache site)(snapshot_original_header site)fe entry ->
  affine_outer_empty_fact row bound entry ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)original E0
    after final Out_normal -> after=entry_temps entry /\ final=entry_memory entry.
Proof.
  intros DOMAIN EMPTY SOURCE.
  assert(QUIET:quiet_statement original=true).
  { rewrite(snapshot_source_exact site); unfold affine_snapshot_source,affine_snapshot_body,affine_setup_child;
      cbn [strict_frontend_loop quiet_statement rectangle_reset frontend_counted_loop counter_increment].
    fold package shape.
    pose proof(@memory_pointer_sequence_quiet _ _ (affine_inner_pointer_body_exact(affine_inner_pointer_syntax package)))as LEAF.
    fold package shape in LEAF; rewrite LEAF; reflexivity. }
  destruct(@quiet_execution_determinate fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    original E0 after final Out_normal SOURCE QUIET E0(entry_temps entry)(entry_memory entry)Out_normal
    (affine_outer_empty_source_complete DOMAIN EMPTY))as [_[TEMPS[MEMORY OUT]]].
  split; assumption.
Qed.
End SOURCE.

Print Assumptions affine_outer_empty_condition.
Print Assumptions affine_outer_empty_source_complete.
Print Assumptions affine_outer_empty_source_exit.
