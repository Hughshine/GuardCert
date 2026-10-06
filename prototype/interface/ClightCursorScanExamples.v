From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightCountedLoop ClightTempFrame ClightTempFootprint.
From GuardInterface Require Import ClightCursorBoundedScan ClightBoundedCheckLoop ClightCursorSpecialization
  ClightCursorCheckBody ClightCheckPlan ClightPrivateScan ClightPrivateScanSafety ClightSharedGuard ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition cursor_example_unreadable :=
  Ederef (Econst_int Int.zero (Tpointer type_int32s noattr)) type_int32s.
Definition cursor_example_reject_first cursor :=
  Test (Ebinop Oeq (Etempvar cursor type_int32s) (Econst_int Int.zero type_int32s) type_int32s)
    (Decision false) (Test cursor_example_unreadable (Decision true) (Decision false)).

Lemma cursor_example_unreadable_undefined ge locals temps memory value :
  ~ eval_expr ge locals temps memory cursor_example_unreadable value.
Proof.
  unfold cursor_example_unreadable; intro RUN; inversion RUN; subst.
  match goal with RUN : eval_lvalue _ _ _ _ (Ederef _ _) _ _ _ |- _ => inversion RUN; subst end.
  match goal with RUN : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => inversion RUN end.
  eliminate_impossible_lvalue.
Qed.

Lemma cursor_example_literal_true entry :
  expression_test (Econst_int Int.one type_int32s) entry true.
Proof. exists (Vint Int.one); split; [constructor|reflexivity]. Qed.

Lemma cursor_example_first_probe entry cursor :
  decision_run entry (cursor_tree_at cursor 0 (cursor_example_reject_first cursor)) false.
Proof.
  unfold cursor_example_reject_first; cbn [cursor_tree_at cursor_expression_at];
    destruct (peq cursor cursor); [|congruence].
  eapply run_test with (b:=true); [|constructor].
  exists (Val.of_bool true); split; [|reflexivity].
  eapply eval_Ebinop; [constructor|constructor|reflexivity].
Qed.

(** Both scratch slots are absent at entry. A rejected first point leaves an
    undefined later probe and all remaining iterations unevaluated. *)
Theorem cursor_example_rejects_before_unreadable
  (fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop)
  ge locals memory cursor result fuel :
  cursor <> result -> Z.of_nat (S fuel) <= Int.max_signed ->
  exists after,
    exec_stmt fe ge locals (PTree.empty val) memory
      (cursor_bounded_scan cursor 0 (Z.of_nat (S fuel)) (Econst_int Int.one type_int32s)
        (cursor_example_reject_first cursor) result) E0 after memory Out_normal /\
    after ! cursor=Some (Vint Int.zero) /\ after ! result=Some (Vint Int.zero).
Proof.
  intros DISTINCT CAP.
  assert (CHECK : decision_run (Entry ge locals (PTree.empty val) memory)
    (bounded_check_tree (fun j => cursor_expression_at cursor j (Econst_int Int.one type_int32s))
      (fun j => cursor_tree_at cursor j (cursor_example_reject_first cursor)) (S fuel) 0) false).
  { cbn [bounded_check_tree cursor_expression_at]; eapply run_test with (b:=true).
    - apply cursor_example_literal_true.
    - eapply decision_bind_run with (b:=false); [apply cursor_example_first_probe|constructor]. }
  destruct (@cursor_bounded_scan_execution fe (Entry ge locals (PTree.empty val) memory) cursor result 0
    (Z.of_nat (S fuel)) (Econst_int Int.one type_int32s) (cursor_example_reject_first cursor) [] (S fuel) false
    DISTINCT ltac:(cbn; tauto) ltac:(cbn; tauto)
    ltac:(unfold cursor_example_reject_first,cursor_example_unreadable; cbn; intros [SAME|[]]; congruence)
    ltac:(cbn; tauto)
    ltac:(unfold cursor_example_reject_first,cursor_example_unreadable; cbn; intros identifier [SAME|[]] OTHER; congruence)
    ltac:(unfold signed_range; change (-2147483648 <= 0 <= 2147483647); lia)
    ltac:(unfold signed_range; change Int.min_signed with (-2147483648); pose proof (Nat2Z.is_nonneg (S fuel)); lia)
    ltac:(lia) CHECK) as [after [RUN [FRAME FLAG]]].
  (* The exact first-iteration execution proves that rejection performs no
     increment. This is stronger than the public frame of the generic API. *)
  set (initialized := PTree.set cursor (Vint Int.zero) (PTree.set result (Vint Int.one) (PTree.empty val))).
  assert (POINT : exec_stmt fe ge locals initialized memory
    (cursor_check_body (cursor_example_reject_first cursor) result) E0
    (PTree.set result (Vint Int.zero) initialized) memory Out_normal).
  { unfold cursor_check_body; eapply (@check_plan_code_execution fe (Entry ge locals initialized memory)
      (tree_check_plan (cursor_example_reject_first cursor)) false).
    - apply check_plan_tree_run; rewrite tree_check_plan_spec.
      eapply (@cursor_tree_run_transport (cursor_example_reject_first cursor)
        (Entry ge locals (PTree.empty val) memory) cursor 0 initialized false).
      + unfold initialized; apply PTree.gss.
      + unfold cursor_example_reject_first,cursor_example_unreadable;
          cbn [cursor_tree_at cursor_expression_at]; destruct (peq cursor cursor); cbn; intros identifier MEMBER; contradiction.
      + apply cursor_example_first_probe.
    - unfold cursor_example_reject_first,cursor_example_unreadable; cbn; intros [SAME|[]]; congruence.
    - apply temp_agree_refl. }
  exists after; split; [exact RUN|split; [|exact FLAG]].
  (* A direct, quiet witness below fixes the private cursor at zero. *)
  assert (EXACT : exec_stmt fe ge locals (PTree.empty val) memory
    (cursor_bounded_scan cursor 0 (Z.of_nat (S fuel)) (Econst_int Int.one type_int32s)
      (cursor_example_reject_first cursor) result) E0 (PTree.set result (Vint Int.zero) initialized) memory Out_normal).
  { unfold cursor_bounded_scan,bounded_check_prefix.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [constructor; constructor|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [constructor; constructor|].
    unfold bounded_check_loop; eapply exec_Sloop_stop1 with (out':=Out_break); [|constructor].
    destruct (@bounded_check_ceiling_test ge locals initialized memory cursor 0 (Z.of_nat (S fuel))
      ltac:(unfold initialized; apply PTree.gss)
      ltac:(unfold signed_range; change (-2147483648 <= 0 <= 2147483647); lia)
      ltac:(unfold signed_range; change Int.min_signed with (-2147483648); pose proof (Nat2Z.is_nonneg (S fuel)); lia)) as [value [EVAL BOOL]].
    assert (POSITIVE : (0 <? Z.of_nat (S fuel))=true) by (apply Z.ltb_lt; rewrite Nat2Z.inj_succ; lia).
    rewrite POSITIVE in BOOL; eapply exec_Sifthenelse with (b:=true); [exact EVAL|exact BOOL|].
    eapply bounded_check_iteration_active with (answer:=false); [apply cursor_example_literal_true|exact POINT|apply PTree.gss]. }
  destruct (@ClightQuietDeterminacy.quiet_execution_determinate _ _ _ _ _ _ _ _ _ _ EXACT
    ltac:(apply private_scan_quiet,cursor_bounded_scan_supported) _ _ _ _ RUN) as [_ [TEMPS REST]].
  rewrite <- TEMPS; unfold initialized; rewrite PTree.gso by congruence; apply PTree.gss.
Qed.

Print Assumptions cursor_example_unreadable_undefined.
Print Assumptions cursor_example_first_probe.
Print Assumptions cursor_example_rejects_before_unreadable.
