From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightCountedLoop ClightFramedLoop ClightTempFrame ClightNoWrap.
From GuardInterface Require Import ClightSharedGuard ClightPrivateScan ClightQuietDeterminacy ClightPrivateScanSafety.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Logical unfolding is a specification only. Runtime code contains one
    loop body, and rejects before another body or its activity test is read. *)
Fixpoint bounded_check_tree (active : Z -> expr) (probe : Z -> decision_tree) fuel index :=
  match fuel with
  | O => Decision true
  | S rest => Test (active index)
      (decision_bind (probe index) (bounded_check_tree active probe rest (index+1)) (Decision false))
      (Decision true)
  end.

Inductive bounded_check_run entry active probe : nat -> Z -> bool -> Prop :=
| bounded_check_done : forall index, bounded_check_run entry active probe O index true
| bounded_check_inactive : forall fuel index,
    expression_test (active index) entry false -> bounded_check_run entry active probe (S fuel) index true
| bounded_check_reject : forall fuel index,
    expression_test (active index) entry true -> decision_run entry (probe index) false ->
    bounded_check_run entry active probe (S fuel) index false
| bounded_check_next : forall fuel index answer,
    expression_test (active index) entry true -> decision_run entry (probe index) true ->
    bounded_check_run entry active probe fuel (index+1) answer ->
    bounded_check_run entry active probe (S fuel) index answer.

Theorem bounded_check_tree_exact entry active probe fuel index answer :
  bounded_check_run entry active probe fuel index answer <->
  decision_run entry (bounded_check_tree active probe fuel index) answer.
Proof.
  split.
  - intro RUN; induction RUN; cbn [bounded_check_tree].
    + constructor.
    + eapply run_test with (b:=false); [exact H|constructor].
    + eapply run_test with (b:=true); [exact H|eapply decision_bind_run; [exact H0|constructor]].
    + eapply run_test with (b:=true); [exact H|eapply decision_bind_run; eassumption].
  - revert index answer; induction fuel as [|fuel IH]; intros index answer RUN; cbn [bounded_check_tree] in RUN.
    + inversion RUN; subst; constructor.
    + inversion RUN; subst; destruct b.
      * match goal with BOUND : decision_run _ (decision_bind _ _ _) _ |- _ =>
          destruct (@decision_bind_inv (probe index) entry (bounded_check_tree active probe fuel (index+1))
            (Decision false) answer BOUND) as [choice [POINT REST]] end.
        destruct choice.
        -- eapply bounded_check_next; [eassumption|exact POINT|apply IH; exact REST].
        -- inversion REST; subst; eapply bounded_check_reject; eassumption.
      * match goal with LEAF : decision_run _ (Decision true) _ |- _ => inversion LEAF; subst end.
        apply bounded_check_inactive; assumption.
Qed.

Definition bounded_check_ceiling cursor ceiling :=
  Ebinop Olt (Etempvar cursor type_int32s) (Econst_int (Int.repr ceiling) type_int32s) type_int32s.
Definition bounded_check_iteration active body result :=
  Sifthenelse active (Ssequence body (Sifthenelse (shared_guard_choice result) Sskip Sbreak)) Sbreak.
Definition bounded_check_loop cursor ceiling active body result :=
  Sloop (Sifthenelse (bounded_check_ceiling cursor ceiling)
    (bounded_check_iteration active body result) Sbreak) (counter_increment cursor).
Definition bounded_check_prefix cursor start ceiling active body result :=
  Ssequence (Sset result (Econst_int Int.one type_int32s))
    (Ssequence (Sset cursor (Econst_int (Int.repr start) type_int32s))
      (bounded_check_loop cursor ceiling active body result)).

Lemma bounded_check_ceiling_test ge locals temps memory cursor index ceiling :
  temps ! cursor = Some (Vint (Int.repr index)) -> signed_range index -> signed_range ceiling ->
  expression_test (bounded_check_ceiling cursor ceiling) (Entry ge locals temps memory) (index <? ceiling).
Proof.
  intros CURSOR INDEX CEILING; exists (Val.of_bool (index <? ceiling)); split; [|apply bool_of_bool].
  unfold bounded_check_ceiling; eapply eval_Ebinop; [constructor; exact CURSOR|constructor|].
  change (Some (Val.of_bool (Int.lt (Int.repr index) (Int.repr ceiling))) = Some (Val.of_bool (index <? ceiling))).
  unfold Int.lt; rewrite !Int.signed_repr by assumption.
  destruct (zlt index ceiling) as [LT|GE].
  - assert (FLAG : (index <? ceiling)=true) by (apply Z.ltb_lt; exact LT); rewrite FLAG; reflexivity.
  - assert (FLAG : (index <? ceiling)=false) by (apply Z.ltb_ge; lia); rewrite FLAG; reflexivity.
Qed.

Lemma bounded_check_iteration_active fe ge locals temps memory active body result answer after :
  expression_test active (Entry ge locals temps memory) true ->
  exec_stmt fe ge locals temps memory body E0 after memory Out_normal ->
  after ! result = Some (Vint (shared_guard_word answer)) ->
  exec_stmt fe ge locals temps memory (bounded_check_iteration active body result)
    E0 after memory (if answer then Out_normal else Out_break).
Proof.
  intros [value [EVAL BOOL]] BODY FLAG; unfold bounded_check_iteration.
  eapply exec_Sifthenelse with (v1:=value) (b:=true); [exact EVAL|exact BOOL|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact BODY|].
  destruct (@shared_guard_choice_test ge locals after memory result answer FLAG) as [choice [TEST CAST]].
  eapply exec_Sifthenelse; [exact TEST|exact CAST|destruct answer; constructor].
Qed.
Lemma bounded_check_iteration_inactive fe ge locals temps memory active body result :
  expression_test active (Entry ge locals temps memory) false ->
  exec_stmt fe ge locals temps memory (bounded_check_iteration active body result) E0 temps memory Out_break.
Proof.
  intros [value [EVAL BOOL]]; unfold bounded_check_iteration.
  eapply exec_Sifthenelse with (v1:=value) (b:=false); [exact EVAL|exact BOOL|constructor].
Qed.

Section REALIZATION.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable entry : clight_entry.
Variables cursor result : ident.
Variables floor ceiling : Z.
Variables active : expr.
Variable body : statement.
Variable live : list ident.
Variables active_at : Z -> expr.
Variable probe : Z -> decision_tree.
Hypothesis CURSOR_RESULT : cursor <> result.
Hypothesis CURSOR_PRIVATE : ~ In cursor live.
Hypothesis CEILING : signed_range ceiling.
Hypothesis ACTIVITY : forall index current choice,
  floor <= index -> signed_range index -> current ! cursor = Some (Vint (Int.repr index)) ->
  temp_agree live (entry_temps entry) current -> expression_test (active_at index) entry choice ->
  expression_test active (Entry (entry_ge entry) (entry_env entry) current (entry_memory entry)) choice.
Hypothesis POINT : forall index current answer,
  floor <= index < ceiling -> signed_range index -> current ! cursor = Some (Vint (Int.repr index)) ->
  current ! result = Some (Vint Int.one) -> temp_agree live (entry_temps entry) current ->
  decision_run entry (probe index) answer ->
  exists after,
    exec_stmt fe (entry_ge entry) (entry_env entry) current (entry_memory entry) body E0 after (entry_memory entry) Out_normal /\
    temp_agree (cursor::live) current after /\ after ! result = Some (Vint (shared_guard_word answer)).

Theorem bounded_check_loop_execution fuel index answer :
  bounded_check_run entry active_at probe fuel index answer ->
  forall current, ceiling = index+Z.of_nat fuel -> floor <= index -> signed_range index ->
  current ! cursor = Some (Vint (Int.repr index)) -> current ! result = Some (Vint Int.one) ->
  temp_agree live (entry_temps entry) current ->
  exists after,
    exec_stmt fe (entry_ge entry) (entry_env entry) current (entry_memory entry)
      (bounded_check_loop cursor ceiling active body result) E0 after (entry_memory entry) Out_normal /\
    temp_agree live current after /\ after ! result = Some (Vint (shared_guard_word answer)).
Proof.
  intro RUN; induction RUN; intros current LENGTH FLOOR INDEX CURSOR FLAG FRAME.
  - cbn in LENGTH; assert (SAME : index=ceiling) by lia; subst index.
    exists current; split; [|split; [apply temp_agree_refl|exact FLAG]].
    unfold bounded_check_loop; eapply exec_Sloop_stop1 with (out':=Out_break); [|constructor].
    destruct (@bounded_check_ceiling_test (entry_ge entry) (entry_env entry) current (entry_memory entry) cursor _ ceiling CURSOR INDEX CEILING) as [value [EVAL BOOL]].
    rewrite Z.ltb_irrefl in BOOL; eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor].
  - assert (LT : (index <? ceiling)=true) by (apply Z.ltb_lt; rewrite Nat2Z.inj_succ in LENGTH; lia).
    exists current; split; [|split; [apply temp_agree_refl|exact FLAG]].
    unfold bounded_check_loop; eapply exec_Sloop_stop1 with (out':=Out_break); [|constructor].
    destruct (@bounded_check_ceiling_test (entry_ge entry) (entry_env entry) current (entry_memory entry) cursor _ ceiling CURSOR INDEX CEILING) as [value [EVAL BOOL]].
    rewrite LT in BOOL; eapply exec_Sifthenelse with (b:=true); [exact EVAL|exact BOOL|].
    apply bounded_check_iteration_inactive,ACTIVITY with (index:=index); assumption.
  - assert (LT : (index <? ceiling)=true) by (apply Z.ltb_lt; rewrite Nat2Z.inj_succ in LENGTH; lia).
    destruct (@POINT index current false ltac:(apply Z.ltb_lt in LT; lia) INDEX CURSOR FLAG FRAME H0) as [after [BODY [PUBLIC RESULT]]].
    exists after; split.
    + unfold bounded_check_loop; eapply exec_Sloop_stop1 with (out':=Out_break); [|constructor].
      destruct (@bounded_check_ceiling_test (entry_ge entry) (entry_env entry) current (entry_memory entry) cursor _ ceiling CURSOR INDEX CEILING) as [value [EVAL BOOL]].
      rewrite LT in BOOL; eapply exec_Sifthenelse with (b:=true); [exact EVAL|exact BOOL|].
      apply bounded_check_iteration_active with (answer:=false); [apply ACTIVITY with (index:=index)|exact BODY|exact RESULT]; assumption.
    + split; [eapply temp_agree_weaken; [|exact PUBLIC]; cbn; auto|exact RESULT].
  - assert (LT : (index <? ceiling)=true) by (apply Z.ltb_lt; rewrite Nat2Z.inj_succ in LENGTH; lia).
    destruct (@POINT index current true ltac:(apply Z.ltb_lt in LT; lia) INDEX CURSOR FLAG FRAME H0) as [middle [BODY [PUBLIC RESULT]]].
    assert (MID_CURSOR : middle ! cursor=Some (Vint (Int.repr index))) by (rewrite PUBLIC by (cbn; auto); exact CURSOR).
    assert (NEXT_RANGE : signed_range (index+1)) by (unfold signed_range in *; apply Z.ltb_lt in LT; lia).
    assert (NEXT_FRAME : temp_agree live current (counter_temps cursor middle (index+1))).
    { eapply temp_agree_trans; [eapply temp_agree_weaken; [|exact PUBLIC]; cbn; auto|apply temp_agree_set; exact CURSOR_PRIVATE]. }
    destruct (IHRUN (counter_temps cursor middle (index+1))) as [after [REST [REST_FRAME EXIT]]].
    + rewrite Nat2Z.inj_succ in LENGTH; lia.
    + lia.
    + exact NEXT_RANGE.
    + unfold counter_temps; apply PTree.gss.
    + unfold counter_temps; rewrite PTree.gso by congruence; exact RESULT.
    + eapply temp_agree_trans; [exact FRAME|exact NEXT_FRAME].
    + exists after; split.
      * unfold bounded_check_loop; eapply exec_Sloop_loop with (out1:=Out_normal) (t1:=E0) (t2:=E0) (t3:=E0).
        -- destruct (@bounded_check_ceiling_test (entry_ge entry) (entry_env entry) current (entry_memory entry) cursor _ ceiling CURSOR INDEX CEILING) as [value [EVAL BOOL]].
           rewrite LT in BOOL; eapply exec_Sifthenelse with (b:=true); [exact EVAL|exact BOOL|].
           apply bounded_check_iteration_active with (answer:=true); [apply ACTIVITY with (index:=index)|exact BODY|exact RESULT]; assumption.
        -- constructor.
        -- exact (@counter_increment_at fe _ _ middle _ cursor index MID_CURSOR INDEX).
        -- exact REST.
      * split; [eapply temp_agree_trans; [exact NEXT_FRAME|exact REST_FRAME]|exact EXIT].
Qed.
Hypothesis RESULT_PRIVATE : ~ In result live.

(** Initialization is actual code. Neither scratch slot needs an entry value. *)
Theorem bounded_check_prefix_execution fuel start answer :
  ceiling = start+Z.of_nat fuel -> floor <= start -> signed_range start ->
  decision_run entry (bounded_check_tree active_at probe fuel start) answer ->
  exists after,
    exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
      (bounded_check_prefix cursor start ceiling active body result) E0 after (entry_memory entry) Out_normal /\
    temp_agree live (entry_temps entry) after /\ after ! result = Some (Vint (shared_guard_word answer)).
Proof.
  intros LENGTH FLOOR START CHECK.
  set (initialized := counter_temps cursor (PTree.set result (Vint Int.one) (entry_temps entry)) start).
  assert (INITIAL_FRAME : temp_agree live (entry_temps entry) initialized).
  { unfold initialized,counter_temps; eapply temp_agree_trans; apply temp_agree_set; assumption. }
  destruct (@bounded_check_loop_execution fuel start answer (proj2 (bounded_check_tree_exact _ _ _ _ _ _) CHECK) initialized)
    as [after [LOOP [FRAME FLAG]]].
  - exact LENGTH.
  - exact FLOOR.
  - exact START.
  - unfold initialized,counter_temps; apply PTree.gss.
  - unfold initialized,counter_temps; rewrite PTree.gso by congruence; apply PTree.gss.
  - exact INITIAL_FRAME.
  - exists after; split.
    + unfold bounded_check_prefix; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [constructor; constructor|].
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [constructor; constructor|exact LOOP].
    + split; [eapply temp_agree_trans; [exact INITIAL_FRAME|exact FRAME]|exact FLAG].
Qed.
End REALIZATION.

Lemma bounded_check_loop_supported cursor ceiling active body result :
  private_scan_statement body -> private_scan_statement (bounded_check_loop cursor ceiling active body result).
Proof.
  intro BODY; unfold bounded_check_loop,bounded_check_iteration,counter_increment.
  auto 8 using scan_loop,scan_if,scan_sequence,scan_skip,scan_break,scan_set.
Qed.

Lemma bounded_check_prefix_supported cursor start ceiling active body result :
  private_scan_statement body -> private_scan_statement (bounded_check_prefix cursor start ceiling active body result).
Proof.
  intro BODY; unfold bounded_check_prefix; apply scan_sequence; [constructor|].
  apply scan_sequence; [constructor|apply bounded_check_loop_supported; exact BODY].
Qed.

Print Assumptions bounded_check_tree_exact.
Print Assumptions bounded_check_ceiling_test.
Print Assumptions bounded_check_iteration_active.
Print Assumptions bounded_check_iteration_inactive.
Print Assumptions bounded_check_loop_execution.
Print Assumptions bounded_check_prefix_execution.
Print Assumptions bounded_check_loop_supported.
Print Assumptions bounded_check_prefix_supported.
