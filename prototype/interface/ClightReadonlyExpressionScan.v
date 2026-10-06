From Stdlib Require Import ZArith Lia.
From compcert.lib Require Import Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightCondition ClightCountedLoop ClightNoWrap ClightPureExpr.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyConditionComposition ReadonlyBranching ReadonlyPrefixScan
  ClightReadonlyRewrite ClightConditionComposition ClightReadonlyBranching ClightReadonlyLoadedTreeSynthesis.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint readonly_bound_expression_scan bound probe fuel index :=
  match fuel with
  | O => Decision true
  | S rest => Test (Ebinop Olt (Econst_int (Int.repr index) type_int32s) bound type_int32s)
      (decision_bind (probe index) (readonly_bound_expression_scan bound probe rest (index+1)) (Decision false))
      (Decision true)
  end.

(** A language service for an immutable, evaluated signed bound expression.
    This can scan one reached affine row. It does not establish permission to
    reach another outer row; the loaded-source prefix service supplies that. *)
Section EXPRESSION_SCAN.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Variable bound : expr.
Variable width : clight_entry -> Z.
Variable domain : clight_entry -> Prop.
Variable probe : Z -> decision_tree.
Variable property : Z -> clight_entry -> Prop.
Hypothesis TYPE : typeof bound = type_int32s.
Hypothesis VALUE : forall entry, domain entry ->
  eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    bound (Vint (Int.repr (width entry))).
Hypothesis RANGE : forall entry, domain entry -> 0 <= width entry <= Int.max_signed.
Hypothesis POINT : forall index, readonly_condition (readonly_clight_host fe observe)
  (fun entry => domain entry /\ 0 <= index < width entry) (property index) (probe index).

Definition expression_scan_invariant index entry := domain entry /\ 0 <= index <= width entry.
Definition expression_scan_active index :=
  Test (Ebinop Olt (Econst_int (Int.repr index) type_int32s) bound type_int32s)
    (Decision true) (Decision false).

Lemma expression_scan_test index entry : expression_scan_invariant index entry ->
  expression_test (Ebinop Olt (Econst_int (Int.repr index) type_int32s) bound type_int32s)
    entry (index <? width entry).
Proof.
  intros [DOMAIN INDEX]; pose proof (@RANGE entry DOMAIN) as WIDTH.
  assert (SIGNED_INDEX : signed_range index) by
    (unfold signed_range; change Int.min_signed with (-2147483648); lia).
  assert (SIGNED_WIDTH : signed_range (width entry)) by
    (unfold signed_range; change Int.min_signed with (-2147483648); lia).
  exists (Val.of_bool (index <? width entry)); split; [|apply bool_of_bool].
  eapply eval_Ebinop; [constructor|apply VALUE; exact DOMAIN|].
  cbn [typeof]; rewrite TYPE.
  change (Some (Val.of_bool (Int.lt (Int.repr index) (Int.repr (width entry)))) =
    Some (Val.of_bool (index <? width entry))).
  unfold Int.lt; rewrite (Int.signed_repr index SIGNED_INDEX), (Int.signed_repr (width entry) SIGNED_WIDTH).
  destruct (zlt index (width entry)) as [LT|GE].
  - assert (FLAG : (index <? width entry) = true) by (apply Z.ltb_lt; exact LT); rewrite FLAG; reflexivity.
  - assert (FLAG : (index <? width entry) = false) by (apply Z.ltb_ge; lia); rewrite FLAG; reflexivity.
Qed.

Lemma expression_scan_activity index : readonly_classifier (readonly_clight_host fe observe)
  (expression_scan_invariant index) (fun entry => index < width entry)
  (fun entry => ~ index < width entry) (expression_scan_active index).
Proof.
  apply readonly_expression_classifier.
  - intros entry INV; eexists; apply expression_scan_test; exact INV.
  - intros entry INV TEST; pose proof (readonly_test_determinate (expression_scan_test INV) TEST) as FLAG.
    apply Z.ltb_lt; exact FLAG.
  - intros entry INV TEST; pose proof (readonly_test_determinate (expression_scan_test INV) TEST) as FLAG.
    apply Z.ltb_ge in FLAG; lia.
Defined.

Lemma expression_scan_point index : readonly_condition (readonly_clight_host fe observe)
  (fun entry => expression_scan_invariant index entry /\ index < width entry)
  (fun entry => property index entry /\ expression_scan_invariant (index+1) entry) (probe index).
Proof.
  eapply readonly_condition_entails.
  - eapply readonly_condition_restrict; [apply POINT|].
    intros entry [[DOMAIN INDEX] ACTIVE]; split; [exact DOMAIN|lia].
  - intros entry [[DOMAIN INDEX] ACTIVE] PROPERTY; split; [exact PROPERTY|split; [exact DOMAIN|lia]].
Defined.

Definition expression_scan_spec : readonly_prefix_spec (readonly_clight_host fe observe) Z :=
  @ReadonlyPrefixSpec clight_entry (readonly_clight_host fe observe) Z (fun index => index+1)
    expression_scan_active probe expression_scan_invariant (fun index entry => index < width entry)
    property expression_scan_activity expression_scan_point.

Lemma expression_scan_syntax fuel start :
  synthesize_prefix_scan (clight_readonly_check_algebra fe observe)
    (clight_readonly_branch_algebra fe observe) expression_scan_spec fuel start =
  readonly_bound_expression_scan bound probe fuel start.
Proof.
  revert start; induction fuel as [|fuel IH]; intro start;
    cbn [synthesize_prefix_scan readonly_bound_expression_scan expression_scan_spec
      expression_scan_active clight_readonly_check_algebra clight_readonly_branch_algebra
      branch_check constant_check prefix_active_probe prefix_point_probe prefix_next decision_bind];
    [reflexivity|rewrite IH; reflexivity].
Qed.

Lemma expression_scan_covered fuel start entry : prefix_scan_property expression_scan_spec fuel start entry ->
  forall index, start <= index < start + Z.of_nat fuel -> index < width entry -> property index entry.
Proof.
  revert start; induction fuel as [|fuel IH]; intros start PROP index INDEX ACTIVE;
    cbn [prefix_scan_property expression_scan_spec prefix_active prefix_next prefix_point_property] in PROP;
    [cbn in INDEX; lia|].
  destruct (PROP ltac:(lia)) as [PROPERTY REST].
  destruct (Z.eq_dec index start); [subst; exact PROPERTY|].
  eapply IH; [exact REST|rewrite Nat2Z.inj_succ in INDEX; lia|exact ACTIVE].
Qed.

Definition readonly_expression_scan_condition fuel : readonly_condition (readonly_clight_host fe observe)
  (fun entry => domain entry /\ width entry <= Z.of_nat fuel)
  (fun entry => forall index, 0 <= index < width entry -> property index entry)
  (readonly_bound_expression_scan bound probe fuel 0).
Proof.
  rewrite <- expression_scan_syntax.
  eapply readonly_condition_entails.
  - eapply readonly_condition_restrict; [apply synthesized_prefix_scan_condition|].
    intros entry [DOMAIN CAP]; split; [exact DOMAIN|pose proof (@RANGE entry DOMAIN); lia].
  - intros entry [DOMAIN CAP] PROP index INDEX.
    eapply expression_scan_covered; [exact PROP|lia|lia].
Defined.
End EXPRESSION_SCAN.

Print Assumptions expression_scan_test.
Print Assumptions expression_scan_activity.
Print Assumptions expression_scan_point.
Print Assumptions expression_scan_covered.
Print Assumptions expression_scan_syntax.
Print Assumptions readonly_expression_scan_condition.
