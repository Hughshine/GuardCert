From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers Coqlib.
From compcert.common Require Import Values.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightCondition ClightPureExpr ClightRectangularStore
  ClightCountedLoop ClightPositiveDivision ClightRectangularGuard ClightNoWrap.
From GuardMemory Require Import GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorAccess.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyTreeFacts.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma tensor_volume_cap_range : 1<=tensor_volume_cap<=Int.max_signed.
Proof.
  unfold tensor_volume_cap; split; [apply Z.min_glb|apply Z.le_min_l].
  - change Int.max_signed with 2147483647; lia.
  - change(1<=if Archi.ptr64 then 4611686018427387904 else 1073741824).
    destruct Archi.ptr64; lia.
Qed.
Lemma tensor_quotient_bound limit accumulated dimension : 0<dimension ->
  (accumulated<=limit/dimension <-> accumulated*dimension<=limit).
Proof.
  intro POSITIVE; split; intro BOUND.
  - pose proof(Z.div_mod limit dimension ltac:(lia)).
    pose proof(Z.mod_pos_bound limit dimension POSITIVE); nia.
  - apply Z.div_le_lower_bound; [exact POSITIVE|nia].
Qed.

Lemma tensor_positive_volume dimensions : Forall(fun dimension=>0<dimension)dimensions -> 1<=tensor_volume dimensions.
Proof.
  intro POSITIVE; induction POSITIVE; cbn [tensor_volume]; [lia|nia].
Qed.

Fixpoint tensor_volume_check limit accumulated dimensions :=
  match dimensions with
  | [] => true
  | dimension::rest =>
      if (0 <? dimension)&&(accumulated <=? limit/dimension)
      then tensor_volume_check limit(accumulated*dimension)rest else false end.
Theorem tensor_volume_check_spec limit accumulated dimensions :
  0<accumulated -> accumulated<=limit ->
  (tensor_volume_check limit accumulated dimensions=true <->
    Forall(fun dimension=>0<dimension)dimensions /\ accumulated*tensor_volume dimensions<=limit).
Proof.
  revert accumulated; induction dimensions as [|dimension rest IH]; intros accumulated POSITIVE LIMIT; cbn.
  - split; intro H; [split; [constructor|nia]|reflexivity].
  - destruct((0 <? dimension)&&(accumulated <=? limit/dimension)) eqn:CHECK.
    + rewrite andb_true_iff,Z.ltb_lt,Z.leb_le in CHECK; destruct CHECK as [D A].
      apply tensor_quotient_bound in A; [|exact D].
      rewrite IH by nia; split; intros [DS VOLUME]; split; [constructor; assumption|nia| |nia].
      inversion DS; assumption.
    + split; [discriminate|]; intros [DS VOLUME]; inversion DS as [|? ? D REST]; subst.
      assert(REST_VOLUME:1<=tensor_volume rest).
      { apply tensor_positive_volume; exact REST. }
      assert(ACCEPT:(0 <? dimension)&&(accumulated <=? limit/dimension)=true).
      { rewrite andb_true_iff,Z.ltb_lt,Z.leb_le; split; [exact D|].
        apply tensor_quotient_bound; [exact D|nia]. }
      congruence.
Qed.
Theorem tensor_volume_check_layout dimensions :
  tensor_volume_check tensor_volume_cap 1 dimensions=true <-> tensor_layout_flag dimensions=true.
Proof.
  rewrite tensor_volume_check_spec by(pose proof tensor_volume_cap_range; lia).
  unfold tensor_layout_flag; rewrite andb_true_iff,Z.leb_le; replace(1*tensor_volume dimensions)with(tensor_volume dimensions)by ring.
  apply and_iff_compat_r; rewrite Forall_forall,forallb_forall; split; intros H dimension MEMBER.
  - apply Z.ltb_lt,H; exact MEMBER.
  - apply Z.ltb_lt,H; exact MEMBER.
Qed.

Definition tensor_positive_expression code := Ebinop Olt(rect_constant 0)code type_int32s.
Definition tensor_quotient_expression dimension := Ebinop Odiv(rect_constant tensor_volume_cap)dimension type_int32s.
Definition tensor_prefix_expression accumulated dimension :=
  Ebinop Ole accumulated(tensor_quotient_expression dimension)type_int32s.
Fixpoint tensor_volume_guard_from accumulated dimensions :=
  match dimensions with
  | [] => Decision true
  | dimension::rest => Test(tensor_positive_expression dimension)
      (Test(tensor_prefix_expression accumulated dimension)
        (tensor_volume_guard_from(tensor_product accumulated dimension)rest)(Decision false))
      (Decision false) end.
Definition tensor_volume_guard dimensions := tensor_volume_guard_from(rect_constant 1)dimensions.
Definition tensor_guard_operand entry code dimension :=
  tensor_operand(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)code dimension /\ signed_range dimension.

Lemma tensor_positive_test entry code dimension : tensor_guard_operand entry code dimension ->
  expression_test(tensor_positive_expression code)entry(0 <? dimension).
Proof.
  intros [[TYPE [PURE EVAL]] RANGE]; exists(Val.of_bool(Int.lt Int.zero(Int.repr dimension))); split.
  - eapply eval_Ebinop; [apply rect_constant_evaluation|exact EVAL|].
    rewrite TYPE,rect_constant_type; reflexivity.
  - rewrite bool_of_bool; unfold Int.lt; rewrite Int.signed_zero,Int.signed_repr by exact RANGE.
    destruct(zlt 0 dimension); cbn; f_equal; symmetry; [apply Z.ltb_lt|apply Z.ltb_ge]; lia.
Qed.
Lemma tensor_prefix_test entry accumulated dimension accumulated_value dimension_value :
  tensor_operand(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)accumulated accumulated_value ->
  tensor_guard_operand entry dimension dimension_value ->
  1<=accumulated_value<=tensor_volume_cap -> 0<dimension_value ->
  expression_test(tensor_prefix_expression accumulated dimension)entry
    (accumulated_value <=? tensor_volume_cap/dimension_value).
Proof.
  intros [TYPE [PURE EVAL]] [[D_TYPE [D_PURE D_EVAL]] D_RANGE] A_RANGE POSITIVE.
  assert(QUOTIENT:eval_expr(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    (tensor_quotient_expression dimension)(Vint(Int.repr(tensor_volume_cap/dimension_value)))).
  { eapply eval_Ebinop; [apply rect_constant_evaluation|exact D_EVAL|].
    rewrite D_TYPE,rect_constant_type; apply signed_nonnegative_division;
      [pose proof tensor_volume_cap_range|unfold signed_range in D_RANGE]; lia. }
  assert(Q_RANGE:Int.min_signed<=tensor_volume_cap/dimension_value<=Int.max_signed).
  { pose proof tensor_volume_cap_range; pose proof Int.min_signed_neg;
    pose proof(Z.div_pos tensor_volume_cap dimension_value ltac:(lia) POSITIVE).
    pose proof(Z.div_le_upper_bound tensor_volume_cap dimension_value tensor_volume_cap POSITIVE ltac:(nia)); lia. }
  assert(A_SIGNED:Int.min_signed<=accumulated_value<=Int.max_signed) by
    (pose proof tensor_volume_cap_range; pose proof Int.min_signed_neg; lia).
  exists(Val.of_bool(negb(Int.lt(Int.repr(tensor_volume_cap/dimension_value))(Int.repr accumulated_value)))); split.
  - eapply eval_Ebinop; [exact EVAL|exact QUOTIENT|rewrite TYPE; reflexivity].
  - rewrite bool_of_bool; unfold Int.lt; rewrite !Int.signed_repr by assumption.
    destruct(zlt(tensor_volume_cap/dimension_value)accumulated_value); cbn; f_equal; symmetry;
      [apply Z.leb_gt|apply Z.leb_le]; lia.
Qed.

Lemma tensor_volume_guard_pure accumulated dimensions :
  pure_scalar accumulated -> Forall pure_scalar dimensions -> pure_tree(tensor_volume_guard_from accumulated dimensions).
Proof.
  intros A DS; revert accumulated A; induction DS as [|dimension rest D DS IH]; intros accumulated A; cbn.
  - constructor.
  - constructor; [unfold tensor_positive_expression; repeat constructor; exact D| |constructor].
    constructor; [unfold tensor_prefix_expression,tensor_quotient_expression; repeat constructor; assumption| |constructor].
    apply IH; unfold tensor_product; constructor; assumption.
Qed.

Theorem tensor_volume_guard_run entry codes dimensions accumulated value :
  Forall2(tensor_guard_operand entry)codes dimensions ->
  tensor_operand(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)accumulated value ->
  1<=value<=tensor_volume_cap ->
  decision_run entry(tensor_volume_guard_from accumulated codes)(tensor_volume_check tensor_volume_cap value dimensions).
Proof.
  intro WORDS; revert accumulated value; induction WORDS as [|code dimension codes dimensions D DS IH];
    intros accumulated value A RANGE; cbn [tensor_volume_guard_from tensor_volume_check]; [constructor|].
  eapply run_test; [apply tensor_positive_test; exact D|].
  destruct(0 <? dimension)eqn:POSITIVE; cbn; [|constructor].
  apply Z.ltb_lt in POSITIVE.
  eapply run_test; [apply tensor_prefix_test with(accumulated_value:=value)(dimension_value:=dimension); assumption|].
  destruct(value <=? tensor_volume_cap/dimension)eqn:BOUND; [|constructor].
  apply Z.leb_le in BOUND; apply tensor_quotient_bound in BOUND; [|exact POSITIVE].
  apply IH; [|nia].
  destruct A as [TYPE [PURE EVAL]],D as [[D_TYPE [D_PURE D_EVAL]] D_RANGE].
  split; [reflexivity|split; [unfold tensor_product; constructor; assumption|]].
  apply tensor_product_evaluation; assumption.
Qed.

Definition tensor_volume_guard_domain codes entry := exists dimensions,Forall2(tensor_guard_operand entry)codes dimensions.
Definition tensor_volume_guard_property codes entry := exists dimensions,
  Forall2(tensor_guard_operand entry)codes dimensions /\ tensor_layout_flag dimensions=true.

Definition tensor_volume_guard_condition fe O(observe:fragment_observation->O->Prop)codes :
  readonly_condition(readonly_clight_host fe observe)(tensor_volume_guard_domain codes)
    (tensor_volume_guard_property codes)(tensor_volume_guard codes).
Proof.
  assert(PURE:forall entry dimensions,Forall2(tensor_guard_operand entry)codes dimensions -> pure_tree(tensor_volume_guard codes)).
  { intros entry dimensions DS; apply tensor_volume_guard_pure; [constructor|].
    apply tensor_operands_pure with(ge:=entry_ge entry)(locals:=entry_env entry)
      (temps:=entry_temps entry)(memory:=entry_memory entry)(values:=dimensions).
    eapply Forall2_impl; [|exact DS]; intros code dimension WORD; exact(proj1 WORD). }
  assert(RUN:forall entry dimensions,Forall2(tensor_guard_operand entry)codes dimensions ->
    decision_run entry(tensor_volume_guard codes)(tensor_volume_check tensor_volume_cap 1 dimensions)).
  { intros entry dimensions DS; apply tensor_volume_guard_run; [exact DS| |pose proof tensor_volume_cap_range; lia].
    split; [reflexivity|split; [constructor|apply rect_constant_evaluation]]. }
  constructor.
  - intros entry [dimensions DS]; eapply pure_decision_run_safe;
      [exact(PURE entry dimensions DS)|exact(RUN entry dimensions DS)].
  - intros entry [dimensions DS]; exists(tensor_volume_check tensor_volume_cap 1 dimensions),entry;
      split; [exact(RUN entry dimensions DS)|reflexivity].
  - intros entry accepted checked [dimensions DS] [CHECK SAME]; split; [exact SAME|].
    intro ACCEPT; subst accepted.
    pose proof(@pure_tree_determinate(tensor_volume_guard codes)(PURE entry dimensions DS)entry true
      (tensor_volume_check tensor_volume_cap 1 dimensions)CHECK(RUN entry dimensions DS))as MATCH.
    exists dimensions; split; [exact DS|apply tensor_volume_check_layout; symmetry; exact MATCH].
Defined.

Theorem tensor_volume_guard_refuses_first entry first rest dimension :
  tensor_guard_operand entry first dimension -> dimension<=0 ->
  decision_run entry(tensor_volume_guard(first::rest))false.
Proof.
  intros WORD NONPOSITIVE; unfold tensor_volume_guard; cbn [tensor_volume_guard_from].
  eapply run_test with(b:=false); [|constructor].
  pose proof(@tensor_positive_test entry first dimension WORD)as TEST.
  assert(NO:(0 <? dimension)=false)by(apply Z.ltb_ge; exact NONPOSITIVE).
  rewrite NO in TEST; exact TEST.
Qed.
Theorem tensor_volume_guard_refuses_first_safe entry first rest dimension :
  tensor_guard_operand entry first dimension -> dimension<=0 -> Forall pure_scalar rest ->
  readonly_tree_safe entry(tensor_volume_guard(first::rest)).
Proof.
  intros WORD NONPOSITIVE PURE; eapply pure_decision_run_safe.
  - apply tensor_volume_guard_pure; [constructor|constructor; [exact(proj1(proj2(proj1 WORD)))|exact PURE]].
  - apply tensor_volume_guard_refuses_first with(dimension:=dimension); assumption.
Qed.

Print Assumptions tensor_volume_cap_range.
Print Assumptions tensor_volume_check_spec.
Print Assumptions tensor_volume_check_layout.
Print Assumptions tensor_positive_test.
Print Assumptions tensor_prefix_test.
Print Assumptions tensor_volume_guard_run.
Print Assumptions tensor_volume_guard_condition.
Print Assumptions tensor_volume_guard_refuses_first.
Print Assumptions tensor_volume_guard_refuses_first_safe.
