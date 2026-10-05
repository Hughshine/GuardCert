From Stdlib Require Import Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightGuard ClightCondition ClightPureExpr ClightNoWrap ClightRedundantSet ClightCountedLoop
  ClightRectangularStore ClightRectangularGuard.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyConditionComposition ReadonlyBranching
  ReadonlyPrefixScan ClightReadonlyRewrite ClightConditionComposition ClightReadonlyBranching ClightReadonlyLoadedTreeSynthesis
  ClightReadonlyCellSwap ClightIndexedAliasGuard ClightLoadedRectangleMemory ClightLoadedRectangleAtoms.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A complete current row is justified by its real source execution, even
    if stores in that row change the outer bound. Future rows are not assumed
    accessible. All inner probes still read the original entry memory. *)
Definition loaded_rectangle_inner_invariant d array bound columns i point entry :=
  0 <= point <= rectangle_stride d /\ 0 <= i < rectangle_outer_limit d /\
  exists m block q qofs word,
    0 < m <= rectangle_stride d /\ (entry_temps entry) ! columns = Some (Vint (Int.repr m)) /\
    rect_array_binding d (entry_ge entry) (entry_env entry) array block /\
    (entry_temps entry) ! bound = Some (Vptr q qofs) /\
    Mem.loadv Mint32 (entry_memory entry) (Vptr q qofs) = Some word /\
    forall j, 0 <= j < m -> writable_word (entry_memory entry) block (loaded_rectangle_offset d i j).
Definition loaded_rectangle_inner_active columns point entry := point < Int.signed (temp_word columns (entry_temps entry)).
Definition loaded_rectangle_inner_active_probe columns point :=
  Test (indexed_active_expr columns point) (Decision true) (Decision false).
Definition loaded_rectangle_inner_point_probe d array bound i point :=
  Test (loaded_rectangle_alias_expr d array bound i point) (Decision false) (Decision true).

Lemma loaded_rectangle_inner_activity d (VALID : rectangle_layout_valid d) fe O
  (observe : fragment_observation -> O -> Prop) array bound columns i point :
  readonly_classifier (readonly_clight_host fe observe) (loaded_rectangle_inner_invariant d array bound columns i point)
    (loaded_rectangle_inner_active columns point) (fun entry => ~ loaded_rectangle_inner_active columns point entry)
    (loaded_rectangle_inner_active_probe columns point).
Proof.
  unfold loaded_rectangle_inner_active_probe; apply readonly_expression_classifier.
  - intros entry [RANGE [IR [m [block [q [qofs [word [MR [COLS REST]]]]]]]]].
    exists (indexed_active_flag columns point entry); apply indexed_active_test;
      [pose proof (rectangle_limits VALID); unfold signed_range in *; change Int.min_signed with (-2147483648) in *; lia|exists (Int.repr m); exact COLS].
  - intros entry [RANGE [IR [m [block [q [qofs [word [MR [COLS REST]]]]]]]]] TEST.
    assert (FLAG : indexed_active_flag columns point entry = true).
    { eapply readonly_test_determinate; [apply indexed_active_test;
        [pose proof (rectangle_limits VALID); unfold signed_range in *; change Int.min_signed with (-2147483648) in *; lia|exists (Int.repr m); exact COLS]|exact TEST]. }
    unfold loaded_rectangle_inner_active, indexed_active_flag in *; apply Z.ltb_lt; exact FLAG.
  - intros entry [RANGE [IR [m [block [q [qofs [word [MR [COLS REST]]]]]]]]] TEST.
    assert (FLAG : indexed_active_flag columns point entry = false).
    { eapply readonly_test_determinate; [apply indexed_active_test;
        [pose proof (rectangle_limits VALID); unfold signed_range in *; change Int.min_signed with (-2147483648) in *; lia|exists (Int.repr m); exact COLS]|exact TEST]. }
    unfold loaded_rectangle_inner_active, indexed_active_flag in *; apply Z.ltb_ge in FLAG; lia.
Defined.

Lemma loaded_rectangle_inner_point d (VALID : rectangle_layout_valid d) fe O
  (observe : fragment_observation -> O -> Prop) array bound columns i point :
  readonly_condition (readonly_clight_host fe observe)
    (fun entry => loaded_rectangle_inner_invariant d array bound columns i point entry /\ loaded_rectangle_inner_active columns point entry)
    (fun entry => loaded_rectangle_alias_flag d array bound i point entry = false /\
      loaded_rectangle_inner_invariant d array bound columns i (point+1) entry)
    (loaded_rectangle_inner_point_probe d array bound i point).
Proof.
  assert (READY : forall entry,
    loaded_rectangle_inner_invariant d array bound columns i point entry -> loaded_rectangle_inner_active columns point entry ->
    expression_test (loaded_rectangle_alias_expr d array bound i point) entry (loaded_rectangle_alias_flag d array bound i point entry)).
  { intros entry [RANGE [IR [m [block [q [qofs [word [MR [COLS [ARRAY [BOUND [READ WORDS]]]]]]]]]]]] ACTIVE.
    unfold loaded_rectangle_inner_active, temp_word in ACTIVE; rewrite COLS in ACTIVE;
      rewrite Int.signed_repr in ACTIVE by (pose proof (rectangle_limits VALID); unfold signed_range in *; change Int.min_signed with (-2147483648) in *; lia).
    eapply loaded_rectangle_alias_test; [exact VALID| |exact ARRAY|exact BOUND|exact READ|apply WORDS; lia].
    apply rectangle_point_bound with (N := rectangle_outer_limit d) (M := m); try assumption;
      pose proof (rectangle_limits VALID); lia. }
  constructor.
  - intros entry [INV ACTIVE]; cbn [loaded_rectangle_inner_point_probe readonly_tree_safe].
    split; [eexists; apply READY; eassumption|intros answer RUN; destruct answer; exact I].
  - intros entry [INV ACTIVE]; exists (negb (loaded_rectangle_alias_flag d array bound i point entry)), entry; split; [|reflexivity].
    unfold loaded_rectangle_inner_point_probe; eapply run_test; [apply READY; eassumption|].
    destruct (loaded_rectangle_alias_flag d array bound i point entry); constructor.
  - intros entry answer checked [INV ACTIVE] [RUN SAME]; split; [exact SAME|intro ACCEPT; subst answer].
    assert (APART : loaded_rectangle_alias_flag d array bound i point entry = false).
    { unfold loaded_rectangle_inner_point_probe in RUN; inversion RUN; subst.
      match goal with LEAF : decision_run _ (if ?choice then Decision false else Decision true) true |- _ =>
        destruct choice; inversion LEAF; subst end.
      eapply readonly_test_determinate; [apply READY; eassumption|eassumption]. }
    split; [exact APART|].
    destruct INV as [RANGE [IR [m [block [q [qofs [word [MR [COLS REST]]]]]]]]].
    unfold loaded_rectangle_inner_active, temp_word in ACTIVE; rewrite COLS in ACTIVE;
      rewrite Int.signed_repr in ACTIVE by (pose proof (rectangle_limits VALID); unfold signed_range in *; change Int.min_signed with (-2147483648) in *; lia).
    split; [lia|split; [exact IR|exists m, block, q, qofs, word; split; [exact MR|split; assumption]]].
Defined.

Definition loaded_rectangle_inner_spec d (VALID : rectangle_layout_valid d) fe O
  (observe : fragment_observation -> O -> Prop) array bound columns i : readonly_prefix_spec (readonly_clight_host fe observe) Z :=
  @ReadonlyPrefixSpec clight_entry (readonly_clight_host fe observe) Z (fun point => point+1)
    (loaded_rectangle_inner_active_probe columns) (loaded_rectangle_inner_point_probe d array bound i)
    (loaded_rectangle_inner_invariant d array bound columns i) (loaded_rectangle_inner_active columns)
    (fun point entry => loaded_rectangle_alias_flag d array bound i point entry = false)
    (@loaded_rectangle_inner_activity d VALID fe O observe array bound columns i)
    (@loaded_rectangle_inner_point d VALID fe O observe array bound columns i).

Definition loaded_rectangle_inner_tree d VALID fe O (observe : fragment_observation -> O -> Prop) array bound columns i :=
  synthesize_prefix_scan (clight_readonly_check_algebra fe observe) (clight_readonly_branch_algebra fe observe)
    (@loaded_rectangle_inner_spec d VALID fe O observe array bound columns i) (Z.to_nat (rectangle_stride d)) 0.

Lemma loaded_rectangle_inner_syntax d VALID fe O (observe : fragment_observation -> O -> Prop)
  array bound columns i fuel point :
  synthesize_prefix_scan (clight_readonly_check_algebra fe observe) (clight_readonly_branch_algebra fe observe)
    (@loaded_rectangle_inner_spec d VALID fe O observe array bound columns i) fuel point =
  synthesize_prefix_scan (clight_readonly_check_algebra (adapter_entry true) eq)
    (clight_readonly_branch_algebra (adapter_entry true) eq)
    (@loaded_rectangle_inner_spec d VALID (adapter_entry true) fragment_observation eq array bound columns i) fuel point.
Proof.
  revert point; induction fuel as [|fuel IH]; intro point; cbn [synthesize_prefix_scan
    loaded_rectangle_inner_spec prefix_next prefix_active_probe prefix_point_probe
    clight_readonly_check_algebra clight_readonly_branch_algebra constant_check branch_check].
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.

Lemma loaded_rectangle_inner_scan_sound d VALID fe O (observe : fragment_observation -> O -> Prop) array bound columns i fuel point entry :
  prefix_scan_property (@loaded_rectangle_inner_spec d VALID fe O observe array bound columns i) fuel point entry ->
  forall j, point <= j < point+Z.of_nat fuel -> j < Int.signed (temp_word columns (entry_temps entry)) ->
    loaded_rectangle_alias_flag d array bound i j entry = false.
Proof.
  revert point; induction fuel as [|fuel IH]; intros point PROP j RANGE ACTIVE;
    cbn [prefix_scan_property loaded_rectangle_inner_spec prefix_active prefix_next prefix_point_property] in PROP;
    [cbn in RANGE; lia|].
  destruct (PROP ltac:(unfold loaded_rectangle_inner_active; lia)) as [APART NEXT].
  destruct (Z.eq_dec j point); [subst; exact APART|].
  eapply IH; [exact NEXT|rewrite Nat2Z.inj_succ in RANGE; lia|exact ACTIVE].
Qed.

Print Assumptions loaded_rectangle_inner_activity.
Print Assumptions loaded_rectangle_inner_point.
Print Assumptions loaded_rectangle_inner_scan_sound.
