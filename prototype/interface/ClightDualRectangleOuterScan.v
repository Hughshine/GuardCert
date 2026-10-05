From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightNoWrap ClightCountedLoop ClightCountedProtocol ClightStraightLine
  ClightRectangularStore ClightRectangularGuard ClightRectangularLoops ClightRectangularRegion CompCertStoreSchedule.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyConditionComposition ReadonlyBranching ReadonlyPrefixScan
  ClightReadonlyRewrite ClightConditionComposition ClightReadonlyBranching ClightReadonlyLoadedTreeSynthesis
  ClightLoadedBoundSyntax ClightLoadedRectangleAtoms ClightDualRectanglePrefix ClightDualRectangleCursor ClightDualRectangleInnerScan.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section OUTER.
Variable d : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid d.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variables array row rows column columns : ident.
Variables body outer : statement.
Hypotheses (RC : row <> column) (RN : row <> rows) (RM : row <> columns)
  (CN : column <> rows) (CM : column <> columns).
Hypotheses (BODY : flatten_region body = [rect_store d array row column])
  (OUTER : flatten_region outer = [rectangle_reset column; loaded_bound_loop column columns body]).

Definition dual_rect_inner_tree O (observe : fragment_observation -> O -> Prop) i :=
  synthesize_prefix_scan (clight_readonly_check_algebra fe observe) (clight_readonly_branch_algebra fe observe)
    (@dual_rect_inner_spec d VALID fe array row rows column columns body outer RC RN RM CN CM BODY O observe i)
    (Z.to_nat (rectangle_stride d)) 0.
Definition dual_rect_row_property i entry := forall j,
  0 <= j < Int.signed (loaded_rectangle_word columns entry) ->
  loaded_rectangle_alias_flag d array rows i j entry = false /\
  loaded_rectangle_alias_flag d array columns i j entry = false.

Lemma dual_rect_open_inner i entry :
  dual_rect_outer_invariant fe d row rows columns outer i entry -> dual_rect_active rows i entry ->
  dual_rect_inner_invariant fe d row rows column columns body outer i 0 entry.
Proof.
  intros [IR [cursor]] ACTIVE; set (state := dro_state cursor).
  destruct (@dual_rect_open_row fe (entry_ge entry) (entry_env entry) (drs_temps state) (drs_memory state)
    d array row rows column columns body outer i (loaded_rectangle_word rows entry) (drs_q state) (drs_qofs state)
    (dro_after cursor) (dro_final cursor) BODY OUTER ltac:(unfold dual_rect_active in ACTIVE; lia)
    (drs_iterator state) (drs_rows state) (drs_rows_read state) (dro_tail cursor))
    as [exit [exit_memory [next [next_memory [INNER [INC TAIL]]]]]].
  split; [unfold dual_rect_active in ACTIVE; lia|split; [pose proof VALID as LAYOUT; unfold rectangle_layout_valid in LAYOUT; lia|constructor]].
  refine {| dri_state := @dual_rect_state_set d row rows columns i entry state column (Vint Int.zero)
      ltac:(congruence) CN CM; dri_iterator := PTree.gss _ _ _;
    dri_exit := exit; dri_exit_memory := exit_memory; dri_next := next; dri_next_memory := next_memory;
    dri_after := dro_after cursor; dri_final := dro_final cursor;
    dri_inner := INNER; dri_increment := INC; dri_tail := TAIL |}.
Qed.

Lemma dual_rect_inner_scan_sound O (observe : fragment_observation -> O -> Prop) i fuel point entry :
  prefix_scan_property (@dual_rect_inner_spec d VALID fe array row rows column columns body outer RC RN RM CN CM BODY O observe i)
    fuel point entry ->
  forall j, point <= j < point+Z.of_nat fuel -> j < Int.signed (loaded_rectangle_word columns entry) ->
    dual_rect_point_property fe d array row rows columns outer i j entry.
Proof.
  revert point; induction fuel as [|fuel IH]; intros point PROP j RANGE ACTIVE;
    cbn [prefix_scan_property dual_rect_inner_spec prefix_active prefix_next prefix_point_property] in PROP;
    [cbn in RANGE; lia|].
  destruct (PROP ltac:(unfold dual_rect_active; lia)) as [POINT NEXT].
  destruct (Z.eq_dec j point); [subst; exact POINT|].
  eapply IH; [exact NEXT|rewrite Nat2Z.inj_succ in RANGE; lia|exact ACTIVE].
Qed.

Definition dual_rect_outer_point O (observe : fragment_observation -> O -> Prop) i :
  readonly_condition (readonly_clight_host fe observe)
    (fun entry => dual_rect_outer_invariant fe d row rows columns outer i entry /\ dual_rect_active rows i entry)
    (fun entry => dual_rect_row_property i entry /\ dual_rect_outer_invariant fe d row rows columns outer (i+1) entry)
    (dual_rect_inner_tree observe i).
Proof.
  eapply readonly_condition_entails.
  - eapply readonly_condition_restrict.
    + exact (@synthesized_prefix_scan_condition clight_entry (readonly_clight_host fe observe) Z
        (clight_readonly_check_algebra fe observe) (clight_readonly_branch_algebra fe observe)
        (@dual_rect_inner_spec d VALID fe array row rows column columns body outer RC RN RM CN CM BODY O observe i)
        (Z.to_nat (rectangle_stride d)) 0).
    + intros entry [INV ACTIVE]; apply dual_rect_open_inner; assumption.
  - intros entry [INV ACTIVE] SCAN.
    destruct INV as [IR [cursor]]; pose proof (drs_columns_range (dro_state cursor)) as MR.
    assert (ALL : forall j, 0 <= j < Int.signed (loaded_rectangle_word columns entry) ->
      dual_rect_point_property fe d array row rows columns outer i j entry).
    { intros j JR; eapply dual_rect_inner_scan_sound; [exact SCAN| |lia].
      rewrite Z2Nat.id by (pose proof (rectangle_limits VALID); lia); lia. }
    split.
    + intros j JR; destruct (ALL j JR) as [AQ [AM LAST]]; auto.
    + destruct (ALL (Int.signed (loaded_rectangle_word columns entry)-1) ltac:(lia)) as [AQ [AM LAST]].
      apply LAST; lia.
Defined.

Definition dual_rect_outer_spec O (observe : fragment_observation -> O -> Prop) : readonly_prefix_spec (readonly_clight_host fe observe) Z.
Proof.
  refine (@ReadonlyPrefixSpec clight_entry (readonly_clight_host fe observe) Z (fun i => i+1)
    (dual_rect_active_probe rows) (dual_rect_inner_tree observe)
    (dual_rect_outer_invariant fe d row rows columns outer) (dual_rect_active rows)
    dual_rect_row_property _ (dual_rect_outer_point observe)).
  intro i; apply dual_rect_activity.
  - intros entry [IR REST]; pose proof (rectangle_limits VALID); unfold signed_range in *;
      change Int.min_signed with (-2147483648) in *; lia.
  - intros entry [IR [cursor]]; exists (loaded_rectangle_word rows entry),
      (drs_q (dro_state cursor)), (drs_qofs (dro_state cursor)); split;
      apply drs_entry_rows || apply drs_entry_rows_read.
Defined.
Definition dual_rect_outer_tree O (observe : fragment_observation -> O -> Prop) :=
  synthesize_prefix_scan (clight_readonly_check_algebra fe observe) (clight_readonly_branch_algebra fe observe)
    (dual_rect_outer_spec observe) (Z.to_nat (rectangle_outer_limit d)) 0.

Lemma dual_rect_outer_scan_sound O (observe : fragment_observation -> O -> Prop) fuel point entry :
  prefix_scan_property (dual_rect_outer_spec observe) fuel point entry ->
  forall i, point <= i < point+Z.of_nat fuel -> i < Int.signed (loaded_rectangle_word rows entry) ->
    dual_rect_row_property i entry.
Proof.
  revert point; induction fuel as [|fuel IH]; intros point PROP i RANGE ACTIVE;
    cbn [prefix_scan_property dual_rect_outer_spec prefix_active prefix_next prefix_point_property] in PROP;
    [cbn in RANGE; lia|].
  destruct (PROP ltac:(unfold dual_rect_active; lia)) as [ROW NEXT].
  destruct (Z.eq_dec i point); [subst; exact ROW|].
  eapply IH; [exact NEXT|rewrite Nat2Z.inj_succ in RANGE; lia|exact ACTIVE].
Qed.
End OUTER.

Print Assumptions dual_rect_open_inner.
Print Assumptions dual_rect_inner_scan_sound.
Print Assumptions dual_rect_outer_point.
Print Assumptions dual_rect_outer_scan_sound.
