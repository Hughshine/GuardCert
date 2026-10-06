From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop ClightTempFrame
  ClightLoopSyntax ClightRegionProgress CompCertMemoryActions.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyBranching ReadonlyPrefixScan
  ClightReadonlyRewrite ClightConditionComposition ClightReadonlyBranching
  ClightReadonlyLoadedTreeSynthesis ClightIndexedAliasGuard ClightLoadedRowPrefix
  ClightStorePermissions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section SCAN.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Variables row cache parameter : ident.
Variable outer_body : statement.
Variable stable : list ident.
Variable ready : clight_entry -> Prop.
Variable upper : clight_entry -> Z -> Z.
Variable point : clight_entry -> Z -> Z -> mem -> mem -> Prop.
Hypotheses (PARAMETER : In parameter stable) (FRESH_ROW : ~ In row stable).
Hypotheses (NORMAL : normal_statement outer_body = true) (QUIET : quiet_statement outer_body = true).
Let count entry := Int.signed (temp_word cache (entry_temps entry)).
Let invariant := @loaded_row_prefix fe row cache parameter outer_body stable ready.
Hypothesis DECODE : forall entry i current memory after final,
  ready entry -> 0 <= i < count entry -> current ! row = Some (Vint (Int.repr i)) ->
  temp_agree stable (entry_temps entry) current ->
  exec_stmt fe (entry_ge entry) (entry_env entry) current memory outer_body E0 after final Out_normal ->
  counted_iterations (point entry i) (Z.to_nat (upper entry i)) 0 memory final /\
    after ! row = current ! row /\ temp_agree stable current after.
Hypothesis WIDTH : forall entry i, ready entry -> 0 <= i < count entry -> 0 <= upper entry i.
Hypothesis PERMISSIONS : forall entry i j before after,
  point entry i j before after -> memory_accesses_back before after.

(** The array instance certifies its executable row probe. Its accepted
    property must preserve the observed bound for decoded physical points.
    This is a proof parameter, not an unchecked property in the compiler. *)
Variable row_probe : Z -> decision_tree.
Variable row_property : Z -> clight_entry -> Prop.
Hypothesis ROW_CHECK : forall i, readonly_condition (readonly_clight_host fe observe)
  (fun entry => invariant i entry /\ i < count entry) (row_property i) (row_probe i).
Hypothesis PRESERVE : forall i entry, invariant i entry -> i < count entry -> row_property i entry ->
  forall block offset, (entry_temps entry) ! parameter = Some (Vptr block offset) ->
  forall j before after, 0 <= j < upper entry i -> point entry i j before after ->
    location_load (MemoryLocation Mint32 block (Ptrofs.unsigned offset)) after =
    location_load (MemoryLocation Mint32 block (Ptrofs.unsigned offset)) before.

Definition loaded_rows_active_probe i :=
  Test (indexed_active_expr cache i) (Decision true) (Decision false).

Lemma loaded_rows_activity i : readonly_classifier (readonly_clight_host fe observe)
  (invariant i) (fun entry => i < count entry) (fun entry => ~ i < count entry)
  (loaded_rows_active_probe i).
Proof.
  assert (DEFINED : forall entry, invariant i entry ->
    expression_test (indexed_active_expr cache i) entry (indexed_active_flag cache i entry)).
  { intros entry [READY [CACHE [RANGE SOURCE]]]; apply indexed_active_test; [|exact CACHE].
    pose proof (Int.signed_range (temp_word cache (entry_temps entry))); unfold count in RANGE;
      unfold signed_range; change Int.min_signed with (-2147483648) in *; lia. }
  apply readonly_expression_classifier.
  - intros entry INV; eexists; apply DEFINED; exact INV.
  - intros entry INV TEST; pose proof (readonly_test_determinate (DEFINED entry INV) TEST) as VALUE.
    unfold indexed_active_flag in VALUE; apply Z.ltb_lt in VALUE; exact VALUE.
  - intros entry INV TEST; pose proof (readonly_test_determinate (DEFINED entry INV) TEST) as VALUE.
    unfold indexed_active_flag in VALUE; apply Z.ltb_ge in VALUE; unfold count; lia.
Defined.

Lemma loaded_rows_point i : readonly_condition (readonly_clight_host fe observe)
  (fun entry => invariant i entry /\ i < count entry)
  (fun entry => row_property i entry /\ invariant (i+1) entry) (row_probe i).
Proof.
  eapply readonly_condition_entails; [apply ROW_CHECK|].
  intros entry [INV ACTIVE] PROPERTY; split; [exact PROPERTY|].
  eapply (@loaded_row_prefix_advance fe row cache parameter outer_body stable ready upper point
    PARAMETER FRESH_ROW NORMAL QUIET DECODE WIDTH PERMISSIONS); [exact INV|exact ACTIVE|].
  apply PRESERVE; assumption.
Defined.

Definition loaded_rows_prefix_spec : readonly_prefix_spec (readonly_clight_host fe observe) Z :=
  @ReadonlyPrefixSpec clight_entry (readonly_clight_host fe observe) Z (fun i => i+1)
    loaded_rows_active_probe row_probe invariant (fun i entry => i < count entry) row_property
    loaded_rows_activity loaded_rows_point.

Definition loaded_rows_scan_condition fuel start :=
  @synthesized_prefix_scan_condition clight_entry (readonly_clight_host fe observe) Z
    (clight_readonly_check_algebra fe observe) (clight_readonly_branch_algebra fe observe)
    loaded_rows_prefix_spec fuel start.

(** Coverage is separate from safety. The caller must establish enough fuel
    to cover the accepted count; exhaustion alone does not imply stability. *)
Theorem loaded_rows_scan_sound fuel start entry :
  prefix_scan_property loaded_rows_prefix_spec fuel start entry ->
  forall i, start <= i < start + Z.of_nat fuel -> i < count entry -> row_property i entry.
Proof.
  revert start; induction fuel as [|fuel IH]; intros start PROP i RANGE ACTIVE;
    cbn [prefix_scan_property loaded_rows_prefix_spec prefix_active prefix_next prefix_point_property] in PROP;
    [cbn in RANGE; lia|].
  destruct (PROP ltac:(lia)) as [PROPERTY REST].
  destruct (Z.eq_dec i start); [subst; exact PROPERTY|].
  eapply IH; [exact REST|rewrite Nat2Z.inj_succ in RANGE; lia|exact ACTIVE].
Qed.
End SCAN.

Print Assumptions loaded_rows_activity.
Print Assumptions loaded_rows_point.
Print Assumptions loaded_rows_scan_condition.
Print Assumptions loaded_rows_scan_sound.
