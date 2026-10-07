From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightRedundantSet ClightNoWrap ClightLoopSyntax
  ClightRegionProgress ClightLoopExecution CompCertMemoryActions.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyBranching ReadonlyPrefixScan
  ClightReadonlyRewrite ClightConditionComposition ClightReadonlyBranching ClightReadonlyLoadedTreeSynthesis
  ClightIndexedAliasGuard ClightStrictIteration ClightStrictLoopProgress ClightSignedExpressionProgress
  ClightExpressionHeaderCapture ClightObservedHeaderPrefix ClightStorePermissions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A source-prefix service independent of body depth and bound expression
    shape. Each accepted body check licenses the next actual source body.
    Observed raw values and the computed cached upper word remain distinct. *)
Section PREFIX.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variables row cache : ident.
Variable bound : expr.
Variable body : statement.
Variables stable written : list ident.
Variable ready : clight_entry -> Prop.
Variable observations : clight_entry -> list (memory_location * val).
Hypothesis TYPE : typeof bound=type_int32s.
Hypothesis ROW_FRESH : ~In row stable.
Hypotheses (NORMAL : normal_statement body=true) (QUIET : quiet_statement body=true).
Hypothesis WRITES : writes_only written body.
Hypothesis ROW_UNWRITTEN : ~In row written.
Hypothesis STABLE_UNWRITTEN : forall id, In id stable -> ~In id written.
Hypothesis PERMISSIONS : forall ge locals current memory after final,
  exec_stmt fe ge locals current memory body E0 after final Out_normal -> memory_accesses_back memory final.
Let count entry := Int.signed(temp_word cache (entry_temps entry)).
Hypothesis HEADER : forall entry i current memory,
  ready entry -> 0<=i<=count entry -> current!row=Some(Vint(Int.repr i)) ->
  temp_agree stable (entry_temps entry) current -> header_observations_match (observations entry) memory ->
  eval_expr (entry_ge entry) (entry_env entry) current memory bound (Vint(temp_word cache (entry_temps entry))).

Definition expression_body_preserved i entry := forall current memory after final,
  current!row=Some(Vint(Int.repr i)) -> temp_agree stable (entry_temps entry) current ->
  header_observations_match (observations entry) memory ->
  exec_stmt fe (entry_ge entry) (entry_env entry) current memory body E0 after final Out_normal ->
  header_observations_match (observations entry) final.

Definition expression_body_prefix i entry :=
  ready entry /\ register_domain cache entry /\ 0<=i<=count entry /\
  header_observations_match (observations entry) (entry_memory entry) /\
  exists current memory after final,
    current!row=Some(Vint(Int.repr i)) /\ temp_agree stable (entry_temps entry) current /\
    header_observations_match (observations entry) memory /\
    memory_accesses_back (entry_memory entry) memory /\
    exec_stmt fe (entry_ge entry) (entry_env entry) current memory
      (strict_frontend_loop row (signed_expression_test row bound) body) E0 after final Out_normal.

Lemma expression_body_prefix_initial entry after final :
  ready entry -> register_domain cache entry -> 0<=count entry ->
  (entry_temps entry)!row=Some(Vint Int.zero) ->
  header_observations_match (observations entry) (entry_memory entry) ->
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (strict_frontend_loop row (signed_expression_test row bound) body) E0 after final Out_normal ->
  expression_body_prefix 0 entry.
Proof.
  intros READY CACHE COUNT ROW OBSERVED SOURCE.
  split; [exact READY|split; [exact CACHE|split; [lia|split; [exact OBSERVED|]]]].
  exists (entry_temps entry),(entry_memory entry),after,final.
  split; [exact ROW|split; [apply temp_agree_refl|split; [exact OBSERVED|split; [apply memory_accesses_back_refl|exact SOURCE]]]].
Qed.

Lemma expression_body_active_test i entry current memory :
  ready entry -> 0<=i<count entry -> current!row=Some(Vint(Int.repr i)) ->
  temp_agree stable (entry_temps entry) current -> header_observations_match (observations entry) memory ->
  expression_test (signed_expression_test row bound) (Entry (entry_ge entry) (entry_env entry) current memory) true.
Proof.
  intros READY RANGE ROW FRAME OBSERVED.
  assert (FLAG : Int.lt (Int.repr i) (temp_word cache (entry_temps entry))=true).
  { unfold Int.lt; rewrite Int.signed_repr by
      (pose proof (Int.signed_range (temp_word cache (entry_temps entry))); unfold count in RANGE;
       unfold signed_range; change Int.min_signed with (-2147483648) in *; lia).
    unfold count in RANGE; destruct (zlt i (Int.signed(temp_word cache (entry_temps entry)))); [reflexivity|lia]. }
  rewrite <-FLAG; eapply signed_expression_test_eval; [exact TYPE|exact ROW|eapply HEADER; eauto; lia].
Qed.

Theorem expression_body_prefix_receipt i entry :
  expression_body_prefix i entry -> i<count entry -> exists current memory after final,
    current!row=Some(Vint(Int.repr i)) /\ temp_agree stable (entry_temps entry) current /\
    header_observations_match (observations entry) memory /\ memory_accesses_back (entry_memory entry) memory /\
    exec_stmt fe (entry_ge entry) (entry_env entry) current memory body E0 after final Out_normal.
Proof.
  intros [READY [CACHE [RANGE [INITIAL [current [memory [after [final [ROW [FRAME [OBSERVED [BACK SOURCE]]]]]]]]]]]] ACTIVE.
  pose proof (@expression_body_active_test i entry current memory READY ltac:(lia) ROW FRAME OBSERVED) as TEST.
  destruct (@strict_active_iteration fe (entry_ge entry) (entry_env entry) row (signed_expression_test row bound) body
    current memory after final NORMAL QUIET TEST SOURCE)
    as [body_temps [body_memory [next_temps [next_memory [BODY REST]]]]].
  exists current,memory,body_temps,body_memory.
  split; [exact ROW|split; [exact FRAME|split; [exact OBSERVED|split; [exact BACK|exact BODY]]]].
Qed.

Theorem expression_body_prefix_advance i entry :
  expression_body_prefix i entry -> i<count entry -> expression_body_preserved i entry ->
  expression_body_prefix (i+1) entry.
Proof.
  intros [READY [CACHE [RANGE [INITIAL [current [memory [after [final [ROW [FRAME [OBSERVED [BACK SOURCE]]]]]]]]]]]] ACTIVE PRESERVE.
  pose proof (@expression_body_active_test i entry current memory READY ltac:(lia) ROW FRAME OBSERVED) as TEST.
  destruct (@strict_active_iteration fe (entry_ge entry) (entry_env entry) row (signed_expression_test row bound) body
    current memory after final NORMAL QUIET TEST SOURCE)
    as [body_temps [body_memory [next_temps [next_memory [BODY [INC TAIL]]]]]].
  pose proof (@PRESERVE current memory body_temps body_memory ROW FRAME OBSERVED BODY) as BODY_OBSERVED.
  assert (BODY_ROW : body_temps!row=Some(Vint(Int.repr i))).
  { rewrite (@writes_only_frame _ _ _ _ _ _ _ _ _ _ BODY written WRITES row ROW_UNWRITTEN); exact ROW. }
  assert (BODY_FRAME : temp_agree stable current body_temps) by (eapply structured_temp_frame; eassumption).
  assert (STRICT : strict_counter_active row body_temps).
  { exists (Int.repr i); split; [exact BODY_ROW|rewrite Int.signed_repr;
      pose proof (Int.signed_range (temp_word cache (entry_temps entry))); unfold count in ACTIVE,RANGE;
      change Int.min_signed with (-2147483648) in *; lia]. }
  destruct (@strict_increment_execution_exact fe (entry_ge entry) (entry_env entry) row body_temps body_memory
    E0 next_temps next_memory Out_normal STRICT INC) as [_ [NEXT [MEMORY _]]].
  subst next_temps next_memory; rewrite (@counter_increment_small row body_temps i BODY_ROW) in TAIL.
  split; [exact READY|split; [exact CACHE|split; [lia|split; [exact INITIAL|]]]].
  exists (PTree.set row (Vint(Int.repr(i+1))) body_temps),body_memory,after,final.
  split; [apply PTree.gss|split; [|split; [exact BODY_OBSERVED|split; [|exact TAIL]]]].
  - intros id MEMBER; rewrite PTree.gso by (intro SAME; subst id; contradiction).
    rewrite BODY_FRAME by exact MEMBER; exact (FRAME id MEMBER).
  - eapply memory_accesses_back_trans; [exact BACK|eapply PERMISSIONS; exact BODY].
Qed.

Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Variable body_probe : Z -> decision_tree.
Hypothesis BODY_CHECK : forall i, readonly_condition (readonly_clight_host fe observe)
  (fun entry => expression_body_prefix i entry /\ i<count entry) (expression_body_preserved i) (body_probe i).

Definition expression_body_active_probe i := Test (indexed_active_expr cache i) (Decision true) (Decision false).
Lemma expression_body_activity i : readonly_classifier (readonly_clight_host fe observe)
  (expression_body_prefix i) (fun entry=>i<count entry) (fun entry=>~i<count entry) (expression_body_active_probe i).
Proof.
  assert (DEFINED : forall entry, expression_body_prefix i entry ->
    expression_test (indexed_active_expr cache i) entry (indexed_active_flag cache i entry)).
  { intros entry [READY [CACHE [RANGE REST]]]; apply indexed_active_test; [|exact CACHE].
    pose proof (Int.signed_range (temp_word cache (entry_temps entry))); unfold count in RANGE;
      unfold signed_range; change Int.min_signed with (-2147483648) in *; lia. }
  apply readonly_expression_classifier.
  - intros entry INV; eexists; apply DEFINED; exact INV.
  - intros entry INV TEST; pose proof (readonly_test_determinate (DEFINED entry INV) TEST) as FLAG.
    unfold indexed_active_flag in FLAG; apply Z.ltb_lt in FLAG; exact FLAG.
  - intros entry INV TEST; pose proof (readonly_test_determinate (DEFINED entry INV) TEST) as FLAG.
    unfold indexed_active_flag in FLAG; apply Z.ltb_ge in FLAG; unfold count; lia.
Defined.

Lemma expression_body_point i : readonly_condition (readonly_clight_host fe observe)
  (fun entry=>expression_body_prefix i entry /\ i<count entry)
  (fun entry=>expression_body_preserved i entry /\ expression_body_prefix (i+1) entry) (body_probe i).
Proof.
  eapply readonly_condition_entails; [apply BODY_CHECK|].
  intros entry [INV ACTIVE] PROPERTY; split; [exact PROPERTY|].
  eapply expression_body_prefix_advance; eassumption.
Defined.

Definition expression_body_prefix_spec : readonly_prefix_spec (readonly_clight_host fe observe) Z :=
  @ReadonlyPrefixSpec clight_entry (readonly_clight_host fe observe) Z (fun i=>i+1)
    expression_body_active_probe body_probe expression_body_prefix (fun i entry=>i<count entry)
    expression_body_preserved expression_body_activity expression_body_point.
Definition expression_body_scan_condition fuel start :=
  @synthesized_prefix_scan_condition clight_entry (readonly_clight_host fe observe) Z
    (clight_readonly_check_algebra fe observe) (clight_readonly_branch_algebra fe observe)
    expression_body_prefix_spec fuel start.

Theorem expression_body_scan_sound fuel start entry :
  prefix_scan_property expression_body_prefix_spec fuel start entry ->
  forall i, start<=i<start+Z.of_nat fuel -> i<count entry -> expression_body_preserved i entry.
Proof.
  revert start; induction fuel as [|fuel IH]; intros start PROP i RANGE ACTIVE;
    cbn [prefix_scan_property expression_body_prefix_spec prefix_active prefix_next prefix_point_property] in PROP;
    [cbn in RANGE; lia|].
  destruct (PROP ltac:(lia)) as [PROPERTY REST]; destruct (Z.eq_dec i start); [subst; exact PROPERTY|].
  eapply IH; [exact REST|rewrite Nat2Z.inj_succ in RANGE; lia|exact ACTIVE].
Qed.
End PREFIX.

Print Assumptions expression_body_prefix_initial.
Print Assumptions expression_body_active_test.
Print Assumptions expression_body_prefix_receipt.
Print Assumptions expression_body_prefix_advance.
Print Assumptions expression_body_activity.
Print Assumptions expression_body_point.
Print Assumptions expression_body_scan_condition.
Print Assumptions expression_body_scan_sound.
