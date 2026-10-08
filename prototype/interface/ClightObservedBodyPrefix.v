From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightRedundantSet ClightNoWrap
  ClightLoopSyntax ClightRegionProgress ClightLoopExecution CompCertMemoryActions.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyBranching ReadonlyPrefixScan
  ClightReadonlyRewrite ClightConditionComposition ClightReadonlyBranching ClightReadonlyLoadedTreeSynthesis
  ClightIndexedAliasGuard ClightStrictIteration ClightStrictLoopProgress ClightAffineLoadedBoundTransport ClightStorePermissions ClightObservedHeaderPrefix.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A reached body may itself read captured observations. Unlike the older
    temp-only setup decoder, DECODE receives the current observation relation.
    Prefix advance still requires source-licensed point preservation. *)

Section PREFIX.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variables row cache : ident.
Variable header : expr.
Variable body : statement.
Variable stable : list ident.
Variable ready : clight_entry -> Prop.
Variable observations : clight_entry -> list (memory_location * val).
Variable upper : clight_entry -> Z -> Z.
Variable point : clight_entry -> Z -> Z -> mem -> mem -> Prop.
Hypothesis FRESH_ROW : ~ In row stable.
Hypotheses (NORMAL : normal_statement body = true) (QUIET : quiet_statement body = true).
Let count entry := Int.signed (temp_word cache (entry_temps entry)).

Hypothesis HEADER : forall entry i current memory,
  ready entry -> 0 <= i <= count entry -> current ! row = Some (Vint (Int.repr i)) ->
  temp_agree stable (entry_temps entry) current -> header_observations_match (observations entry) memory ->
  expression_test header (Entry (entry_ge entry) (entry_env entry) current memory) (i <? count entry).
Hypothesis DECODE : forall entry i current memory after final,
  ready entry -> 0 <= i < count entry -> current ! row = Some (Vint (Int.repr i)) ->
  temp_agree stable (entry_temps entry) current ->
  header_observations_match (observations entry) memory ->
  exec_stmt fe (entry_ge entry) (entry_env entry) current memory body E0 after final Out_normal ->
  counted_iterations (point entry i) (Z.to_nat (upper entry i)) 0 memory final /\
    after ! row = current ! row /\ temp_agree stable current after.
Hypothesis WIDTH : forall entry i, ready entry -> 0 <= i < count entry -> 0 <= upper entry i.
Hypothesis PERMISSIONS : forall entry i j before after,
  point entry i j before after -> memory_accesses_back before after.

Definition observed_body_prefix i entry :=
  ready entry /\ register_domain cache entry /\ 0 <= i <= count entry /\
  header_observations_match (observations entry) (entry_memory entry) /\
  exists current memory after final,
    current ! row = Some (Vint (Int.repr i)) /\ temp_agree stable (entry_temps entry) current /\
    header_observations_match (observations entry) memory /\
    memory_accesses_back (entry_memory entry) memory /\
    exec_stmt fe (entry_ge entry) (entry_env entry) current memory
      (strict_frontend_loop row header body) E0 after final Out_normal.

Lemma observed_body_prefix_initial entry after final :
  ready entry -> register_domain cache entry -> 0 <= count entry ->
  (entry_temps entry) ! row = Some (Vint Int.zero) ->
  header_observations_match (observations entry) (entry_memory entry) ->
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (strict_frontend_loop row header body) E0 after final Out_normal ->
  observed_body_prefix 0 entry.
Proof.
  intros READY CACHE COUNT ROW READS SOURCE; split; [exact READY|split; [exact CACHE|split; [lia|split; [exact READS|]]]].
  exists (entry_temps entry),(entry_memory entry),after,final.
  split; [exact ROW|split; [apply temp_agree_refl|split; [exact READS|split; [apply memory_accesses_back_refl|exact SOURCE]]]].
Qed.

Lemma observed_body_active_test i entry current memory :
  ready entry -> 0 <= i < count entry -> current ! row = Some (Vint (Int.repr i)) ->
  temp_agree stable (entry_temps entry) current -> header_observations_match (observations entry) memory ->
  expression_test header (Entry (entry_ge entry) (entry_env entry) current memory) true.
Proof.
  intros READY RANGE ROW FRAME READS; pose proof (@HEADER entry i current memory READY ltac:(lia) ROW FRAME READS) as TEST.
  assert (ACTIVE : (i <? count entry) = true) by (apply Z.ltb_lt; lia); rewrite ACTIVE in TEST; exact TEST.
Qed.

Theorem observed_body_prefix_receipt i entry :
  observed_body_prefix i entry -> i < count entry ->
  exists current memory after final,
    current ! row = Some (Vint (Int.repr i)) /\ temp_agree stable (entry_temps entry) current /\
    header_observations_match (observations entry) memory /\
    memory_accesses_back (entry_memory entry) memory /\
    exec_stmt fe (entry_ge entry) (entry_env entry) current memory body E0 after final Out_normal /\
    counted_iterations (point entry i) (Z.to_nat (upper entry i)) 0 memory final.
Proof.
  intros [READY [CACHE [RANGE [INITIAL [current [memory [after [final [ROW [FRAME [READS [BACK SOURCE]]]]]]]]]]]] ACTIVE.
  pose proof (@observed_body_active_test i entry current memory READY ltac:(lia) ROW FRAME READS) as TEST.
  destruct (@strict_active_iteration fe (entry_ge entry) (entry_env entry) row header body
    current memory after final NORMAL QUIET TEST SOURCE)
    as [body_temps [body_memory [next_temps [next_memory [BODY [INC TAIL]]]]]].
  destruct (@DECODE entry i current memory body_temps body_memory READY ltac:(lia) ROW FRAME READS BODY) as [ITER REST].
  exists current,memory,body_temps,body_memory; split; [exact ROW|split; [exact FRAME|split;
    [exact READS|split; [exact BACK|split; assumption]]]].
Qed.

Theorem observed_body_prefix_advance i entry :
  observed_body_prefix i entry -> i < count entry ->
  (forall observation, In observation (observations entry) -> forall j before after,
    0 <= j < upper entry i -> point entry i j before after ->
    location_load (fst observation) after = location_load (fst observation) before) ->
  observed_body_prefix (i+1) entry.
Proof.
  intros [READY [CACHE [RANGE [INITIAL [current [memory [after [final [ROW [FRAME [READS [BACK SOURCE]]]]]]]]]]]] ACTIVE PRESERVE.
  pose proof (@observed_body_active_test i entry current memory READY ltac:(lia) ROW FRAME READS) as TEST.
  destruct (@strict_active_iteration fe (entry_ge entry) (entry_env entry) row header body
    current memory after final NORMAL QUIET TEST SOURCE)
    as [body_temps [body_memory [next_temps [next_memory [BODY [INC TAIL]]]]]].
  destruct (@DECODE entry i current memory body_temps body_memory READY ltac:(lia) ROW FRAME READS BODY)
    as [ITER [AFTER_ROW AFTER_FRAME]].
  assert (BODY_READS : header_observations_match (observations entry) body_memory).
  { unfold header_observations_match in *; rewrite Forall_forall in READS |- *; intros observation MEMBER.
    assert (SAME : location_load (fst observation) body_memory = location_load (fst observation) memory).
    { eapply counted_observation_preserved; [|exact ITER].
      intros j JR first last STEP; apply PRESERVE with (j:=j); [exact MEMBER| |exact STEP].
      rewrite Z2Nat.id in JR by (apply WIDTH; [exact READY|lia]); lia. }
    rewrite SAME; apply READS; exact MEMBER. }
  assert (BODY_ROW : body_temps ! row = Some (Vint (Int.repr i))) by (rewrite AFTER_ROW; exact ROW).
  assert (SIGNED : signed_range i) by
    (pose proof (Int.signed_range (temp_word cache (entry_temps entry))); unfold count in ACTIVE;
     unfold signed_range; change Int.min_signed with (-2147483648) in *; lia).
  assert (STRICT : strict_counter_active row body_temps).
  { exists (Int.repr i); split; [exact BODY_ROW|rewrite Int.signed_repr by exact SIGNED;
      pose proof (Int.signed_range (temp_word cache (entry_temps entry))); unfold count in ACTIVE; lia]. }
  destruct (@strict_increment_execution_exact fe (entry_ge entry) (entry_env entry) row
    body_temps body_memory E0 next_temps next_memory Out_normal STRICT INC) as [_ [NEXT [MEMORY _]]].
  subst next_temps next_memory; rewrite (@counter_increment_small row body_temps i BODY_ROW) in TAIL.
  split; [exact READY|split; [exact CACHE|split; [lia|split; [exact INITIAL|]]]].
  exists (PTree.set row (Vint (Int.repr (i+1))) body_temps),body_memory,after,final.
  split; [apply PTree.gss|split; [|split; [exact BODY_READS|split; [|exact TAIL]]]].
  - intros identifier MEMBER; rewrite PTree.gso by (intro SAME; subst identifier; contradiction).
    rewrite AFTER_FRAME by exact MEMBER; exact (FRAME identifier MEMBER).
  - eapply memory_accesses_back_trans; [exact BACK|].
    eapply counted_memory_accesses_back; [|exact ITER]; intros j first last STEP; eapply PERMISSIONS; exact STEP.
Qed.

Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Variable row_probe : Z -> decision_tree.
Variable row_property : Z -> clight_entry -> Prop.
Hypothesis ROW_CHECK : forall i, readonly_condition (readonly_clight_host fe observe)
  (fun entry => observed_body_prefix i entry /\ i < count entry) (row_property i) (row_probe i).
Hypothesis PRESERVE : forall i entry, observed_body_prefix i entry -> i < count entry -> row_property i entry ->
  forall observation, In observation (observations entry) -> forall j before after,
    0 <= j < upper entry i -> point entry i j before after ->
    location_load (fst observation) after = location_load (fst observation) before.

Definition observed_body_active_probe i := Test (indexed_active_expr cache i) (Decision true) (Decision false).
Lemma observed_body_activity i : readonly_classifier (readonly_clight_host fe observe)
  (observed_body_prefix i) (fun entry => i < count entry) (fun entry => ~ i < count entry)
  (observed_body_active_probe i).
Proof.
  assert (DEFINED : forall entry, observed_body_prefix i entry ->
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

Lemma observed_body_point i : readonly_condition (readonly_clight_host fe observe)
  (fun entry => observed_body_prefix i entry /\ i < count entry)
  (fun entry => row_property i entry /\ observed_body_prefix (i+1) entry) (row_probe i).
Proof.
  eapply readonly_condition_entails; [apply ROW_CHECK|].
  intros entry [INV ACTIVE] PROPERTY; split; [exact PROPERTY|].
  eapply observed_body_prefix_advance; [exact INV|exact ACTIVE|].
  apply PRESERVE; assumption.
Defined.

Definition observed_body_prefix_spec : readonly_prefix_spec (readonly_clight_host fe observe) Z :=
  @ReadonlyPrefixSpec clight_entry (readonly_clight_host fe observe) Z (fun i => i+1)
    observed_body_active_probe row_probe observed_body_prefix (fun i entry => i < count entry) row_property
    observed_body_activity observed_body_point.
Definition observed_body_scan_condition fuel start :=
  @synthesized_prefix_scan_condition clight_entry (readonly_clight_host fe observe) Z
    (clight_readonly_check_algebra fe observe) (clight_readonly_branch_algebra fe observe)
    observed_body_prefix_spec fuel start.

Theorem observed_body_scan_sound fuel start entry :
  prefix_scan_property observed_body_prefix_spec fuel start entry ->
  forall i, start <= i < start+Z.of_nat fuel -> i < count entry -> row_property i entry.
Proof.
  revert start; induction fuel as [|fuel IH]; intros start PROP i RANGE ACTIVE;
    cbn [prefix_scan_property observed_body_prefix_spec prefix_active prefix_next prefix_point_property] in PROP;
    [cbn in RANGE; lia|].
  destruct (PROP ltac:(lia)) as [PROPERTY REST]; destruct (Z.eq_dec i start); [subst; exact PROPERTY|].
  eapply IH; [exact REST|rewrite Nat2Z.inj_succ in RANGE; lia|exact ACTIVE].
Qed.
End PREFIX.

Print Assumptions observed_body_prefix_initial.
Print Assumptions observed_body_active_test.
Print Assumptions observed_body_prefix_receipt.
Print Assumptions observed_body_prefix_advance.
Print Assumptions observed_body_activity.
Print Assumptions observed_body_point.
Print Assumptions observed_body_scan_condition.
Print Assumptions observed_body_scan_sound.

