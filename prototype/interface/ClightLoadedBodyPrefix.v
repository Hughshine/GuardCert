From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightRedundantSet
  ClightNoWrap ClightLoopSyntax ClightRegionProgress ClightLoopExecution.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyBranching ReadonlyPrefixScan
  ClightReadonlyRewrite ClightReadonlyLoadedTreeSynthesis ClightConditionComposition ClightReadonlyBranching ClightIndexedAliasGuard
  ClightLoadedBoundSyntax ClightStrictIteration ClightStrictLoopProgress ClightStorePermissions ClightStructuredStorePermissions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The body is arbitrary structured code, including recursively nested
    loops. The domain-specific point check must preserve the observation for
    the actual body, rather than supply a two-dimensional counted-row model. *)
Section PREFIX.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variables row cache pointer : ident.
Variable body : statement.
Variable stable : list ident.
Variable ready : clight_entry -> Prop.
Let count entry := Int.signed (temp_word cache (entry_temps entry)).

Definition loaded_body_preserved i entry :=
  forall block offset current memory after final,
    (entry_temps entry)!pointer=Some(Vptr block offset) ->
    current!row=Some(Vint(Int.repr i)) -> temp_agree stable (entry_temps entry) current ->
    Mem.loadv Mint32 memory (Vptr block offset)=Some(Vint(temp_word cache (entry_temps entry))) ->
    exec_stmt fe (entry_ge entry) (entry_env entry) current memory body E0 after final Out_normal ->
    Mem.loadv Mint32 final (Vptr block offset)=Mem.loadv Mint32 memory (Vptr block offset).

Definition loaded_body_prefix i entry :=
  ready entry /\ register_domain cache entry /\ 0<=i<=count entry /\
  exists block offset current memory after final,
    (entry_temps entry)!pointer=Some(Vptr block offset) /\
    Mem.loadv Mint32 (entry_memory entry) (Vptr block offset)=Some(Vint(temp_word cache (entry_temps entry))) /\
    current!row=Some(Vint(Int.repr i)) /\ temp_agree stable (entry_temps entry) current /\
    Mem.loadv Mint32 memory (Vptr block offset)=Some(Vint(temp_word cache (entry_temps entry))) /\
    memory_accesses_back (entry_memory entry) memory /\
    exec_stmt fe (entry_ge entry) (entry_env entry) current memory
      (loaded_bound_loop row pointer body) E0 after final Out_normal.

Lemma loaded_body_prefix_initial entry block offset after final :
  ready entry -> register_domain cache entry -> 0<=count entry ->
  (entry_temps entry)!row=Some(Vint Int.zero) ->
  (entry_temps entry)!pointer=Some(Vptr block offset) ->
  Mem.loadv Mint32 (entry_memory entry) (Vptr block offset)=Some(Vint(temp_word cache (entry_temps entry))) ->
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (loaded_bound_loop row pointer body) E0 after final Out_normal -> loaded_body_prefix 0 entry.
Proof.
  intros READY CACHE COUNT ROW POINTER READ SOURCE; split; [exact READY|split; [exact CACHE|split; [lia|]]].
  exists block,offset,(entry_temps entry),(entry_memory entry),after,final.
  split; [exact POINTER|split; [exact READ|split; [exact ROW|split; [apply temp_agree_refl|
    split; [exact READ|split; [apply memory_accesses_back_refl|exact SOURCE]]]]]].
Qed.

Hypothesis POINTER_MEMBER : In pointer stable.
Hypotheses (NORMAL : normal_statement body=true) (QUIET : quiet_statement body=true).

Lemma loaded_body_active_test i entry block offset current memory :
  0<=i<count entry -> (entry_temps entry)!pointer=Some(Vptr block offset) ->
  current!row=Some(Vint(Int.repr i)) -> temp_agree stable (entry_temps entry) current ->
  Mem.loadv Mint32 memory (Vptr block offset)=Some(Vint(temp_word cache (entry_temps entry))) ->
  expression_test (loaded_bound_test row pointer) (Entry (entry_ge entry) (entry_env entry) current memory) true.
Proof.
  intros RANGE POINTER ROW FRAME READ.
  assert (SIGNED : signed_range i).
  { pose proof (Int.signed_range (temp_word cache (entry_temps entry)));
      unfold count in RANGE; unfold signed_range; change Int.min_signed with (-2147483648) in *; lia. }
  assert (LT : Int.lt (Int.repr i) (temp_word cache (entry_temps entry))=true).
  { unfold Int.lt; rewrite Int.signed_repr by exact SIGNED.
    destruct (zlt i (Int.signed (temp_word cache (entry_temps entry)))); [reflexivity|unfold count in RANGE; lia]. }
  rewrite <-LT; eapply loaded_bound_test_eval; [exact ROW|rewrite FRAME by exact POINTER_MEMBER; exact POINTER|exact READ].
Qed.

Theorem loaded_body_prefix_receipt i entry :
  loaded_body_prefix i entry -> i<count entry ->
  exists block offset current memory after final,
    (entry_temps entry)!pointer=Some(Vptr block offset) /\
    current!row=Some(Vint(Int.repr i)) /\ temp_agree stable (entry_temps entry) current /\
    Mem.loadv Mint32 memory (Vptr block offset)=Some(Vint(temp_word cache (entry_temps entry))) /\
    memory_accesses_back (entry_memory entry) memory /\
    exec_stmt fe (entry_ge entry) (entry_env entry) current memory body E0 after final Out_normal.
Proof.
  intros [READY [CACHE [RANGE [block [offset [current [memory [after [final
    [POINTER [INITIAL [ROW [FRAME [READ [BACK SOURCE]]]]]]]]]]]]]]] ACTIVE.
  pose proof (@loaded_body_active_test i entry block offset current memory ltac:(lia) POINTER ROW FRAME READ) as TEST.
  destruct (@strict_active_iteration fe (entry_ge entry) (entry_env entry) row (loaded_bound_test row pointer) body
    current memory after final NORMAL QUIET TEST SOURCE) as [body_temps [body_memory [next_temps [next_memory [BODY REST]]]]].
  exists block,offset,current,memory,body_temps,body_memory.
  split; [exact POINTER|split; [exact ROW|split; [exact FRAME|split; [exact READ|split; assumption]]]].
Qed.

Variable written : list ident.
Hypothesis WRITES : writes_only written body.
Hypothesis ROW_UNWRITTEN : ~In row written.
Hypothesis STABLE_UNWRITTEN : forall identifier, In identifier stable -> ~In identifier written.
Hypothesis ROW_FRESH : ~In row stable.

Theorem loaded_body_prefix_advance i entry :
  loaded_body_prefix i entry -> i<count entry -> loaded_body_preserved i entry -> loaded_body_prefix (i+1) entry.
Proof.
  intros [READY [CACHE [RANGE [block [offset [current [memory [after [final
    [POINTER [INITIAL [ROW [FRAME [READ [BACK SOURCE]]]]]]]]]]]]]]] ACTIVE PRESERVE.
  pose proof (@loaded_body_active_test i entry block offset current memory ltac:(lia) POINTER ROW FRAME READ) as TEST.
  destruct (@strict_active_iteration fe (entry_ge entry) (entry_env entry) row (loaded_bound_test row pointer) body
    current memory after final NORMAL QUIET TEST SOURCE)
    as [body_temps [body_memory [next_temps [next_memory [BODY [INC TAIL]]]]]].
  assert (BODY_READ : Mem.loadv Mint32 body_memory (Vptr block offset)=Some(Vint(temp_word cache (entry_temps entry)))).
  { rewrite (PRESERVE block offset current memory body_temps body_memory POINTER ROW FRAME READ BODY); exact READ. }
  assert (BODY_ROW : body_temps!row=Some(Vint(Int.repr i))).
  { rewrite (@writes_only_frame _ _ _ _ _ _ _ _ _ _ BODY written WRITES row ROW_UNWRITTEN); exact ROW. }
  assert (BODY_FRAME : temp_agree stable current body_temps).
  { eapply structured_temp_frame; eassumption. }
  assert (SIGNED : signed_range i).
  { pose proof (Int.signed_range (temp_word cache (entry_temps entry)));
      unfold count in ACTIVE; unfold signed_range; change Int.min_signed with (-2147483648) in *; lia. }
  assert (STRICT : strict_counter_active row body_temps).
  { exists (Int.repr i); split; [exact BODY_ROW|rewrite Int.signed_repr by exact SIGNED;
      pose proof (Int.signed_range (temp_word cache (entry_temps entry))); unfold count in ACTIVE; lia]. }
  destruct (@strict_increment_execution_exact fe (entry_ge entry) (entry_env entry) row
    body_temps body_memory E0 next_temps next_memory Out_normal STRICT INC) as [_ [NEXT [MEMORY _]]].
  subst next_temps next_memory; rewrite (@counter_increment_small row body_temps i BODY_ROW) in TAIL.
  split; [exact READY|split; [exact CACHE|split; [lia|]]].
  exists block,offset,(PTree.set row (Vint(Int.repr(i+1))) body_temps),body_memory,after,final.
  split; [exact POINTER|split; [exact INITIAL|split; [apply PTree.gss|split; [|split; [exact BODY_READ|split; [|exact TAIL]]]]]].
  - intros identifier MEMBER; rewrite PTree.gso by (intro SAME; subst identifier; contradiction).
    rewrite BODY_FRAME by exact MEMBER; apply FRAME; exact MEMBER.
  - eapply memory_accesses_back_trans; [exact BACK|eapply structured_memory_accesses_back; eassumption].
Qed.

Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Variable body_probe : Z -> decision_tree.
Hypothesis BODY_CHECK : forall i, readonly_condition (readonly_clight_host fe observe)
  (fun entry=>loaded_body_prefix i entry /\ i<count entry) (loaded_body_preserved i) (body_probe i).

Definition loaded_body_active_probe i := Test (indexed_active_expr cache i) (Decision true) (Decision false).
Lemma loaded_body_activity i : readonly_classifier (readonly_clight_host fe observe)
  (loaded_body_prefix i) (fun entry=>i<count entry) (fun entry=>~i<count entry) (loaded_body_active_probe i).
Proof.
  assert (DEFINED : forall entry, loaded_body_prefix i entry ->
    expression_test (indexed_active_expr cache i) entry (indexed_active_flag cache i entry)).
  { intros entry [READY [CACHE [RANGE REST]]]; apply indexed_active_test; [|exact CACHE].
    pose proof (Int.signed_range (temp_word cache (entry_temps entry)));
      unfold count in RANGE; unfold signed_range; change Int.min_signed with (-2147483648) in *; lia. }
  apply readonly_expression_classifier.
  - intros entry INV; eexists; apply DEFINED; exact INV.
  - intros entry INV TEST; pose proof (readonly_test_determinate (DEFINED entry INV) TEST) as FLAG.
    unfold indexed_active_flag in FLAG; apply Z.ltb_lt in FLAG; exact FLAG.
  - intros entry INV TEST; pose proof (readonly_test_determinate (DEFINED entry INV) TEST) as FLAG.
    unfold indexed_active_flag in FLAG; apply Z.ltb_ge in FLAG; unfold count; lia.
Defined.

Lemma loaded_body_point i : readonly_condition (readonly_clight_host fe observe)
  (fun entry=>loaded_body_prefix i entry /\ i<count entry)
  (fun entry=>loaded_body_preserved i entry /\ loaded_body_prefix (i+1) entry) (body_probe i).
Proof.
  eapply readonly_condition_entails; [apply BODY_CHECK|].
  intros entry [INV ACTIVE] PROPERTY; split; [exact PROPERTY|eapply loaded_body_prefix_advance; eassumption].
Defined.

Definition loaded_body_prefix_spec : readonly_prefix_spec (readonly_clight_host fe observe) Z :=
  @ReadonlyPrefixSpec clight_entry (readonly_clight_host fe observe) Z (fun i=>i+1)
    loaded_body_active_probe body_probe loaded_body_prefix (fun i entry=>i<count entry) loaded_body_preserved
    loaded_body_activity loaded_body_point.

Theorem loaded_body_scan_sound fuel start entry :
  prefix_scan_property loaded_body_prefix_spec fuel start entry ->
  forall i, start<=i<start+Z.of_nat fuel -> i<count entry -> loaded_body_preserved i entry.
Proof.
  revert start; induction fuel as [|fuel IH]; intros start PROP i RANGE ACTIVE;
    cbn [prefix_scan_property loaded_body_prefix_spec prefix_active prefix_next prefix_point_property] in PROP;
    [cbn in RANGE; lia|].
  destruct (PROP ltac:(lia)) as [PROPERTY REST]; destruct (Z.eq_dec i start); [subst; exact PROPERTY|].
  eapply IH; [exact REST|rewrite Nat2Z.inj_succ in RANGE; lia|exact ACTIVE].
Qed.

(** Unlike a silent assumption of finite coverage, the fuel obligation is an
    explicit hypothesis of the complete observation-preservation certificate. *)
Definition loaded_body_stability_condition fuel : readonly_condition (readonly_clight_host fe observe)
  (fun entry=>loaded_body_prefix 0 entry /\ count entry<=Z.of_nat fuel)
  (fun entry=>forall i, 0<=i<count entry -> loaded_body_preserved i entry)
  (synthesize_prefix_scan (clight_readonly_check_algebra fe observe)
    (clight_readonly_branch_algebra fe observe) loaded_body_prefix_spec fuel 0).
Proof.
  eapply readonly_condition_entails.
  - eapply readonly_condition_restrict; [apply synthesized_prefix_scan_condition|intros entry [INV COVER]; exact INV].
  - intros entry [INV COVER] CHECKED i RANGE; eapply loaded_body_scan_sound; [exact CHECKED|lia|lia].
Defined.
End PREFIX.

Print Assumptions loaded_body_prefix_initial.
Print Assumptions loaded_body_active_test.
Print Assumptions loaded_body_prefix_receipt.
Print Assumptions loaded_body_prefix_advance.
Print Assumptions loaded_body_activity.
Print Assumptions loaded_body_point.
Print Assumptions loaded_body_scan_sound.
Print Assumptions loaded_body_stability_condition.
