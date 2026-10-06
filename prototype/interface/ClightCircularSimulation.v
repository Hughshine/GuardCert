From Stdlib Require Import List Bool Arith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightNoWrap ClightSameAddress
  ClightRegionProgress ClightTempFrame ClightTempFootprint ClightOpenRegionContract
  CompCertMemoryEquivalence.
From GuardInterface Require Import ClightCircularMachine ClightCircularGuard ClightCircularPrefix
  ClightCircularTransport ClightReadonlyCellSwap ClightStableLoadGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope nat_scope.

Definition circular_prefix_rank phase : nat :=
  match phase with
  | cm_start => 10 | cm_header => 9 | cm_inner => 8 | cm_head_skip => 7
  | cm_test => 6 | cm_body_skip => 5 | cm_store_pre => 4 | cm_store_skip => 3 | cm_store => 2 | _ => 0 end.

Section SIMULATION.
Variable live : list ident.
Variable iterator out bound cache : ident.
Hypothesis CACHE_FRESH : ~ In cache live.
Hypothesis ITER_BOUND : iterator <> bound.
Hypothesis ITER_OUT : iterator <> out.
Variable temps : bool.
Variable ge tge : genv.
Hypothesis GLOBALS : preserving_globals ge tge.
Variable fn tfn : function.
Variable outside toutside : cont.
Variable locals : env.
Let head := circular_loaded_test iterator bound.
Let cached := circular_cached_test iterator cache.
Let original := circular_memory_loop iterator out head.
Let replacement := guarded_circular_region iterator out bound cache.

Definition circular_inputs := In iterator live /\ In out live /\ In bound live.
Lemma circular_inputs_from_scope : statement_scope live original -> circular_inputs.
Proof.
  unfold circular_inputs, original, head, circular_memory_loop, ClightCounterProgress.generic_frontend_loop,
    circular_loaded_test, circular_store, circular_increment_expression,
    word_load, pointer_temp, statement_scope.
  cbn [statement_temps expression_temps]; intro SCOPE; repeat split; apply SCOPE; cbn; auto.
Qed.
Lemma circular_head_scope : circular_inputs -> expression_scope live head.
Proof.
  intros [ITER [OUT BOUND]]; unfold head, circular_loaded_test, word_load, pointer_temp, expression_scope.
  cbn [expression_temps]; intros id [SAME|[SAME|BAD]]; [subst; exact ITER | subst; exact BOUND | contradiction].
Qed.
Lemma circular_address_scope : circular_inputs -> expression_scope live (same_address_guard out bound).
Proof.
  intros [ITER [OUT BOUND]]; unfold same_address_guard, pointer_temp, expression_scope.
  cbn [expression_temps]; intros id [SAME|[SAME|BAD]]; [subst; exact OUT | subst; exact BOUND | contradiction].
Qed.

Definition circular_stable le tle m := exists b ofs upper,
  le ! bound = Some (Vptr b ofs) /\ Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint upper) /\
  tle ! cache = Some (Vint upper) /\ le ! out <> le ! bound.
Definition circular_pending phase le m :=
  0 < circular_prefix_rank phase /\
  (phase = cm_body_skip \/ phase = cm_store_pre \/ phase = cm_store_skip \/ phase = cm_store -> expression_test head (Entry ge locals le m) true).

Inductive circular_local_match : nat -> state -> state -> Prop :=
| local_pending : forall phase le tle m,
    circular_inputs -> temp_agree live le tle -> circular_pending phase le m ->
    circular_local_match (circular_prefix_rank phase)
      (circular_machine_state iterator out fn outside locals head phase le m)
      (State tfn replacement toutside locals tle m)
| local_fallback : forall phase le tle m,
    phase <> cm_done -> circular_inputs -> temp_agree live le tle ->
    circular_local_match 0
      (circular_machine_state iterator out fn outside locals head phase le m)
      (circular_machine_state iterator out tfn toutside locals head phase tle m)
| local_fast : forall phase le tle m,
    phase <> cm_done -> circular_inputs -> temp_agree live le tle -> circular_stable le tle m ->
    circular_local_match 0
      (circular_machine_state iterator out fn outside locals head phase le m)
      (circular_machine_state iterator out tfn toutside locals cached phase tle m).

Lemma circular_identity_next phase le tle m next_phase after final :
  circular_inputs -> temp_agree live le tle ->
  circular_move iterator out temps ge locals head phase le m next_phase after final ->
  exists tafter,
    circular_move iterator out temps tge locals head phase tle m next_phase tafter final /\
    temp_agree live after tafter.
Proof.
  intros INPUTS AGREE MOVE; eapply circular_move_identity.
  - exact GLOBALS.
  - exact (proj1 INPUTS).
  - exact (proj1 (proj2 INPUTS)).
  - apply circular_head_scope; exact INPUTS.
  - exact AGREE.
  - exact MOVE.
Qed.

Lemma circular_fast_next phase le tle m next_phase after final :
  circular_inputs -> temp_agree live le tle -> circular_stable le tle m ->
  circular_move iterator out temps ge locals head phase le m next_phase after final ->
  exists tafter,
    circular_move iterator out temps tge locals cached phase tle m next_phase tafter final /\
    temp_agree live after tafter /\ circular_stable after tafter final.
Proof.
  intros INPUTS AGREE STABLE MOVE; destruct INPUTS as [ITER [OUT BOUND]].
  destruct STABLE as [b [ofs [upper [PTR [READ [CACHE APART]]]]]].
  inversion MOVE; subst.
  all: try solve [exists tle; split; [constructor | split; [exact AGREE | do 3 eexists; eauto]]].
  - exists tle; split.
    + constructor; eapply circular_loaded_test_cached; eassumption.
    + split; [exact AGREE | do 3 eexists; eauto].
  - exists tle; split.
    + constructor; eapply circular_store_transport; eassumption.
    + split; [exact AGREE |]. exists b, ofs, upper; split; [exact PTR | split; [|auto]].
      eapply circular_store_preserves_bound; eassumption.
  - exists (PTree.set iterator value tle); split.
    + constructor; eapply circular_expression_transport; [exact GLOBALS | |exact AGREE |eassumption].
      unfold expression_scope; cbn [circular_increment_expression expression_temps];
        intros id [SAME|BAD]; [subst; exact ITER | contradiction].
    + split; [apply temp_agree_set_both; exact AGREE |].
      exists b, ofs, upper; rewrite !PTree.gso by
        (try exact (not_eq_sym ITER_BOUND); try exact (not_eq_sym ITER_OUT);
         intro SAME; subst cache; exact (CACHE_FRESH ITER)).
      repeat split; assumption.
Qed.

Lemma circular_store_dispatch le tle m final :
  circular_inputs -> temp_agree live le tle ->
  expression_test head (Entry ge locals le m) true ->
  exec_stmt (adapter_entry temps) ge locals le m (circular_store out iterator) E0 le final Out_normal ->
  exists target,
    star (adapter_step temps) tge (State tfn replacement toutside locals tle m) E0 target /\
    circular_local_match 0
      (circular_machine_state iterator out fn outside locals head cm_after_store le final) target.
Proof.
  intros INPUTS AGREE TEST STORE.
  destruct INPUTS as [ITER [OUT BOUND_SCOPE]].
  assert (INPUTS : circular_inputs) by (repeat split; assumption).
  pose proof (@circular_domain_from_prefix temps ge locals iterator out bound le m final TEST STORE)
    as [DOMAIN ADDRESSES].
  pose proof (ADDRESSES TEST) as ADDRESS_DOMAIN.
  pose proof (proj2 (@address_guard_correct out bound (Entry ge locals le m)
    (address_accept out bound (Entry ge locals le m)) ADDRESS_DOMAIN) eq_refl) as ADDRESS_TEST.
  pose proof (@circular_test_transport live ge tge locals le tle m head true
    GLOBALS (circular_head_scope INPUTS) AGREE TEST) as TARGET_HEAD.
  pose proof (@circular_test_transport live ge tge locals le tle m (same_address_guard out bound) _
    GLOBALS (circular_address_scope INPUTS) AGREE ADDRESS_TEST) as TARGET_ADDRESS.
  destruct (address_accept out bound (Entry ge locals le m)) eqn:ALIAS.
  - exists (circular_machine_state iterator out tfn toutside locals head cm_after_store tle final); split.
    + eapply circular_guard_alias; [exact TARGET_HEAD | exact TARGET_ADDRESS |].
      eapply circular_store_transport; eassumption.
    + apply local_fallback; [discriminate | exact INPUTS | exact AGREE].
  - assert (APART : le ! out <> le ! bound).
    { apply (stable_addresses_apart ADDRESS_DOMAIN); rewrite ALIAS; reflexivity. }
    destruct DOMAIN as [word [upper [b [ofs [ITER_VALUE [BOUND READ]]]]]].
    set (cached_temps := PTree.set cache (Vint upper) tle).
    assert (CACHED_AGREE : temp_agree live le cached_temps).
    { eapply temp_agree_trans; [exact AGREE | apply temp_agree_set; exact CACHE_FRESH]. }
    assert (CACHED_VALUE : cached_temps ! cache = Some (Vint upper)) by (apply PTree.gss).
    assert (CACHED_HEAD : expression_test cached (Entry tge locals cached_temps m) true).
    { eapply circular_loaded_test_cached; eassumption. }
    assert (TARGET_STORE : exec_stmt (adapter_entry temps) tge locals cached_temps m
      (circular_store out iterator) E0 cached_temps final Out_normal).
    { eapply circular_store_transport; eassumption. }
    exists (circular_machine_state iterator out tfn toutside locals cached cm_after_store cached_temps final); split.
    + eapply circular_guard_apart; [exact TARGET_HEAD | exact TARGET_ADDRESS | | exact CACHED_HEAD | exact TARGET_STORE].
      eapply circular_word_load_eval; [rewrite (AGREE bound BOUND_SCOPE); exact BOUND | exact READ].
    + apply local_fast; [discriminate | exact INPUTS | exact CACHED_AGREE |].
      exists b, ofs, upper; split; [exact BOUND | split; [|auto]].
      eapply circular_store_preserves_bound; eassumption.
Qed.

Lemma circular_local_advance index source target events next :
  circular_local_match index source target -> adapter_step temps ge source events next ->
  exists next_index next_target,
    (plus (adapter_step temps) tge target events next_target \/
     (star (adapter_step temps) tge target events next_target /\ next_index < index)) /\
    (circular_local_match next_index next next_target \/
     open_region_exit live fn tfn outside toutside locals next next_target).
Proof.
  intros MATCH STEP; inversion MATCH; subst.
  - destruct H1 as [RANK KNOWN_HEAD].
    assert (ACTIVE : phase <> cm_done) by (intro SAME; subst; cbn [circular_prefix_rank] in RANK; lia).
    destruct (@circular_machine_step_closed iterator out temps ge fn outside locals head phase le m events next ACTIVE STEP)
      as [next_phase [after [final [TRACE [NEXT MOVE]]]]]; subst events next.
    destruct phase; cbn [circular_prefix_rank] in RANK; try lia; inversion MOVE; subst.
    all: try solve [lazymatch goal with
      |- context [circular_local_match _ (circular_machine_state _ _ _ _ _ _ ?next_phase _ _) _] =>
        exists (circular_prefix_rank next_phase)
      end;
      exists (State tfn replacement toutside locals tle final); split;
      [right; split; [apply star_refl | cbn [circular_prefix_rank]; lia] | left;
       apply local_pending; [exact H | exact H0 | split; [cbn [circular_prefix_rank]; lia | intros BAD; decompose [or] BAD; discriminate]]]].
    all: try solve [lazymatch goal with
      |- context [circular_local_match _ (circular_machine_state _ _ _ _ _ _ ?next_phase _ _) _] =>
        exists (circular_prefix_rank next_phase)
      end;
      exists (State tfn replacement toutside locals tle final); split;
      [right; split; [apply star_refl | cbn [circular_prefix_rank]; lia] | left;
       apply local_pending; [exact H | exact H0 | split; [cbn [circular_prefix_rank]; lia |
         intros _; apply KNOWN_HEAD; auto]]]].
    + destruct flag.
      * exists (circular_prefix_rank cm_body_skip), (State tfn replacement toutside locals tle final); split.
        -- right; split; [apply star_refl | cbn [circular_prefix_rank]; lia].
        -- left; apply local_pending; [exact H | exact H0 | split; [cbn [circular_prefix_rank]; lia | intros _; assumption]].
      * exists 0, (circular_machine_state iterator out tfn toutside locals head cm_break_seq tle final); split.
        -- right; split; [|cbn [circular_prefix_rank]; lia].
           apply circular_guard_empty; eapply circular_test_transport; eauto using circular_head_scope.
        -- left; apply local_fallback; [discriminate | exact H | exact H0].
    + destruct (circular_store_dispatch H H0 (KNOWN_HEAD ltac:(auto)) ltac:(eassumption))
        as [next_target [RUN RESULT]].
      exists 0, next_target; split; [right; split; [exact RUN | cbn [circular_prefix_rank]; lia] | left; exact RESULT].
  - destruct (@circular_machine_step_closed iterator out temps ge fn outside locals head phase le m events next H STEP)
      as [next_phase [after [final [TRACE [NEXT MOVE]]]]]; subst events next.
    destruct (circular_identity_next H0 H1 MOVE) as [tafter [TARGET AGREE]].
    exists 0, (circular_machine_state iterator out tfn toutside locals head next_phase tafter final); split.
    + left; apply plus_one; apply circular_machine_step_sound; exact TARGET.
    + destruct (circular_phase_equal next_phase cm_done) as [DONE|ACTIVE].
      * right; subst next_phase; exists after, tafter, final, final.
        split; [reflexivity | split; [reflexivity | split; [exact AGREE | apply memory_equivalent_refl]]].
      * left; apply local_fallback; assumption.
  - destruct (@circular_machine_step_closed iterator out temps ge fn outside locals head phase le m events next H STEP)
      as [next_phase [after [final [TRACE [NEXT MOVE]]]]]; subst events next.
    destruct (circular_fast_next H0 H1 H2 MOVE) as [tafter [TARGET [AGREE STABLE]]].
    exists 0, (circular_machine_state iterator out tfn toutside locals cached next_phase tafter final); split.
    + left; apply plus_one; apply circular_machine_step_sound; exact TARGET.
    + destruct (circular_phase_equal next_phase cm_done) as [DONE|ACTIVE].
      * right; subst next_phase; exists after, tafter, final, final.
        split; [reflexivity | split; [reflexivity | split; [exact AGREE | apply memory_equivalent_refl]]].
      * left; apply local_fast; assumption.
Qed.

Definition circular_open_protocol : open_region_protocol live temps ge tge fn tfn outside toutside locals original replacement.
Proof.
  refine {| open_match := circular_local_match |}.
  - intros le tle m SCOPE AGREE; exists (circular_prefix_rank cm_start).
    apply local_pending with (phase := cm_start); [apply circular_inputs_from_scope; exact SCOPE | exact AGREE |].
    split; [cbn [circular_prefix_rank]; lia | intros BAD; decompose [or] BAD; discriminate].
  - intros index source target MATCH; inversion MATCH; subst;
      destruct (circular_machine_source_shape iterator out fn outside locals head phase le m)
        as [code [stack SHAPE]]; exists code, stack, le, m; exact SHAPE.
  - exact circular_local_advance.
Defined.

End SIMULATION.

Theorem guarded_circular_contract live iterator out bound cache :
  ~ In cache live -> iterator <> bound -> iterator <> out ->
  open_region_contract live (circular_memory_loop iterator out (circular_loaded_test iterator bound))
    (guarded_circular_region iterator out bound cache).
Proof.
  intros FRESH ITER_BOUND ITER_OUT; constructor.
  - reflexivity.
  - reflexivity.
  - intros temps ge tge fn tfn outside toutside locals GLOBALS.
    exists (@circular_open_protocol live iterator out bound cache FRESH ITER_BOUND ITER_OUT
      temps ge tge GLOBALS fn tfn outside toutside locals); exact I.
Qed.

Print Assumptions circular_fast_next.
Print Assumptions circular_store_dispatch.
Print Assumptions circular_local_advance.
Print Assumptions guarded_circular_contract.
