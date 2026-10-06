From Stdlib Require Import List.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightGuard ClightNoWrap ClightTempFrame
  ClightTempFootprint ClightRegionProgress ClightSameAddress.
From GuardInterface Require Import ClightCircularMachine ClightCircularCounter
  ClightReadonlyCellSwap ClightStableLoadBody.
Import ListNotations.
Set Implicit Arguments.

Lemma circular_expression_transport live ge tge locals le tle m a value :
  preserving_globals ge tge -> expression_scope live a -> temp_agree live le tle ->
  eval_expr ge locals le m a value -> eval_expr tge locals tle m a value.
Proof.
  intros GLOBALS SCOPE AGREE RUN.
  eapply expression_temp_transport; [exact SCOPE | exact AGREE |].
  eapply (proj1 (region_expressions_preserved GLOBALS locals le m)); exact RUN.
Qed.
Lemma circular_test_transport live ge tge locals le tle m a flag :
  preserving_globals ge tge -> expression_scope live a -> temp_agree live le tle ->
  expression_test a (Entry ge locals le m) flag -> expression_test a (Entry tge locals tle m) flag.
Proof.
  intros GLOBALS SCOPE AGREE [value [EVAL BOOL]]. exists value; split; [|exact BOOL].
  eapply circular_expression_transport; eassumption.
Qed.
Lemma circular_store_transport live temps ge tge locals le tle m final iterator out :
  preserving_globals ge tge -> In iterator live -> In out live -> temp_agree live le tle ->
  exec_stmt (adapter_entry temps) ge locals le m (circular_store out iterator) E0 le final Out_normal ->
  exec_stmt (adapter_entry temps) tge locals tle m (circular_store out iterator) E0 tle final Out_normal.
Proof.
  intros GLOBALS ITER OUT AGREE RUN.
  pose proof (@quiet_execution_preserved (adapter_entry temps) (adapter_entry temps) ge tge GLOBALS
    locals le m (circular_store out iterator) E0 le final Out_normal RUN eq_refl) as PRESERVED.
  inversion PRESERVED; subst.
  econstructor; [| |eassumption|eassumption].
  - eapply lvalue_temp_transport with (le := le) (live := live); [|exact AGREE|].
    + unfold expression_scope; cbn [word_load pointer_temp expression_temps]; intros id [SAME|BAD]; [subst; exact OUT | contradiction].
    + eassumption.
  - eapply expression_temp_transport; [| exact AGREE | eassumption].
    unfold expression_scope; cbn [expression_temps]; intros id [SAME|BAD]; [subst; exact ITER | contradiction].
Qed.

Lemma circular_loaded_test_cached live ge tge locals le tle m iterator bound cache b ofs upper flag :
  In iterator live -> temp_agree live le tle ->
  le ! bound = Some (Vptr b ofs) -> Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint upper) ->
  tle ! cache = Some (Vint upper) ->
  expression_test (circular_loaded_test iterator bound) (Entry ge locals le m) flag ->
  expression_test (circular_cached_test iterator cache) (Entry tge locals tle m) flag.
Proof.
  intros ITER_SCOPE AGREE PTR READ CACHE TEST.
  destruct (circular_loaded_test_facts TEST) as [word [other [p [off [ITER [BOUND [LOAD FLAG]]]]]]].
  assert (ADDRESS : Vptr p off = Vptr b ofs) by congruence; injection ADDRESS as SAME SAME'; subst p off.
  assert (WORD : other = upper) by congruence; subst other; rewrite FLAG.
  exists (Val.of_bool (negb (Int.eq word upper))); split; [|apply bool_of_bool].
  eapply eval_Ebinop with (v1 := Vint word) (v2 := Vint upper).
  - apply eval_Etempvar; cbn [entry_temps]; rewrite (AGREE iterator ITER_SCOPE); exact ITER.
  - apply eval_Etempvar; exact CACHE.
  - reflexivity.
Qed.

Lemma circular_store_preserves_bound temps ge locals le m final iterator out bound b ofs upper :
  le ! bound = Some (Vptr b ofs) -> Mem.loadv Mint32 m (Vptr b ofs) = Some upper ->
  le ! out <> le ! bound ->
  exec_stmt (adapter_entry temps) ge locals le m (circular_store out iterator) E0 le final Out_normal ->
  Mem.loadv Mint32 final (Vptr b ofs) = Some upper.
Proof.
  intros BOUND READ APART STORE.
  destruct (circular_store_facts STORE) as [p [off [value [OUT WRITE]]]].
  eapply mint32_load_survives_apart_store; [exact WRITE | exact READ |].
  intro SAME; apply APART; congruence.
Qed.

Lemma circular_move_identity live temps ge tge locals iterator out head phase le tle m next_phase after final :
  preserving_globals ge tge -> In iterator live -> In out live -> expression_scope live head ->
  temp_agree live le tle ->
  circular_move iterator out temps ge locals head phase le m next_phase after final ->
  exists tafter, circular_move iterator out temps tge locals head phase tle m next_phase tafter final /\
    temp_agree live after tafter.
Proof.
  intros GLOBALS ITER OUT HEAD AGREE MOVE; inversion MOVE; subst.
  all: try solve [exists tle; split; [constructor | exact AGREE]].
  - exists tle; split; [constructor; eapply circular_test_transport; eassumption | exact AGREE].
  - exists tle; split; [constructor; eapply circular_store_transport; eassumption | exact AGREE].
  - exists (PTree.set iterator value tle); split; [constructor | apply temp_agree_set_both; exact AGREE].
    eapply circular_expression_transport; [exact GLOBALS | |exact AGREE |eassumption].
    unfold expression_scope; cbn [circular_increment_expression expression_temps];
      intros id [SAME|BAD]; [subst; exact ITER | contradiction].
Qed.

Print Assumptions circular_store_transport.
Print Assumptions circular_loaded_test_cached.
Print Assumptions circular_store_preserves_bound.
Print Assumptions circular_move_identity.
