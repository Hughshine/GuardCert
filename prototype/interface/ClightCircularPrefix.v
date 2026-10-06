From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightSameAddress.
From GuardInterface Require Import ClightCircularMachine ClightCircularGuard.
Set Implicit Arguments.

Section PREFIX.
Variable iterator out : ident.
Variable temps : bool.
Variable ge : genv.
Variable fn : function.
Variable outside : cont.
Variable locals : env.

Lemma circular_prefix_to_test head le m :
  star (adapter_step temps) ge
    (circular_machine_state iterator out fn outside locals head cm_start le m) E0
    (circular_machine_state iterator out fn outside locals head cm_test le m).
Proof.
  eapply star_step; [apply circular_machine_step_sound; constructor | | reflexivity].
  eapply star_step; [apply circular_machine_step_sound; constructor | | reflexivity].
  eapply star_step; [apply circular_machine_step_sound; constructor | | reflexivity].
  eapply star_step; [apply circular_machine_step_sound; constructor | apply star_refl | reflexivity].
Qed.
Lemma circular_prefix_head head le m flag : expression_test head (Entry ge locals le m) flag ->
  star (adapter_step temps) ge
    (circular_machine_state iterator out fn outside locals head cm_start le m) E0
    (circular_machine_state iterator out fn outside locals head (if flag then cm_body_skip else cm_break_seq) le m).
Proof.
  intro TEST; eapply star_trans; [apply circular_prefix_to_test | |reflexivity].
  apply star_one; apply circular_machine_step_sound; constructor; exact TEST.
Qed.
Lemma circular_prefix_store head le m final : expression_test head (Entry ge locals le m) true ->
  exec_stmt (adapter_entry temps) ge locals le m (circular_store out iterator) E0 le final Out_normal ->
  star (adapter_step temps) ge
    (circular_machine_state iterator out fn outside locals head cm_start le m) E0
    (circular_machine_state iterator out fn outside locals head cm_after_store le final).
Proof.
  intros TEST STORE; eapply star_trans; [apply (circular_prefix_head TEST) | |reflexivity].
  eapply star_step; [apply circular_machine_step_sound; constructor | |reflexivity].
  eapply star_step; [apply circular_machine_step_sound; constructor | |reflexivity].
  eapply star_step; [apply circular_machine_step_sound; constructor | |reflexivity].
  apply star_one; apply circular_machine_step_sound; constructor; exact STORE.
Qed.

Lemma circular_guard_empty iterator_bound cache le m :
  expression_test (circular_loaded_test iterator iterator_bound) (Entry ge locals le m) false ->
  star (adapter_step temps) ge
    (State fn (guarded_circular_region iterator out iterator_bound cache) outside locals le m) E0
    (circular_machine_state iterator out fn outside locals (circular_loaded_test iterator iterator_bound) cm_break_seq le m).
Proof.
  intros TEST; unfold guarded_circular_region, circular_guard; cbn [tree_statement].
  destruct TEST as [value [EVAL BOOL]].
  eapply star_step; [unfold adapter_step; eapply step_ifthenelse with (b := false); eauto | |reflexivity].
  apply circular_prefix_head with (flag := false); exists value; split; assumption.
Qed.
Lemma circular_guard_alias iterator_bound cache le m final :
  expression_test (circular_loaded_test iterator iterator_bound) (Entry ge locals le m) true ->
  expression_test (same_address_guard out iterator_bound) (Entry ge locals le m) true ->
  exec_stmt (adapter_entry temps) ge locals le m (circular_store out iterator) E0 le final Out_normal ->
  star (adapter_step temps) ge
    (State fn (guarded_circular_region iterator out iterator_bound cache) outside locals le m) E0
    (circular_machine_state iterator out fn outside locals (circular_loaded_test iterator iterator_bound) cm_after_store le final).
Proof.
  intros HEAD ALIAS STORE; unfold guarded_circular_region, circular_guard; cbn [tree_statement].
  destruct HEAD as [value [EVAL BOOL]], ALIAS as [pointer_result [CMP POINTER_BOOL]].
  eapply star_step; [unfold adapter_step; eapply step_ifthenelse with (b := true); eauto | |reflexivity].
  eapply star_step; [unfold adapter_step; eapply step_ifthenelse with (b := true); eauto | |reflexivity].
  apply circular_prefix_store; [exists value; auto | exact STORE].
Qed.
Lemma circular_guard_apart iterator_bound cache le m upper final :
  expression_test (circular_loaded_test iterator iterator_bound) (Entry ge locals le m) true ->
  expression_test (same_address_guard out iterator_bound) (Entry ge locals le m) false ->
  eval_expr ge locals le m (word_load iterator_bound) (Vint upper) ->
  expression_test (circular_cached_test iterator cache)
    (Entry ge locals (PTree.set cache (Vint upper) le) m) true ->
  exec_stmt (adapter_entry temps) ge locals (PTree.set cache (Vint upper) le) m
    (circular_store out iterator) E0 (PTree.set cache (Vint upper) le) final Out_normal ->
  star (adapter_step temps) ge
    (State fn (guarded_circular_region iterator out iterator_bound cache) outside locals le m) E0
    (circular_machine_state iterator out fn outside locals (circular_cached_test iterator cache)
      cm_after_store (PTree.set cache (Vint upper) le) final).
Proof.
  intros HEAD APART LOAD CACHED STORE; unfold guarded_circular_region, circular_guard; cbn [tree_statement].
  destruct HEAD as [value [EVAL BOOL]], APART as [pointer_result [CMP POINTER_BOOL]].
  eapply star_step; [unfold adapter_step; eapply step_ifthenelse with (b := true); eauto | |reflexivity].
  eapply star_step; [unfold adapter_step; eapply step_ifthenelse with (b := false); eauto | |reflexivity].
  unfold guarded_circular_candidate.
  eapply star_step; [unfold adapter_step; apply step_seq | |reflexivity].
  eapply star_step; [unfold adapter_step; apply step_set; exact LOAD | |reflexivity].
  eapply star_step; [unfold adapter_step; apply step_skip_seq | |reflexivity].
  apply circular_prefix_store; assumption.
Qed.
End PREFIX.

Print Assumptions circular_prefix_store.
Print Assumptions circular_guard_empty.
Print Assumptions circular_guard_alias.
Print Assumptions circular_guard_apart.
