From Stdlib Require Import List.
From compcert.lib Require Import Coqlib Maps.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightGuard CompCertMemoryEquivalence CompCertOperatorEquivalence
  ClightMemoryEquivalence.

Lemma expression_memory_transport ge e le first second a v :
  memory_equivalent first second -> eval_expr ge e le first a v -> eval_expr ge e le second a v.
Proof. intros EQ RUN; eapply (proj1 (expressions_memory_equivalent ge e le _ _ EQ)); exact RUN. Qed.
Lemma lvalue_memory_transport ge e le first second a b ofs bf :
  memory_equivalent first second -> eval_lvalue ge e le first a b ofs bf ->
  eval_lvalue ge e le second a b ofs bf.
Proof. intros EQ RUN; eapply (proj2 (expressions_memory_equivalent ge e le _ _ EQ)); exact RUN. Qed.
Lemma cast_memory_transport first second v from to result :
  memory_equivalent first second -> sem_cast v from to first = Some result ->
  sem_cast v from to second = Some result.
Proof. intros EQ RUN; rewrite <- (memory_equivalent_cast _ _ _ _ _ EQ); exact RUN. Qed.
Lemma bool_memory_transport first second v ty result :
  memory_equivalent first second -> bool_val v ty first = Some result -> bool_val v ty second = Some result.
Proof. intros EQ RUN; rewrite <- (memory_equivalent_bool _ _ _ _ EQ); exact RUN. Qed.

Lemma exprlist_memory_transport ge e le first second args tys values :
  memory_equivalent first second -> eval_exprlist ge e le first args tys values ->
  eval_exprlist ge e le second args tys values.
Proof.
  intros EQ RUN; induction RUN; econstructor; eauto using expression_memory_transport, cast_memory_transport.
Qed.

(** Same code and continuation, equivalent memory. This is a context
    transport property of Clight, not a program transformation by itself. *)
Inductive memory_related_states : state -> state -> Prop :=
| memory_state : forall f s k e le first second,
    memory_equivalent first second ->
    memory_related_states (State f s k e le first) (State f s k e le second)
| memory_call : forall fd args k first second,
    memory_equivalent first second ->
    memory_related_states (Callstate fd args k first) (Callstate fd args k second)
| memory_return : forall v k first second,
    memory_equivalent first second ->
    memory_related_states (Returnstate v k first) (Returnstate v k second).

Local Hint Resolve expression_memory_transport lvalue_memory_transport cast_memory_transport
  bool_memory_transport exprlist_memory_transport : core.

Theorem step_memory_transport temps ge source trace source' :
  adapter_step temps ge source trace source' -> forall target,
  memory_related_states source target ->
  exists target', adapter_step temps ge target trace target' /\ memory_related_states source' target'.
Proof.
  intros STEP target MATCH; inversion STEP; subst; inversion MATCH; subst.
  all: try solve [eexists; split; [unfold adapter_step; econstructor; eauto | constructor; auto]].
  - match goal with EQ : memory_equivalent _ _, WRITE : assign_loc _ _ _ _ _ _ _ _ |- _ =>
      destruct (assign_loc_memory_equivalent _ _ _ _ _ _ _ _ _ EQ WRITE) as [final [WRITE' NEXT]] end.
    eexists; split; [unfold adapter_step; eapply step_assign; eauto | constructor; auto].
  - match goal with EQ : memory_equivalent _ _, CALL : external_call _ _ _ _ _ _ _ |- _ =>
      destruct (memory_equivalent_external_call _ _ _ _ _ _ _ _ EQ CALL) as [final [CALL' NEXT]] end.
    eexists; split; [unfold adapter_step; eapply step_builtin; eauto | constructor; auto].
  - match goal with EQ : memory_equivalent _ _, FREE : Mem.free_list _ _ = Some _ |- _ =>
      destruct (memory_equivalent_free_list _ _ _ _ EQ FREE) as [final [FREE' NEXT]] end.
    eexists; split; [unfold adapter_step; eapply step_return_0; eauto | constructor; auto].
  - match goal with EQ : memory_equivalent _ _, FREE : Mem.free_list _ _ = Some _ |- _ =>
      destruct (memory_equivalent_free_list _ _ _ _ EQ FREE) as [final [FREE' NEXT]] end.
    eexists; split; [unfold adapter_step; eapply step_return_1; eauto | constructor; auto].
  - match goal with EQ : memory_equivalent _ _, FREE : Mem.free_list _ _ = Some _ |- _ =>
      destruct (memory_equivalent_free_list _ _ _ _ EQ FREE) as [final [FREE' NEXT]] end.
    eexists; split; [unfold adapter_step; eapply step_skip_call; eauto | constructor; auto].
  - match goal with EQ : memory_equivalent _ _, ENTRY : adapter_entry temps ge _ _ _ _ _ _ |- _ =>
      destruct (entry_memory_equivalent _ _ _ _ _ _ _ _ _ EQ ENTRY) as [final [ENTRY' NEXT]] end.
    eexists; split; [unfold adapter_step; eapply step_internal_function; eauto | constructor; auto].
  - match goal with EQ : memory_equivalent _ _, CALL : external_call _ _ _ _ _ _ _ |- _ =>
      destruct (memory_equivalent_external_call _ _ _ _ _ _ _ _ EQ CALL) as [final [CALL' NEXT]] end.
    eexists; split; [unfold adapter_step; eapply step_external_function; eauto | constructor; auto].
Qed.

Theorem star_memory_transport temps ge source trace source' :
  star (adapter_step temps) ge source trace source' -> forall target,
  memory_related_states source target ->
  exists target', star (adapter_step temps) ge target trace target' /\ memory_related_states source' target'.
Proof.
  intro RUN; induction RUN; intros target MATCH.
  - exists target; split; [apply star_refl | exact MATCH].
  - destruct (step_memory_transport _ _ _ _ _ H _ MATCH) as [middle [STEP NEXT]].
    destruct (IHRUN _ NEXT) as [final [REST RESULT]].
    exists final; split; [econstructor; eauto | exact RESULT].
Qed.

Print Assumptions step_memory_transport.
