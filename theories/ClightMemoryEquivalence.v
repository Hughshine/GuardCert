From Stdlib Require Import List.
From compcert.lib Require Import Coqlib Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import CompCertMemoryEquivalence CompCertOperatorEquivalence.
From Guard Require Import ClightGuard ClightCondition.

Lemma load_bitfield_memory_equivalent ty sz sg pos width first second addr value :
  memory_equivalent first second -> load_bitfield ty sz sg pos width first addr value ->
  load_bitfield ty sz sg pos width second addr value.
Proof. intros EQ LOAD; inversion LOAD; subst; econstructor; eauto using memory_equivalent_loadv. Qed.

Lemma deref_loc_memory_equivalent ty first second b ofs bf value :
  memory_equivalent first second -> deref_loc ty first b ofs bf value ->
  deref_loc ty second b ofs bf value.
Proof.
  intros EQ LOAD; inversion LOAD; subst.
  - eapply deref_loc_value; eauto using memory_equivalent_loadv.
  - apply deref_loc_reference; assumption.
  - apply deref_loc_copy; assumption.
  - eapply deref_loc_bitfield; eauto using load_bitfield_memory_equivalent.
Qed.

Theorem expressions_memory_equivalent ge e le first second :
  memory_equivalent first second ->
  (forall a value, eval_expr ge e le first a value -> eval_expr ge e le second a value) /\
  (forall a b ofs bf, eval_lvalue ge e le first a b ofs bf -> eval_lvalue ge e le second a b ofs bf).
Proof.
  intro EQ. apply eval_expr_lvalue_ind; intros; try solve [econstructor; eauto].
  - econstructor; eauto. erewrite <- memory_equivalent_unary; eauto.
  - econstructor; eauto. erewrite <- memory_equivalent_binary; eauto.
  - econstructor; eauto. erewrite <- memory_equivalent_cast; eauto.
  - econstructor; eauto using deref_loc_memory_equivalent.
Qed.

Lemma store_bitfield_memory_equivalent ty sz sg pos width first second addr value first' normalized :
  memory_equivalent first second -> store_bitfield ty sz sg pos width first addr value first' normalized ->
  exists second', store_bitfield ty sz sg pos width second addr value second' normalized /\
    memory_equivalent first' second'.
Proof.
  intros EQ STORE; inversion STORE; subst.
  match goal with WRITE : Mem.storev _ _ _ _ = Some _ |- _ =>
    destruct (memory_equivalent_storev _ _ _ _ _ _ EQ WRITE) as [second' [WRITE' NEXT]] end.
  exists second'; split; [econstructor; eauto using memory_equivalent_loadv | exact NEXT].
Qed.

Theorem assign_loc_memory_equivalent ce ty first second b ofs bf value first' :
  memory_equivalent first second -> assign_loc ce ty first b ofs bf value first' ->
  exists second', assign_loc ce ty second b ofs bf value second' /\ memory_equivalent first' second'.
Proof.
  intros EQ STORE; inversion STORE; subst.
  - destruct (memory_equivalent_storev _ _ _ _ _ _ EQ H0) as [second' [WRITE NEXT]].
    exists second'; split; [econstructor; eauto | exact NEXT].
  - match goal with WRITE : Mem.storebytes _ _ _ _ = Some _ |- _ =>
      destruct (memory_equivalent_storebytes _ _ _ _ _ _ EQ WRITE) as [second' [WRITE' NEXT]] end.
    exists second'; split; [|exact NEXT]. eapply assign_loc_copy; eauto.
    erewrite <- memory_equivalent_loadbytes; eauto.
  - destruct (store_bitfield_memory_equivalent _ _ _ _ _ _ _ _ _ _ _ EQ H) as [second' [WRITE NEXT]].
    exists second'; split; [econstructor; eauto | exact NEXT].
Qed.

Lemma alloc_variables_memory_equivalent ge e first second vars e' first' :
  memory_equivalent first second -> alloc_variables ge e first vars e' first' ->
  exists second', alloc_variables ge e second vars e' second' /\ memory_equivalent first' second'.
Proof.
  intros EQ ALLOC; revert second EQ; induction ALLOC; intros second EQ.
  - exists second; split; [constructor | exact EQ].
  - destruct (memory_equivalent_alloc _ _ _ _ _ _ EQ H) as [middle [ALLOC' NEXT]].
    destruct (IHALLOC _ NEXT) as [second' [REST RESULT]].
    exists second'; split; [econstructor; eauto | exact RESULT].
Qed.

Lemma bind_parameters_memory_equivalent ge e first second params args first' :
  memory_equivalent first second -> bind_parameters ge e first params args first' ->
  exists second', bind_parameters ge e second params args second' /\ memory_equivalent first' second'.
Proof.
  intros EQ BIND; revert second EQ; induction BIND; intros second EQ.
  - exists second; split; [constructor | exact EQ].
  - destruct (assign_loc_memory_equivalent _ _ _ _ _ _ _ _ _ EQ H0) as [middle [WRITE NEXT]].
    destruct (IHBIND _ NEXT) as [second' [REST RESULT]].
    exists second'; split; [econstructor; eauto | exact RESULT].
Qed.

Theorem entry_memory_equivalent temps ge f args first second e le first' :
  memory_equivalent first second -> adapter_entry temps ge f args first e le first' ->
  exists second', adapter_entry temps ge f args second e le second' /\ memory_equivalent first' second'.
Proof.
  intros EQ ENTRY; unfold adapter_entry in *; destruct temps; inversion ENTRY; subst.
  - destruct (alloc_variables_memory_equivalent _ _ _ _ _ _ _ EQ H2) as [second' [ALLOC RESULT]].
    exists second'; split; [econstructor; eauto | exact RESULT].
  - destruct (alloc_variables_memory_equivalent _ _ _ _ _ _ _ EQ H0) as [middle [ALLOC NEXT]].
    destruct (bind_parameters_memory_equivalent _ _ _ _ _ _ _ NEXT H1) as [second' [BIND RESULT]].
    exists second'; split; [econstructor; eauto | exact RESULT].
Qed.

Lemma decision_memory_equivalent ge e le first second tree result :
  memory_equivalent first second -> decision_run (Entry ge e le first) tree result ->
  decision_run (Entry ge e le second) tree result.
Proof.
  intros EQ RUN; induction RUN; [constructor |]. econstructor; [|exact IHRUN].
  destruct H as [v [EV BOOL]]. exists v; split.
  - eapply (proj1 (expressions_memory_equivalent ge e le _ _ EQ)); exact EV.
  - erewrite <- memory_equivalent_bool; eauto.
Qed.

Print Assumptions expressions_memory_equivalent.
Print Assumptions assign_loc_memory_equivalent.
