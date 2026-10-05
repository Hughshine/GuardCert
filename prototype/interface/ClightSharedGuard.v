From Stdlib Require Import Bool List.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr.
From GuardInterface Require Import ClightReadonlyRewrite.
Import ListNotations.
Set Implicit Arguments.

(** Materialization is a compiler implementation of the original pure tree.
    It writes one compiler-private Boolean only after the last test. The
    source, candidate, original temps, memory and events are unchanged. *)
Definition shared_guard_word (accepted : bool) := if accepted then Int.one else Int.zero.
Definition shared_guard_code tree result :=
  tree_statement tree (Sset result (Econst_int Int.one type_int32s))
    (Sset result (Econst_int Int.zero type_int32s)).
Definition shared_guard_choice result := Etempvar result type_int32s.
Definition shared_guard_statement tree result yes no :=
  Ssequence (shared_guard_code tree result) (Sifthenelse (shared_guard_choice result) yes no).

Lemma shared_guard_execution fe ge locals temps memory tree result accepted :
  decision_run (Entry ge locals temps memory) tree accepted ->
  exec_stmt fe ge locals temps memory (shared_guard_code tree result) E0
    (PTree.set result (Vint (shared_guard_word accepted)) temps) memory Out_normal.
Proof.
  intro CHECK; unfold shared_guard_code; eapply decision_fragment_run; [exact CHECK|].
  destruct accepted; constructor; constructor.
Qed.

Lemma shared_guard_choice_test ge locals temps memory result accepted :
  temps ! result = Some (Vint (shared_guard_word accepted)) ->
  expression_test (shared_guard_choice result) (Entry ge locals temps memory) accepted.
Proof.
  intro LOOKUP; exists (Vint (shared_guard_word accepted)); split; [constructor; exact LOOKUP|].
  destruct accepted; reflexivity.
Qed.

Lemma shared_guard_selected fe ge locals temps memory tree result accepted trace after final outcome yes no :
  decision_run (Entry ge locals temps memory) tree accepted ->
  exec_stmt fe ge locals (PTree.set result (Vint (shared_guard_word accepted)) temps) memory
    (if accepted then yes else no) trace after final outcome ->
  exec_stmt fe ge locals temps memory (shared_guard_statement tree result yes no) trace after final outcome.
Proof.
  intros CHECK LEAF; unfold shared_guard_statement.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := trace); [eapply shared_guard_execution; exact CHECK|].
  unfold shared_guard_choice; eapply exec_Sifthenelse with (v1 := Vint (shared_guard_word accepted)) (b := accepted).
  - constructor; apply PTree.gss.
  - destruct accepted; reflexivity.
  - exact LEAF.
Qed.
Print Assumptions shared_guard_execution.
Print Assumptions shared_guard_choice_test.
Print Assumptions shared_guard_selected.
