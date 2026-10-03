From Stdlib Require Import List.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightCondition ClightNoWrap ClightRedundantSet.
From GuardMemory Require Import GuardMemoryControlSettle GuardMemoryRecursiveSource GuardMemoryRecursiveDomain.
Import ListNotations.
Set Implicit Arguments.

Fixpoint memory_recursive_restore nest := match nest with
  | MemorySourceLeaf _ => Sskip
  | MemorySourceAxis iterator bound _ child => Ssequence (memory_recursive_restore child)
      (Sset iterator (Etempvar bound type_int32s)) end.
Lemma memory_recursive_exit_keys nest temps :
  map fst (combine (memory_nest_iterators nest)
    (map (fun bound => Vint (temp_word bound temps)) (memory_nest_bounds nest))) = memory_nest_iterators nest.
Proof. induction nest; cbn; [reflexivity|f_equal; exact IHnest]. Qed.
Theorem memory_recursive_restore_execution fe ge locals nest temps memory : memory_nest_fresh nest ->
  (forall identifier, In identifier (memory_nest_bounds nest) -> register_domain identifier (Entry ge locals temps memory)) ->
  exec_stmt fe ge locals temps memory (memory_recursive_restore nest) E0 (memory_recursive_exit nest temps) memory Out_normal.
Proof.
  induction nest as [code|iterator bound body child IH]; cbn [memory_recursive_restore]; intros FRESH WORDS; [constructor|].
  destruct (memory_nest_fresh_child FRESH) as [CHILD_FRESH [ITERATOR_FRESH [BOUND_FRESH DISTINCT]]].
  destruct (WORDS bound ltac:(cbn; auto)) as [word WORD]; cbn [entry_temps] in WORD.
  change (exec_stmt fe ge locals temps memory
    (Ssequence (memory_recursive_restore child) (Sset iterator (Etempvar bound type_int32s))) E0
    (PTree.set iterator (Vint (temp_word bound temps)) (memory_recursive_exit child temps)) memory Out_normal).
  unfold temp_word at 1; rewrite WORD.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := memory_recursive_exit child temps) (m1 := memory).
  - apply IH; [exact CHILD_FRESH|intros identifier MEMBER; apply WORDS; cbn; auto].
  - constructor; constructor; unfold memory_recursive_exit; rewrite memory_settle_controls_frame.
    + exact WORD.
    + rewrite memory_recursive_exit_keys; exact BOUND_FRESH.
Qed.
Lemma memory_settle_controls_agree assignments live first second : temp_agree live first second ->
  temp_agree live (memory_settle_controls assignments first) (memory_settle_controls assignments second).
Proof.
  intro FRAME; induction assignments as [|[identifier value] assignments IH]; cbn; [exact FRAME|].
  intros key MEMBER; rewrite !PTree.gsspec; destruct (peq key identifier); [reflexivity|apply IH; exact MEMBER].
Qed.
Theorem memory_recursive_exit_frame nest live first second :
  temp_agree (memory_nest_bounds nest++live) first second ->
  temp_agree live (memory_recursive_exit nest first) (memory_recursive_exit nest second).
Proof.
  intro FRAME; unfold memory_recursive_exit.
  assert (WORDS : map (fun bound => Vint (temp_word bound first)) (memory_nest_bounds nest) =
    map (fun bound => Vint (temp_word bound second)) (memory_nest_bounds nest)).
  { apply map_ext_in; intros identifier MEMBER; unfold temp_word.
    rewrite FRAME by (apply in_or_app; left; exact MEMBER); reflexivity. }
  rewrite WORDS; apply memory_settle_controls_agree.
  intros identifier MEMBER; apply FRAME,in_or_app; right; exact MEMBER.
Qed.
Print Assumptions memory_recursive_restore_execution.
