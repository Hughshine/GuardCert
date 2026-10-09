From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightCountedLoop.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleMatmulExit
  GuardMemoryDoubleRectangularNestData.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Capture accepts only positive counts. Restore every reached public I64
    iterator from its own private I32 parameter; no equality of bounds is used. *)
Fixpoint double_rectangular_exit_code iterators caches : statement :=
  match iterators,caches with
  | iterator::iterators,cache::caches=>Ssequence (double_rectangular_exit_code iterators caches)
      (Sset iterator (double_cached_long cache))
  | _,_=>Sskip end.
Theorem double_rectangular_exit_code_execution iterators : forall caches counts fe ge locals temps memory,
  length iterators=length caches ->
  (forall cache, In cache caches -> ~ In cache iterators) ->
  Forall2 (fun cache count => 0<Z.of_nat count /\ signed_range (Z.of_nat count) /\
    temps ! cache=Some (Vint (Int.repr (Z.of_nat count)))) caches counts ->
  exec_stmt fe ge locals temps memory (double_rectangular_exit_code iterators caches) E0
    (double_rectangular_nest_exit iterators counts temps) memory Out_normal.
Proof.
  induction iterators as [|iterator iterators IH]; intros caches counts fe ge locals temps memory LENGTH FRESH WORDS.
  - destruct caches as [|cache caches]; cbn [length] in LENGTH; [|discriminate].
    inversion WORDS; subst counts; constructor.
  - destruct caches as [|cache caches]; cbn [length] in LENGTH; [discriminate|].
    inversion WORDS as [|cache' count caches' counts' FACT REST]; subst cache' caches' counts.
    destruct FACT as [POSITIVE [RANGE WORD]].
    destruct count as [|count]; [cbn in POSITIVE; lia|].
    cbn [double_rectangular_exit_code]; rewrite double_rectangular_nest_exit_cons.
    eapply exec_Sseq_1 with (le1:=double_rectangular_nest_exit iterators counts' temps)
      (m1:=memory) (t1:=E0) (t2:=E0).
    + apply IH; [lia| |exact REST].
      intros key MEMBER WRITTEN; apply (FRESH key ltac:(right; exact MEMBER)); right; exact WRITTEN.
    + apply exec_Sset,double_cached_long_execution; [exact RANGE|].
      rewrite double_rectangular_nest_exit_frame; [exact WORD|].
      intro MEMBER; apply (FRESH cache ltac:(left; reflexivity)); right; exact MEMBER.
Qed.
Theorem double_rectangular_exit_agree iterators counts live before after :
  temp_agree live before after -> temp_agree live
    (double_rectangular_nest_exit iterators counts before) (double_rectangular_nest_exit iterators counts after).
Proof.
  intros FRAME key MEMBER; unfold double_rectangular_nest_exit.
  rewrite !double_rectangular_set_assignments_lookup.
  destruct (double_rectangular_assignment_value (double_rectangular_exit_assignments iterators counts) key);
    [reflexivity|apply FRAME; exact MEMBER].
Qed.

Print Assumptions double_rectangular_exit_code_execution.
Print Assumptions double_rectangular_exit_agree.
