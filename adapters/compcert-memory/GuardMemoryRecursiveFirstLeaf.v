From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame ClightLoopSyntax ClightRegionProgress ClightNoWrap ClightCondition.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryTripleWords.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A successful positive source loop provides a real first leaf execution.
    No array base, pointer validity, or leaf instruction meaning is assumed. *)
Theorem memory_recursive_first_leaf fe ge locals nest :
  memory_nest_shapes nest -> memory_nest_fresh nest ->
  normal_statement (memory_nest_leaf nest) = true -> quiet_statement (memory_nest_leaf nest) = true ->
  writes_only [] (memory_nest_leaf nest) ->
  forall protected temps memory after final,
    (forall identifier, In identifier (memory_nest_iterators nest) -> ~ In identifier protected) ->
    Forall (fun bound => 0 < Int.signed (temp_word bound temps)) (memory_nest_bounds nest) ->
    memory_nest_initial nest temps ->
    exec_stmt fe ge locals temps memory (memory_nest_source nest) E0 after final Out_normal ->
    exists leaf_temps leaf_after leaf_final, temp_agree protected temps leaf_temps /\
      exec_stmt fe ge locals leaf_temps memory (memory_nest_leaf nest) E0 leaf_after leaf_final Out_normal.
Proof.
  induction nest as [code|iterator bound body child IH];
    intros SHAPES FRESH NORMAL QUIET WRITES protected temps memory after final PROTECTED POSITIVE INITIAL SOURCE.
  - exists temps,after,final; split; [apply temp_agree_refl|exact SOURCE].
  - destruct (memory_nest_fresh_child FRESH) as [CHILD_FRESH [ITERATOR_FRESH [BOUND_FRESH DISTINCT]]].
    inversion POSITIVE as [|same tail HEAD TAIL]; subst same tail.
    destruct (@memory_frontend_positive_body fe ge locals iterator bound body (memory_nest_iterators child)
      temps memory after final (@memory_nest_body_normal iterator bound body child SHAPES NORMAL QUIET)
      (@memory_nest_body_writes iterator bound body child SHAPES WRITES)
      ITERATOR_FRESH BOUND_FRESH INITIAL HEAD SOURCE) as [next [target BODY]].
    pose proof (@memory_nest_child_decode fe ge locals body child temps memory next target (proj1 SHAPES) BODY) as CHILD.
    assert (CHILD_PROTECTED : forall identifier, In identifier (memory_nest_iterators child) -> ~ In identifier protected).
    { intros identifier MEMBER; apply PROTECTED; cbn; auto. }
    assert (CHILD_POSITIVE : Forall (fun key => 0 < Int.signed (temp_word key (memory_nest_child_temps child temps)))
      (memory_nest_bounds child)).
    { rewrite Forall_forall in TAIL |- *; intros key MEMBER.
      pose proof (@memory_nest_child_frame child temps (memory_nest_bounds child) (proj2 CHILD_FRESH)) as FRAME.
      unfold temp_word; rewrite (FRAME key MEMBER); apply TAIL; exact MEMBER. }
    destruct (IH (proj2 SHAPES) CHILD_FRESH NORMAL QUIET WRITES protected
      (memory_nest_child_temps child temps) memory next target CHILD_PROTECTED CHILD_POSITIVE
      (memory_nest_child_initial child temps) CHILD) as [leaf_temps [leaf_after [leaf_final [FRAME RUN]]]].
    exists leaf_temps,leaf_after,leaf_final; split; [|exact RUN].
    eapply temp_agree_trans; [apply memory_nest_child_frame; exact CHILD_PROTECTED|exact FRAME].
Qed.
Print Assumptions memory_recursive_first_leaf.
