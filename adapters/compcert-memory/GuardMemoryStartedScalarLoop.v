From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Misc.
From Guard Require Import ClightCountedLoop RectangularIteration.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles
  GuardMemoryPolyhedral GuardMemoryLoops GuardMemoryNaryCompute GuardMemoryNaryLoops GuardMemoryScalarLoops.
From GuardMemory Require Import GuardMemoryScalarContextTail.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The extra context slot is a loop-bound parameter.  Instructions receive
    only the original coordinates and scalar/address arguments. *)
Definition memory_started_scalar_loop dimensions scalars instructions :=
  L.Loop (L.Var (dimensions+scalars)%nat) (L.Var O)
    (memory_scalar_rectangle 1 (Nat.pred dimensions) scalars instructions).

Theorem memory_started_scalar_loop_iterations upper counts instructions values start count before after :
  Z.of_nat upper = start + Z.of_nat count ->
  (L.loop_semantics (memory_started_scalar_loop (S (length counts)) (length values) instructions)
    (map Z.of_nat (upper::counts)++values++[start]) before after <->
   counted_iterations (fun x => memory_nary_iterations
     (fun coordinates => memory_scalar_sequence_point instructions coordinates values) counts [x])
     count start before after).
Proof.
  intro SPAN.
  set (parameters := map Z.of_nat (upper::counts)++values++[start]).
  assert (LOWER : nth (S (length counts)+length values)%nat parameters 0 = start).
  { unfold parameters.
    replace (S (length counts)+length values)%nat with (length (map Z.of_nat (upper::counts)++values))
      by (rewrite length_app,length_map; cbn; lia).
    rewrite app_assoc; apply nth_middle. }
  assert (UPPER : nth O parameters 0 = Z.of_nat upper) by (unfold parameters; reflexivity).
  assert (CHILD : forall x first final,
    L.loop_semantics (memory_scalar_rectangle 1 (length counts) (length values) instructions)
      (x::parameters) first final <->
    memory_nary_iterations (fun coordinates => memory_scalar_sequence_point instructions coordinates values)
      counts [x] first final).
  { intros x first final.
    pose proof (@memory_scalar_rectangle_iterations_tail counts instructions values [start] [x] [upper]
      first final eq_refl) as CHILD.
    cbn [length rev map app] in CHILD; unfold parameters; exact CHILD. }
  unfold memory_started_scalar_loop; cbn [Nat.pred].
  split; intro RUN.
  - inversion RUN as [| | | | | env' lower upper' code first final ITER]; subst env' lower upper' code first final.
    change (Iter.iter_semantics (fun x => L.loop_semantics
      (memory_scalar_rectangle 1 (length counts) (length values) instructions) (x::parameters))
      (Zrange (nth (S (length counts)+length values)%nat parameters 0) (nth O parameters 0)) before after) in ITER.
    rewrite LOWER,UPPER in ITER.
    apply (proj1 (@memory_range_iterations count _ start (Z.of_nat upper) before after SPAN)) in ITER.
    eapply counted_iterations_map; [|exact ITER]; intros x first final STEP; apply CHILD; exact STEP.
  - apply L.LLoop.
    change (Iter.iter_semantics (fun x => L.loop_semantics
      (memory_scalar_rectangle 1 (length counts) (length values) instructions) (x::parameters))
      (Zrange (nth (S (length counts)+length values)%nat parameters 0) (nth O parameters 0)) before after).
    rewrite LOWER,UPPER.
    apply (proj2 (@memory_range_iterations count _ start (Z.of_nat upper) before after SPAN)).
    eapply counted_iterations_map; [|exact RUN]; intros x first final STEP; apply CHILD; exact STEP.
Qed.
Print Assumptions memory_started_scalar_loop_iterations.
