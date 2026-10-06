From Stdlib Require Import List.
From compcert.lib Require Import Coqlib.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryAffineSourceExpressions
  GuardMemoryAffineSourceLoop GuardMemoryAffineSourceEndpoints.
Set Implicit Arguments.

(** A checked source encoding guarantees that its parameters can also be
    encoded at an arbitrary row endpoint in the same context. *)
Theorem memory_source_loop_endpoint_encoding expression row context encoded :
  memory_source_loop_expression row context expression = Some encoded ->
  forall point, exists endpoint,
    memory_source_endpoint_expression row context point expression = Some endpoint.
Proof.
  revert encoded; induction expression; intros encoded ENCODE point;
    cbn [memory_source_loop_expression] in ENCODE;
    cbn [memory_source_endpoint_expression].
  - destruct (peq identifier row); [eexists; reflexivity|].
    destruct (memory_source_position identifier context) as [position|];
      cbn in ENCODE; [eexists; reflexivity|discriminate].
  - eexists; reflexivity.
  - destruct (memory_source_loop_expression row context expression1) as [first|] eqn:FIRST; [|discriminate].
    destruct (memory_source_loop_expression row context expression2) as [second|] eqn:SECOND; [|discriminate].
    destruct (IHexpression1 _ eq_refl point) as [a A], (IHexpression2 _ eq_refl point) as [b B].
    rewrite A,B; eexists; reflexivity.
  - destruct (memory_source_loop_expression row context expression1) as [first|] eqn:FIRST; [|discriminate].
    destruct (memory_source_loop_expression row context expression2) as [second|] eqn:SECOND; [|discriminate].
    destruct (IHexpression1 _ eq_refl point) as [a A], (IHexpression2 _ eq_refl point) as [b B].
    rewrite A,B; eexists; reflexivity.
  - destruct (memory_source_loop_expression row context expression) as [first|] eqn:FIRST; [|discriminate].
    destruct (IHexpression _ eq_refl point) as [a A]; rewrite A; eexists; reflexivity.
  - destruct (memory_source_loop_expression row context expression) as [first|] eqn:FIRST; [|discriminate].
    destruct (IHexpression _ eq_refl point) as [a A]; rewrite A; eexists; reflexivity.
Qed.
Print Assumptions memory_source_loop_endpoint_encoding.
