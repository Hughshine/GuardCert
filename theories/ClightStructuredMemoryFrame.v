From Stdlib Require Import List.
From compcert.common Require Import Memory.
From compcert.cfrontend Require Import Clight ClightBigstep.
Set Implicit Arguments.

(** A language service for completed structured execution. It lifts actual
    assignment effects through control flow. It asserts neither termination
    nor guard safety at arbitrary entries. Calls and nonlocal exits are absent. *)
Fixpoint structured_memory_frame (leaf : expr -> expr -> Prop) source : Prop := match source with
| Sskip | Sset _ _ | Sbreak | Scontinue => True
| Sassign target value => leaf target value
| Ssequence first second | Sloop first second =>
    structured_memory_frame leaf first /\ structured_memory_frame leaf second
| Sifthenelse _ first second => structured_memory_frame leaf first /\ structured_memory_frame leaf second
| _ => False end.

Theorem structured_memory_frame_execution ge
  (leaf : expr -> expr -> Prop) (relation : env -> mem -> mem -> Prop) :
  (forall locals memory, relation locals memory memory) ->
  (forall locals before middle final,
    relation locals before middle -> relation locals middle final -> relation locals before final) ->
  (forall fe locals temps memory left right trace after final outcome,
    leaf left right -> exec_stmt fe ge locals temps memory (Sassign left right) trace after final outcome ->
    relation locals memory final) ->
  forall fe locals temps memory source trace after final outcome,
    exec_stmt fe ge locals temps memory source trace after final outcome ->
    structured_memory_frame leaf source -> relation locals memory final.
Proof.
  intros REFL TRANS LEAF fe locals temps memory source trace after final outcome RUN.
  induction RUN; intro FRAME; cbn [structured_memory_frame] in FRAME; try contradiction; try apply REFL.
  - eapply LEAF with (fe:=fe); [exact FRAME|econstructor; eassumption].
  - destruct FRAME as [FIRST SECOND]; eapply TRANS; [apply IHRUN1; exact FIRST|apply IHRUN2; exact SECOND].
  - apply IHRUN; exact (proj1 FRAME).
  - apply IHRUN; destruct b; [exact (proj1 FRAME)|exact (proj2 FRAME)].
  - apply IHRUN; exact (proj1 FRAME).
  - destruct FRAME as [FIRST SECOND]; eapply TRANS; [apply IHRUN1; exact FIRST|apply IHRUN2; exact SECOND].
  - eapply TRANS; [apply IHRUN1; exact (proj1 FRAME)|].
    eapply TRANS; [apply IHRUN2; exact (proj2 FRAME)|apply IHRUN3; exact FRAME].
Qed.

Print Assumptions structured_memory_frame_execution.
