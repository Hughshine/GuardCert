From Stdlib Require Import List ZArith.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryRectangles GuardMemoryNaryCompute GuardMemoryNaryLoops GuardMemoryScalarLoops GuardMemoryScalarContextTail.
Import ListNotations.
Set Implicit Arguments.

(** Affine child bounds do not occupy the constant-count slots used by the
    rectangular representation. Arguments are source-order coordinates,
    followed by the actual stable context; extra metadata is not a payload. *)
Definition affine_leaf_arguments dimensions parameters :=
  memory_nary_arguments dimensions++memory_variables_from dimensions parameters.

Lemma affine_leaf_arguments_value coordinates parameters tail :
  map (L.eval_expr (rev coordinates++parameters++tail))
    (affine_leaf_arguments (length coordinates) (length parameters))=coordinates++parameters.
Proof.
  unfold affine_leaf_arguments; rewrite map_app,memory_nary_arguments_value.
  rewrite <-(length_rev coordinates) at 1.
  rewrite memory_variables_from_prefix; reflexivity.
Qed.

Fixpoint affine_leaf_sequence dimensions parameters instructions : L.stmt_list := match instructions with
  | [] => L.SNil
  | instruction::rest => L.SCons (L.Instr instruction (affine_leaf_arguments dimensions parameters))
      (affine_leaf_sequence dimensions parameters rest) end.

Theorem affine_leaf_instruction_semantics instruction coordinates parameters tail before after :
  L.loop_semantics (L.Instr instruction (affine_leaf_arguments (length coordinates) (length parameters)))
    (rev coordinates++parameters++tail) before after <->
  memory_nary_point instruction (coordinates++parameters) before after.
Proof.
  split; intro RUN.
  - inversion RUN as [inst args environment first final writes reads EXEC| | | | | ]; subst.
    rewrite affine_leaf_arguments_value in EXEC.
    change (GuardMemoryInstr.instr_semantics instruction (coordinates++parameters) writes reads before after) in EXEC.
    destruct EXEC as [WRITES [READS ACTION]]; subst; repeat split; assumption || reflexivity.
  - apply L.LInstr with (wcs:=memory_write_cells instruction (coordinates++parameters))
      (rcs:=memory_read_cells instruction (coordinates++parameters)).
    rewrite affine_leaf_arguments_value; exact RUN.
Qed.

Theorem affine_leaf_sequence_semantics instructions coordinates parameters tail before after :
  L.loop_semantics (L.Seq (affine_leaf_sequence (length coordinates) (length parameters) instructions))
    (rev coordinates++parameters++tail) before after <->
  memory_nary_sequence_point instructions (coordinates++parameters) before after.
Proof.
  unfold memory_nary_sequence_point; revert before after; induction instructions; intros before after;
    cbn [affine_leaf_sequence]; split; intro RUN.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; econstructor.
    + apply(proj1(@affine_leaf_instruction_semantics a coordinates parameters tail before _)); eassumption.
    + apply IHinstructions; eassumption.
  - inversion RUN; subst; eapply L.LSeq.
    + apply(proj2(@affine_leaf_instruction_semantics a coordinates parameters tail before _)); eassumption.
    + apply IHinstructions; eassumption.
Qed.
Print Assumptions affine_leaf_arguments_value.
Print Assumptions affine_leaf_instruction_semantics.
Print Assumptions affine_leaf_sequence_semantics.
