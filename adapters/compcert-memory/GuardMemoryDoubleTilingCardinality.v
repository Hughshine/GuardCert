From Stdlib Require Import List Lia.
From GuardMemory Require Import GuardMemoryDoubleExtractedTiling.
Import ListNotations.
Set Implicit Arguments.

(** The existing final tiling attachment is a positional correspondence. This
    necessary condition exposes its limit before any dependence oracle runs. *)
Theorem double_tiling_attachment_cardinality dimension before candidate witnesses attached :
  double_attach_tiling_instructions dimension before candidate witnesses = Some attached ->
  length before = length candidate /\ length before = length witnesses.
Proof.
  revert candidate witnesses attached.
  induction before as [|old olds IH]; intros [|next nexts] [|witness rest] attached;
    cbn; try discriminate.
  - intros; auto.
  - destruct (double_attach_tiling_instructions dimension olds nexts rest) as [tail|] eqn:TAIL;
      [|discriminate].
    intro; destruct (IH _ _ _ TAIL); cbn; auto.
Qed.

Corollary double_tiling_attachment_refuses_split dimension before candidate witnesses :
  length before <> length candidate ->
  double_attach_tiling_instructions dimension before candidate witnesses = None.
Proof.
  intro DIFFERENT.
  destruct (double_attach_tiling_instructions dimension before candidate witnesses) as [attached|] eqn:ATTACH;
    [|reflexivity].
  exfalso; apply DIFFERENT;
    exact (proj1 (@double_tiling_attachment_cardinality dimension before candidate witnesses attached ATTACH)).
Qed.

Print Assumptions double_tiling_attachment_cardinality.
Print Assumptions double_tiling_attachment_refuses_split.
