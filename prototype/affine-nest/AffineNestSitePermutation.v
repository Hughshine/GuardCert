From Stdlib Require Import List ZArith.
From GuardMemory Require Import GuardMemoryPolyhedral GuardMemoryPolyhedralRectangles GuardMemoryPointIsomorphism.
From GuardAffineNest Require Import AffineNestSiteSwap.
Import ListNotations.
Set Implicit Arguments.

Fixpoint affine_site_permutation {A} (positions:list nat)(source:list A) : option(list A) :=
  match positions with
  | []=>Some source
  | position::rest=>match affine_site_swap position source with
      Some next=>affine_site_permutation rest next|None=>None end end.
Theorem affine_site_permutation_execution parameters positions source target context variables initial final :
  affine_site_permutation positions source=Some target ->
  (PL.poly_instance_list_semantics parameters(source,context,variables) initial final <->
   PL.poly_instance_list_semantics parameters(target,context,variables) initial final).
Proof.
  revert source target; induction positions; intros source target CHECK; cbn in CHECK.
  - inversion CHECK; reflexivity.
  - destruct(affine_site_swap a source) as [next|] eqn:SWAP; [|discriminate].
    rewrite(@affine_site_swap_execution parameters a source next context variables initial final SWAP).
    apply IHpositions; exact CHECK.
Qed.
Print Assumptions affine_site_permutation_execution.
