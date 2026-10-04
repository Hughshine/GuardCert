From Stdlib Require Import List Arith Bool ZArith.
From GuardMemory Require Import GuardMemoryPolyhedral GuardMemoryPolyhedralRectangles
  GuardMemorySequencePolyhedral GuardMemoryPointIsomorphism.
Import ListNotations.
Set Implicit Arguments.

Fixpoint affine_site_swap {A} position (items:list A) : option(list A) :=
  match position,items with
  | O,first::second::rest=>Some(second::first::rest)
  | S previous,first::rest=>match affine_site_swap previous rest with
      Some swapped=>Some(first::swapped)|None=>None end
  | _,_=>None end.
Fixpoint affine_site_swap_index position site := match position,site with
  | O,O=>1%nat | O,S O=>O | O,S(S rest)=>S(S rest)
  | S _,O=>O | S previous,S index=>S(affine_site_swap_index previous index) end.
Lemma affine_site_swap_index_inverse position site :
  affine_site_swap_index position(affine_site_swap_index position site)=site.
Proof.
  revert site; induction position; intro site; [destruct site as [|[|site]]; reflexivity|].
  destruct site; cbn; [reflexivity|rewrite IHposition; reflexivity].
Qed.
Lemma affine_site_swap_lookup {A} position (source target:list A) site item :
  affine_site_swap position source=Some target -> nth_error source site=Some item ->
  nth_error target(affine_site_swap_index position site)=Some item.
Proof.
  revert source target site; induction position; intros source target site SWAP LOOKUP.
  - destruct source as [|first [|second rest]]; try discriminate.
    inversion SWAP; subst target; destruct site as [|[|site]]; cbn in *; assumption.
  - destruct source as [|first rest]; [discriminate|]; cbn in SWAP.
    destruct(affine_site_swap position rest) as [swapped|] eqn:REST; [|discriminate].
    inversion SWAP; subst target; destruct site; cbn in *; [exact LOOKUP|eapply IHposition; eassumption].
Qed.
Definition affine_site_swap_point position (point:PL.InstrPoint) : PL.InstrPoint :=
  {| PL.ILSema.ip_nth:=affine_site_swap_index position(PL.ILSema.ip_nth point);
     PL.ILSema.ip_index:=PL.ILSema.ip_index point;
     PL.ILSema.ip_transformation:=PL.ILSema.ip_transformation point;
     PL.ILSema.ip_time_stamp:=PL.ILSema.ip_time_stamp point;
     PL.ILSema.ip_instruction:=PL.ILSema.ip_instruction point;
     PL.ILSema.ip_depth:=PL.ILSema.ip_depth point |}.
Lemma affine_site_swap_point_inverse position point :
  affine_site_swap_point position(affine_site_swap_point position point)=point.
Proof. destruct point; unfold affine_site_swap_point; cbn; rewrite affine_site_swap_index_inverse; reflexivity. Qed.
Lemma affine_site_swap_reverse {A} position (source target:list A) :
  affine_site_swap position source=Some target -> affine_site_swap position target=Some source.
Proof.
  revert source target; induction position; intros source target SWAP.
  - destruct source as [|first [|second rest]]; try discriminate; inversion SWAP; reflexivity.
  - destruct source as [|first rest]; [discriminate|]; cbn in SWAP.
    destruct(affine_site_swap position rest) as [swapped|] eqn:REST; [|discriminate].
    inversion SWAP; subst target; cbn; rewrite(IHposition rest swapped REST); reflexivity.
Qed.
Lemma affine_site_swap_valid parameters position source target point :
  affine_site_swap position source=Some target -> memory_sequence_valid_point parameters source point ->
  memory_sequence_valid_point parameters target(affine_site_swap_point position point).
Proof.
  intros SWAP [instruction [LOOKUP [PREFIX [BELONG WIDTH]]]].
  exists instruction; split; [eapply affine_site_swap_lookup; eassumption|].
  split; [exact PREFIX|]; split; [|exact WIDTH].
  unfold PL.belongs_to,affine_site_swap_point; cbn; exact BELONG.
Qed.
Definition affine_site_swap_isomorphism parameters position source target
  (SWAP:affine_site_swap position source=Some target) : memory_point_isomorphism parameters source target.
Proof.
  refine {| point_forward:=affine_site_swap_point position;point_backward:=affine_site_swap_point position |}.
  - intros; eapply affine_site_swap_valid; eassumption.
  - intros; eapply affine_site_swap_valid; [eapply affine_site_swap_reverse; exact SWAP|eassumption].
  - intros; apply affine_site_swap_point_inverse.
  - intros; apply affine_site_swap_point_inverse.
  - reflexivity.
  - reflexivity.
  - intros point initial final VALID RUN; destruct point; inversion RUN; econstructor; eassumption.
  - intros point initial final VALID RUN; destruct point; inversion RUN; econstructor; eassumption.
Defined.
Theorem affine_site_swap_execution parameters position source target context variables initial final :
  affine_site_swap position source=Some target ->
  (PL.poly_instance_list_semantics parameters(source,context,variables) initial final <->
   PL.poly_instance_list_semantics parameters(target,context,variables) initial final).
Proof.
  intro SWAP; apply memory_point_isomorphism_execution;
    exact(@affine_site_swap_isomorphism parameters position source target SWAP).
Qed.
Print Assumptions affine_site_swap_execution.
