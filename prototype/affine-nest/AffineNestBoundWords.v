From Stdlib Require Import List.
From compcert.lib Require Import Maps.
From compcert.common Require Import Values.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestFirstDomain
  AffineNestFirstLeaf AffineNestSourceDecode.
Import ListNotations.
Set Implicit Arguments.

Fixpoint affine_tail_bound_reads nest := match nest with
  | AffineSourceLeaf _ => []
  | AffineSourceAxis _ _ _ _ child => match child with
      | AffineSourceLeaf _ => []
      | AffineSourceAxis _ _ expression _ _ =>
          memory_source_affine_reads expression++affine_tail_bound_reads child end end.

(** Definition of a stable bound parameter follows from the actual first
    source headers, including their activity conditions. It is not inferred
    from an interval proposal. The root bound is handled by its own header. *)
Theorem affine_first_headers_used_bound_word nest : forall temps identifier,
  affine_first_header_domain nest temps -> affine_first_path_active nest temps ->
  ~In identifier(affine_nest_mutated nest) -> In identifier(affine_tail_bound_reads nest) ->
  exists word,temps!identifier=Some(Vint word).
Proof.
  induction nest as [source|iterator bound expression body child IH];
    intros temps identifier DOMAIN ACTIVE PROTECTED MEMBER; [contradiction|].
  destruct DOMAIN as [ITERATOR [BOUND DOMAIN]]; destruct ACTIVE as [ROOT_ACTIVE CHILD_ACTIVE].
  specialize(DOMAIN ROOT_ACTIVE).
  destruct child as [leaf|child_iterator child_bound child_expression child_body grandchild];
    [contradiction|].
  destruct DOMAIN as [WORDS CHILD_DOMAIN].
  cbn [affine_tail_bound_reads] in MEMBER; apply in_app_or in MEMBER.
  destruct MEMBER as [MEMBER|MEMBER]; [apply WORDS; exact MEMBER|].
  assert (CHILD_PROTECTED:~In identifier(affine_nest_mutated
    (AffineSourceAxis child_iterator child_bound child_expression child_body grandchild))).
  { intro BAD; apply PROTECTED; cbn [affine_nest_mutated affine_nest_controls List.In] in *; tauto. }
  destruct (IH _ _ CHILD_DOMAIN CHILD_ACTIVE CHILD_PROTECTED MEMBER) as [word WORD].
  exists word; cbn [affine_first_child_temps] in WORD.
  rewrite PTree.gso in WORD.
  - rewrite PTree.gso in WORD; [exact WORD|].
    intro SAME; subst; apply PROTECTED; cbn [affine_nest_mutated affine_nest_controls List.In]; auto.
  - intro SAME; subst; apply PROTECTED; cbn [affine_nest_mutated affine_nest_controls List.In]; auto.
Qed.
Print Assumptions affine_first_headers_used_bound_word.
