From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightRedundantSet.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestFirstDomain.
Import ListNotations.
Set Implicit Arguments.

Definition affine_words_defined identifiers (temps : temp_env) :=
  forall id, In id identifiers -> exists word, temps!id=Some(Vint word).
Lemma affine_defined_word_set identifiers temps id word :
  affine_words_defined identifiers temps -> affine_words_defined identifiers (PTree.set id (Vint word) temps).
Proof.
  intros WORDS key MEMBER; destruct (peq id key) as [SAME|OTHER].
  - subst key; exists word; apply PTree.gss.
  - destruct (WORDS key MEMBER) as [value VALUE]; exists value; rewrite PTree.gso by congruence; exact VALUE.
Qed.

(** A captured parameter environment permits private header probing. The
    probe initializes future controls itself; no cached-source execution or
    leaf completion is a premise of this numeric-domain service. *)
Theorem affine_defined_parameters_first_headers nest prefix parameters temps :
  affine_nest_bound_dependencies prefix parameters nest ->
  affine_words_defined (prefix++parameters) temps ->
  (match nest with
   | AffineSourceLeaf _ => True
   | AffineSourceAxis iterator bound _ _ _ =>
       (exists word,temps!iterator=Some(Vint word)) /\ (exists word,temps!bound=Some(Vint word))
   end) ->
  affine_first_header_domain nest temps.
Proof.
  revert prefix temps; induction nest as [leaf|iterator bound expression body child IH];
    intros prefix temps DEPENDENCIES WORDS ROOT; [exact I|].
  destruct DEPENDENCIES as [READS CHILD]; destruct ROOT as [ITERATOR BOUND].
  cbn [affine_first_header_domain]; split; [exact ITERATOR|split; [exact BOUND|]].
  intro ACTIVE; destruct child as [leaf|child_iterator child_bound child_expression child_body child]; [exact I|].
  destruct CHILD as [CHILD_READS REST].
  assert (CHILD_WORDS : affine_words_defined ((prefix++[iterator])++parameters) temps).
  { intros id MEMBER; repeat rewrite in_app_iff in MEMBER; cbn in MEMBER.
    destruct MEMBER as [[OLD|[SAME|BAD]]|PARAMETER].
    - apply WORDS,in_or_app; left; exact OLD.
    - subst id; exact ITERATOR.
    - contradiction.
    - apply WORDS,in_or_app; right; exact PARAMETER. }
  split.
  - intros id MEMBER; apply CHILD_WORDS,CHILD_READS; exact MEMBER.
  - apply IH with (prefix:=prefix++[iterator]); [split; assumption| |].
    + apply affine_defined_word_set,affine_defined_word_set; exact CHILD_WORDS.
    + split; [exists Int.zero; apply PTree.gss|].
      destruct (peq child_iterator child_bound) as [SAME|OTHER].
      * subst child_bound; exists Int.zero; apply PTree.gss.
      * eexists; rewrite PTree.gso by congruence; apply PTree.gss.
Qed.

Corollary affine_captured_parameters_first_headers iterator bound expression body child parameters temps :
  affine_nest_bound_dependencies [] parameters (AffineSourceAxis iterator bound expression body child) ->
  affine_words_defined parameters temps ->
  (exists word,temps!iterator=Some(Vint word)) -> (exists word,temps!bound=Some(Vint word)) ->
  affine_first_header_domain (AffineSourceAxis iterator bound expression body child) temps.
Proof. intros DEPS WORDS ROW BOUND; eapply affine_defined_parameters_first_headers; [exact DEPS|exact WORDS|split; assumption]. Qed.

Print Assumptions affine_defined_word_set.
Print Assumptions affine_defined_parameters_first_headers.
Print Assumptions affine_captured_parameters_first_headers.
