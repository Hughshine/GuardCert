From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep Ctypes Cop.
From Guard Require Import ClightNoWrap ClightTempFrame.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax.
Import ListNotations.
Set Implicit Arguments.

Fixpoint affine_nest_controls nest := match nest with
  | AffineSourceLeaf _ => []
  | AffineSourceAxis iterator bound _ _ child => iterator::bound::affine_nest_controls child end.
Lemma affine_nest_controls_member nest identifier :
  In identifier (affine_nest_controls nest) <->
  In identifier (affine_nest_iterators nest) \/ In identifier (affine_nest_bounds nest).
Proof. induction nest; cbn; [tauto|rewrite IHnest; tauto]. Qed.
Lemma affine_nest_fresh_controls nest : affine_nest_fresh nest -> NoDup (affine_nest_controls nest).
Proof.
  induction nest; cbn [affine_nest_fresh affine_nest_iterators affine_nest_bounds affine_nest_controls];
    intro UNIQUE; [constructor|].
  inversion UNIQUE as [|first rest ITERATOR_FRESH TAIL]; subst.
  pose proof (@NoDup_remove_1 _ (affine_nest_iterators nest) (affine_nest_bounds nest) bound TAIL) as CHILD_FRESH.
  pose proof (@NoDup_remove_2 _ (affine_nest_iterators nest) (affine_nest_bounds nest) bound TAIL) as BOUND_FRESH.
  constructor.
  - cbn; intros [SAME|MEMBER]; apply ITERATOR_FRESH.
    + subst; apply in_or_app; right; cbn; auto.
    + apply affine_nest_controls_member in MEMBER; apply in_or_app; destruct MEMBER as [MEMBER|MEMBER].
      * left; exact MEMBER.
      * right; cbn; auto.
  - constructor; [|apply IHnest; exact CHILD_FRESH].
    intro MEMBER; apply affine_nest_controls_member in MEMBER; apply BOUND_FRESH,in_or_app; exact MEMBER.
Qed.

Fixpoint affine_exit_statement nest := match nest with
  | AffineSourceLeaf _ => Sskip
  | AffineSourceAxis iterator bound _ _ child =>
      Ssequence (Sset iterator (Ebinop Osub (Etempvar bound type_int32s)
        (Econst_int Int.one type_int32s) type_int32s))
      (Ssequence (match child with
        | AffineSourceLeaf _ => Sskip
        | AffineSourceAxis _ child_bound expression _ _ =>
            Ssequence (Sset child_bound (memory_source_affine_code expression)) (affine_exit_statement child) end)
        (Sset iterator (Etempvar bound type_int32s))) end.

Definition affine_word_valuation temps identifier := Int.signed (temp_word identifier temps).
Fixpoint affine_exit_temps nest temps := match nest with
  | AffineSourceLeaf _ => temps
  | AffineSourceAxis iterator bound _ _ child =>
      let upper := temp_word bound temps in
      let last := PTree.set iterator (Vint (Int.sub upper Int.one)) temps in
      let settled := match child with
        | AffineSourceLeaf _ => last
        | AffineSourceAxis _ child_bound expression _ _ =>
            affine_exit_temps child (PTree.set child_bound
              (Vint (Int.repr (memory_source_affine_math (affine_word_valuation last) expression))) last) end in
      PTree.set iterator (Vint upper) settled end.

Lemma affine_exit_temps_other nest temps identifier :
  ~ In identifier (affine_nest_controls nest) -> (affine_exit_temps nest temps)!identifier=temps!identifier.
Proof.
  revert temps; induction nest; intros temps FRESH; cbn; [reflexivity|].
  assert (NOT_ITERATOR : identifier <> iterator) by (intro SAME; subst; apply FRESH; cbn; auto).
  assert (NOT_CHILD : ~ In identifier (affine_nest_controls nest)) by (intro MEMBER; apply FRESH; cbn; auto).
  rewrite PTree.gso by congruence.
  destruct nest; [rewrite PTree.gso by congruence; reflexivity|].
  rewrite IHnest by exact NOT_CHILD.
  rewrite PTree.gso.
  - rewrite PTree.gso by congruence; reflexivity.
  - intro SAME; subst; apply NOT_CHILD; cbn; auto.
Qed.

Fixpoint affine_exit_domain nest temps := match nest with
  | AffineSourceLeaf _ => True
  | AffineSourceAxis iterator bound _ _ child =>
      (exists word,temps!bound=Some(Vint word)) /\
      let last := PTree.set iterator (Vint (Int.sub (temp_word bound temps) Int.one)) temps in
      match child with
      | AffineSourceLeaf _ => True
      | AffineSourceAxis _ child_bound expression _ _ =>
          (forall identifier, In identifier (memory_source_affine_reads expression) ->
            exists word,last!identifier=Some(Vint word)) /\
          affine_exit_domain child (PTree.set child_bound
            (Vint (Int.repr (memory_source_affine_math (affine_word_valuation last) expression))) last) end end.

Lemma affine_exit_fresh_child iterator bound expression body child :
  NoDup (affine_nest_controls (AffineSourceAxis iterator bound expression body child)) ->
  NoDup (affine_nest_controls child) /\ ~ In bound (affine_nest_controls child) /\ iterator <> bound.
Proof.
  cbn; intro UNIQUE; inversion UNIQUE as [|first rest ITERATOR_FRESH TAIL]; subst.
  inversion TAIL as [|first rest BOUND_FRESH CHILD_FRESH]; subst.
  repeat split; auto.
  intro SAME; subst; apply ITERATOR_FRESH; cbn; auto.
Qed.

Theorem affine_exit_statement_execution nest fe ge locals temps memory :
  NoDup (affine_nest_controls nest) -> affine_exit_domain nest temps ->
  exec_stmt fe ge locals temps memory (affine_exit_statement nest) E0
    (affine_exit_temps nest temps) memory Out_normal.
Proof.
  revert temps; induction nest; intros temps UNIQUE DOMAIN; [constructor|].
  destruct DOMAIN as [[upper WORD] DOMAIN].
  assert (UPPER : temp_word bound temps = upper) by (unfold temp_word; rewrite WORD; reflexivity).
  destruct (@affine_exit_fresh_child iterator bound expression body nest UNIQUE) as [CHILD_FRESH [BOUND_FRESH DISTINCT]].
  set (last := PTree.set iterator (Vint (Int.sub upper Int.one)) temps).
  assert (LAST_BOUND : last!bound=Some(Vint upper)) by (unfold last; rewrite PTree.gso by congruence; exact WORD).
  assert (FIRST : exec_stmt fe ge locals temps memory
    (Sset iterator (Ebinop Osub (Etempvar bound type_int32s) (Econst_int Int.one type_int32s) type_int32s))
    E0 last memory Out_normal).
  { constructor; eapply eval_Ebinop; [constructor; exact WORD|constructor|reflexivity]. }
  cbn [affine_exit_statement affine_exit_temps]; rewrite UPPER.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact FIRST|].
  destruct nest as [leaf|child_iterator child_bound child_expression child_body child].
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [constructor|constructor; constructor; exact LAST_BOUND].
  - rewrite UPPER in DOMAIN; change ((forall identifier, In identifier (memory_source_affine_reads child_expression) ->
      exists word,last!identifier=Some(Vint word)) /\ affine_exit_domain
        (AffineSourceAxis child_iterator child_bound child_expression child_body child)
        (PTree.set child_bound (Vint (Int.repr (memory_source_affine_math (affine_word_valuation last) child_expression))) last)) in DOMAIN.
    destruct DOMAIN as [READS CHILD_DOMAIN].
    set (prepared:=PTree.set child_bound (Vint (Int.repr (memory_source_affine_math (affine_word_valuation last) child_expression))) last).
    assert (EVAL:eval_expr ge locals last memory (memory_source_affine_code child_expression)
      (Vint (Int.repr (memory_source_affine_math (affine_word_valuation last) child_expression)))).
    { apply memory_source_affine_evaluation; intros identifier MEMBER; destruct (READS identifier MEMBER) as [word LOOKUP].
      unfold affine_word_valuation,temp_word; rewrite LOOKUP,Int.repr_signed; reflexivity. }
    assert (AFTER_BOUND:(affine_exit_temps (AffineSourceAxis child_iterator child_bound child_expression child_body child) prepared)!bound=Some(Vint upper)).
    { rewrite affine_exit_temps_other by exact BOUND_FRESH.
      unfold prepared; rewrite PTree.gso; [exact LAST_BOUND|intro SAME; subst; apply BOUND_FRESH; cbn; auto]. }
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [constructor; exact EVAL|apply IHnest; assumption].
    + constructor; constructor; exact AFTER_BOUND.
Qed.
Print Assumptions affine_exit_temps_other.
Print Assumptions affine_exit_statement_execution.
