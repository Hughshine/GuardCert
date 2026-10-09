From Stdlib Require Import List.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
Set Implicit Arguments.

Lemma memory_bitfield_load_unique ty size sign position width memory address first second :
  load_bitfield ty size sign position width memory address first ->
  load_bitfield ty size sign position width memory address second -> first = second.
Proof.
  intros FIRST SECOND; inversion FIRST; subst; inversion SECOND; subst.
  match goal with
  | A : Mem.loadv _ _ _ = Some (Vint ?x), B : Mem.loadv _ _ _ = Some (Vint ?y) |- _ =>
    assert (x = y) by congruence; subst y; reflexivity
  end.
Qed.

Lemma memory_dereference_unique ty memory block offset bits first second :
  deref_loc ty memory block offset bits first ->
  deref_loc ty memory block offset bits second -> first = second.
Proof.
  intros FIRST SECOND; inversion FIRST; subst; inversion SECOND; subst; try congruence.
  eapply memory_bitfield_load_unique; eauto.
Qed.

Theorem memory_expression_lvalue_unique ge locals temps memory :
  (forall expression first,
    eval_expr ge locals temps memory expression first ->
    forall second, eval_expr ge locals temps memory expression second -> first = second) /\
  (forall expression block offset bits,
    eval_lvalue ge locals temps memory expression block offset bits ->
    forall other_block other_offset other_bits,
    eval_lvalue ge locals temps memory expression other_block other_offset other_bits ->
    block = other_block /\ offset = other_offset /\ bits = other_bits).
Proof.
  apply eval_expr_lvalue_ind.
  - intros word ty value RUN; inversion RUN; subst; auto.
    match goal with H : eval_lvalue _ _ _ _ (Econst_int _ _) _ _ _ |- _ => inversion H end.
  - intros word ty value RUN; inversion RUN; subst; auto.
    match goal with H : eval_lvalue _ _ _ _ (Econst_float _ _) _ _ _ |- _ => inversion H end.
  - intros word ty value RUN; inversion RUN; subst; auto.
    match goal with H : eval_lvalue _ _ _ _ (Econst_single _ _) _ _ _ |- _ => inversion H end.
  - intros word ty value RUN; inversion RUN; subst; auto.
    match goal with H : eval_lvalue _ _ _ _ (Econst_long _ _) _ _ _ |- _ => inversion H end.
  - intros id ty value LOOKUP other RUN; inversion RUN; subst; try congruence.
    match goal with H : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inversion H end.
  - intros a ty block offset LVALUE IH other RUN; inversion RUN; subst.
    + match goal with H : eval_lvalue _ _ _ _ a _ _ _ |- _ =>
        destruct (IH _ _ _ H) as [BLOCK [OFFSET BITS]]; subst; reflexivity end.
    + match goal with H : eval_lvalue _ _ _ _ (Eaddrof _ _) _ _ _ |- _ => inversion H end.
  - intros op a ty input value EVAL IH OP other RUN; inversion RUN; subst.
    + match goal with H : eval_expr _ _ _ _ a ?v |- _ =>
        pose proof (IH _ H) as SAME; subst v; congruence end.
    + match goal with H : eval_lvalue _ _ _ _ (Eunop _ _ _) _ _ _ |- _ => inversion H end.
  - intros op a b ty first second value A IHA B IHB OP other RUN; inversion RUN; subst.
    + match goal with H : eval_expr _ _ _ _ a ?v |- _ =>
        pose proof (IHA _ H) as SAME; subst v end.
      match goal with H : eval_expr _ _ _ _ b ?v |- _ =>
        pose proof (IHB _ H) as SAME; subst v end; congruence.
    + match goal with H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H end.
  - intros a ty input value EVAL IH CAST other RUN; inversion RUN; subst.
    + match goal with H : eval_expr _ _ _ _ a ?v |- _ =>
        pose proof (IH _ H) as SAME; subst v; congruence end.
    + match goal with H : eval_lvalue _ _ _ _ (Ecast _ _) _ _ _ |- _ => inversion H end.
  - intros first second value RUN; inversion RUN; subst; auto.
    match goal with H : eval_lvalue _ _ _ _ (Esizeof _ _) _ _ _ |- _ => inversion H end.
  - intros first second value RUN; inversion RUN; subst; auto.
    match goal with H : eval_lvalue _ _ _ _ (Ealignof _ _) _ _ _ |- _ => inversion H end.
  - intros a block offset bits value LVALUE IH READ other RUN.
    inversion LVALUE; subst; inversion RUN; subst;
      match goal with H : eval_lvalue _ _ _ _ _ ?b ?o ?bf |- _ =>
        destruct (IH _ _ _ H) as [BLOCK [OFFSET BITS]]; subst;
        eapply memory_dereference_unique; eauto end.
  - intros id block ty LOOKUP other_block other_offset other_bits RUN.
    inversion RUN; subst; repeat split; try reflexivity; congruence.
  - intros id block ty LOOKUP SYMBOL other_block other_offset other_bits RUN.
    inversion RUN; subst; repeat split; try reflexivity; congruence.
  - intros a ty block offset EVAL IH other_block other_offset other_bits RUN.
    inversion RUN; subst.
    match goal with H : eval_expr _ _ _ _ a (Vptr ?b ?o) |- _ =>
      pose proof (IH _ H) as SAME; inversion SAME; subst; auto end.
  - intros a field ty block offset id composite attr delta bits EVAL IH TYPE COMPOSITE FIELD
      other_block other_offset other_bits RUN.
    inversion RUN; subst; try congruence.
    match goal with H : eval_expr _ _ _ _ a (Vptr ?b ?o) |- _ =>
      pose proof (IH _ H) as SAME; inversion SAME; subst end.
    assert (co = composite) by congruence; subst co.
    assert ((delta0,other_bits) = (delta,bits)) as FIELD_SAME by congruence; inversion FIELD_SAME; subst; auto.
  - intros a field ty block offset id composite attr delta bits EVAL IH TYPE COMPOSITE FIELD
      other_block other_offset other_bits RUN.
    inversion RUN; subst; try congruence.
    match goal with H : eval_expr _ _ _ _ a (Vptr ?b ?o) |- _ =>
      pose proof (IH _ H) as SAME; inversion SAME; subst end.
    assert (co = composite) by congruence; subst co.
    assert ((delta0,other_bits) = (delta,bits)) as FIELD_SAME by congruence; inversion FIELD_SAME; subst; auto.
Qed.

Lemma memory_expression_unique ge locals temps memory expression first second :
  eval_expr ge locals temps memory expression first ->
  eval_expr ge locals temps memory expression second -> first = second.
Proof. intros FIRST SECOND; exact (proj1 (memory_expression_lvalue_unique ge locals temps memory) expression first FIRST second SECOND). Qed.

Print Assumptions memory_expression_unique.
