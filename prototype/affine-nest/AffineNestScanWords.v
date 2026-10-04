From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightTempFrame ClightRectangularStore.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation GuardMemoryAffineRenaming.
From GuardAffineNest Require Import AffineNestScanSyntax.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma affine_scan_word_view_frame registers values valuation before after live :
  incl(map values registers) live -> temp_agree live before after ->
  affine_scan_word_view registers values valuation before -> affine_scan_word_view registers values valuation after.
Proof.
  intros INCLUDED FRAME WORDS identifier MEMBER; rewrite FRAME; [apply WORDS; exact MEMBER|].
  apply INCLUDED,in_map; exact MEMBER.
Qed.

Lemma affine_scan_word_view_update registers values valuation temps iterator counter value live :
  values iterator=counter -> ~In counter live -> incl(map values registers) live ->
  affine_scan_word_view registers values valuation temps -> temps!counter=Some(Vint(Int.repr value)) ->
  affine_scan_word_view(registers++[iterator]) values(memory_source_set_valuation valuation iterator value) temps.
Proof.
  intros SAME FRESH INCLUDED WORDS COUNTER identifier MEMBER.
  unfold memory_source_set_valuation; destruct(peq identifier iterator) as [->|OTHER].
  - rewrite SAME; exact COUNTER.
  - apply in_app_or in MEMBER as [MEMBER|MEMBER]; [apply WORDS; exact MEMBER|].
    cbn in MEMBER; intuition congruence.
Qed.

Theorem affine_scan_expression_evaluation expression values valuation ge locals temps memory :
  (forall identifier, In identifier(memory_source_affine_reads expression) ->
    temps!(values identifier)=Some(Vint(Int.repr(valuation identifier)))) ->
  eval_expr ge locals temps memory(memory_source_affine_code(memory_source_affine_rename values expression))
    (Vint(Int.repr(memory_source_affine_math valuation expression))).
Proof.
  induction expression; intro WORDS; cbn [memory_source_affine_rename memory_source_affine_code memory_source_affine_math].
  - constructor; apply WORDS; cbn; auto.
  - apply rect_constant_evaluation.
  - apply operand_sum_evaluation; try apply memory_source_affine_type;
      [apply IHexpression1|apply IHexpression2]; intros identifier MEMBER; apply WORDS,in_or_app; auto.
  - eapply eval_Ebinop with(v1:=Vint(Int.repr(memory_source_affine_math valuation expression1)))
      (v2:=Vint(Int.repr(memory_source_affine_math valuation expression2))).
    + apply IHexpression1; intros identifier MEMBER; apply WORDS,in_or_app; auto.
    + apply IHexpression2; intros identifier MEMBER; apply WORDS,in_or_app; auto.
    + rewrite !memory_source_affine_type.
      change(Some(Vint(Int.sub(Int.repr(memory_source_affine_math valuation expression1))
        (Int.repr(memory_source_affine_math valuation expression2))))=
        Some(Vint(Int.repr(memory_source_affine_math valuation expression1-memory_source_affine_math valuation expression2)))).
      rewrite memory_source_integer_subtract; reflexivity.
  - apply operand_product_evaluation; [apply memory_source_affine_type|apply IHexpression; exact WORDS].
  - eapply eval_Ebinop with(v1:=Vint(Int.repr factor))(v2:=Vint(Int.repr(memory_source_affine_math valuation expression))).
    + apply rect_constant_evaluation.
    + apply IHexpression; exact WORDS.
    + rewrite rect_constant_type,memory_source_affine_type.
      change(Some(Vint(Int.mul(Int.repr factor)(Int.repr(memory_source_affine_math valuation expression))))=
        Some(Vint(Int.repr(factor*memory_source_affine_math valuation expression)))).
      rewrite rect_integer_multiply; reflexivity.
Qed.
Print Assumptions affine_scan_expression_evaluation.
