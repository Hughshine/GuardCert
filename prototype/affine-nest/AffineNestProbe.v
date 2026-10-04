From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep Ctypes Cop.
From Guard Require Import ClightCondition ClightCountedLoop ClightNoWrap ClightTempFrame.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryAffineRenaming.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestFirstDomain AffineNestFirstLeaf
  AffineNestBoundWords AffineNestProbeRenaming.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_probe_store result (flag : bool) := Sset result
  (Econst_int (if flag then Int.one else Int.zero) type_int32s).
Fixpoint affine_first_probe nest rename result := match nest with
  | AffineSourceLeaf _ => affine_probe_store result true
  | AffineSourceAxis iterator bound _ _ child =>
      Sifthenelse (counter_condition (rename iterator) (rename bound))
        (match child with
        | AffineSourceLeaf _ => affine_first_probe child rename result
        | AffineSourceAxis child_iterator child_bound expression _ _ =>
            Ssequence (Sset (rename child_bound)
              (memory_source_affine_code(memory_source_affine_rename rename expression)))
              (Ssequence (Sset (rename child_iterator)(Econst_int Int.zero type_int32s))
                (affine_first_probe child rename result)) end)
        (affine_probe_store result false) end.
Fixpoint affine_first_path_flag nest temps := match nest with
  | AffineSourceLeaf _ => true
  | AffineSourceAxis iterator bound _ _ child =>
      if Int.lt (temp_word iterator temps) (temp_word bound temps)
      then affine_first_path_flag child (affine_first_child_temps child temps) else false end.

Lemma affine_integer_lt word upper : Int.lt word upper=(Int.signed word <? Int.signed upper).
Proof.
  unfold Int.lt; destruct(zlt (Int.signed word)(Int.signed upper));
    [symmetry; apply Z.ltb_lt|symmetry; apply Z.ltb_ge]; lia.
Qed.
Theorem affine_first_path_flag_exact nest : forall temps,
  affine_first_path_flag nest temps=true <-> affine_first_path_active nest temps.
Proof.
  induction nest; intro temps; cbn [affine_first_path_flag affine_first_path_active]; [tauto|].
  rewrite affine_integer_lt; destruct(Int.signed(temp_word iterator temps) <? Int.signed(temp_word bound temps)) eqn:ACTIVE.
  - apply Z.ltb_lt in ACTIVE; rewrite IHnest; tauto.
  - apply Z.ltb_ge in ACTIVE; split; [discriminate|intros [BAD _]; lia].
Qed.

Lemma affine_probe_header_test iterator bound registers rename ge locals source target memory :
  In iterator registers -> In bound registers ->
  (exists word,source!iterator=Some(Vint word)) -> (exists word,source!bound=Some(Vint word)) ->
  affine_renamed_view registers rename source target ->
  expression_test (counter_condition(rename iterator)(rename bound)) (Entry ge locals target memory)
    (Int.lt(temp_word iterator source)(temp_word bound source)).
Proof.
  intros ITERATOR BOUND [word WORD] [upper UPPER] VIEW.
  unfold temp_word; rewrite WORD,UPPER.
  exists(Val.of_bool(Int.lt word upper)); split.
  - unfold counter_condition; eapply eval_Ebinop.
    + constructor; cbn; rewrite VIEW by exact ITERATOR; exact WORD.
    + constructor; cbn; rewrite VIEW by exact BOUND; exact UPPER.
    + reflexivity.
  - destruct(Int.lt word upper); reflexivity.
Qed.
Print Assumptions affine_first_path_flag_exact.
Print Assumptions affine_probe_header_test.
