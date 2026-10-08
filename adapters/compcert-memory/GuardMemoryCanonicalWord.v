From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes Cop ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightRectangularStore ClightTempFrame.
From GuardMemory Require Import GuardMemoryCanonicalDifference.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition canonical_word_sub first second := Ebinop Osub first second type_int32s.
Definition canonical_word_less first second := Ebinop Olt first second type_int32s.
Definition canonical_word_register identifier := Etempvar identifier type_int32s.
Definition canonical_word_center bound := canonical_word_sub (canonical_word_register bound) (rect_constant 1).
Definition canonical_word_bound bound :=
  canonical_word_sub (Ebinop Oadd (canonical_word_register bound) (canonical_word_register bound) type_int32s)
    (rect_constant 1).
Definition canonical_bound_statement bound output :=
  Sifthenelse (canonical_word_less (canonical_word_register bound) (rect_constant 1))
    (Sset output (rect_constant 0)) (Sset output (canonical_word_bound bound)).

Lemma canonical_integer_sub x y : Int.sub (Int.repr x) (Int.repr y) = Int.repr (x-y).
Proof.
  unfold Int.sub; apply Int.eqm_samerepr; apply Int.eqm_sub;
    apply Int.eqm_sym; apply Int.eqm_unsigned_repr.
Qed.

Lemma canonical_word_sub_value ge locals temps memory first second a b :
  typeof first = type_int32s -> typeof second = type_int32s ->
  eval_expr ge locals temps memory first (Vint (Int.repr a)) ->
  eval_expr ge locals temps memory second (Vint (Int.repr b)) ->
  eval_expr ge locals temps memory (canonical_word_sub first second) (Vint (Int.repr (a-b))).
Proof.
  intros FIRST_TYPE SECOND_TYPE FIRST SECOND; unfold canonical_word_sub.
  eapply eval_Ebinop; [exact FIRST|exact SECOND|].
  rewrite FIRST_TYPE,SECOND_TYPE.
  change (Some (Vint (Int.sub (Int.repr a) (Int.repr b))) = Some (Vint (Int.repr (a-b)))).
  rewrite canonical_integer_sub; reflexivity.
Qed.

Lemma canonical_word_less_value ge locals temps memory first second a b :
  typeof first = type_int32s -> typeof second = type_int32s ->
  eval_expr ge locals temps memory first (Vint (Int.repr a)) ->
  eval_expr ge locals temps memory second (Vint (Int.repr b)) ->
  signed_range a -> signed_range b ->
  expression_test (canonical_word_less first second) (Entry ge locals temps memory) (a <? b).
Proof.
  intros FIRST_TYPE SECOND_TYPE FIRST SECOND A B; exists (Val.of_bool (a <? b)); split.
  - unfold canonical_word_less; eapply eval_Ebinop; [exact FIRST|exact SECOND|].
    rewrite FIRST_TYPE,SECOND_TYPE.
    change (Some (Val.of_bool (Int.lt (Int.repr a) (Int.repr b))) = Some (Val.of_bool (a <? b))).
    unfold Int.lt; rewrite !Int.signed_repr by assumption.
    destruct (zlt a b) as [LESS|GREATER].
    + assert (TEST : (a <? b)=true) by (apply Z.ltb_lt; exact LESS); rewrite TEST; reflexivity.
    + assert (TEST : (a <? b)=false) by (apply Z.ltb_ge; lia); rewrite TEST; reflexivity.
  - destruct (a <? b); reflexivity.
Qed.

Lemma canonical_word_center_value ge locals temps memory bound count :
  temps!bound = Some (Vint (Int.repr count)) ->
  eval_expr ge locals temps memory (canonical_word_center bound) (Vint (Int.repr (count-1))).
Proof.
  intro WORD; unfold canonical_word_center; apply canonical_word_sub_value;
    [reflexivity|apply rect_constant_type|constructor; exact WORD|apply rect_constant_evaluation].
Qed.

Lemma canonical_word_bound_value ge locals temps memory bound count :
  temps!bound = Some (Vint (Int.repr count)) ->
  eval_expr ge locals temps memory (canonical_word_bound bound) (Vint (Int.repr (2*count-1))).
Proof.
  intro WORD; replace (2*count-1) with ((count+count)-1) by lia.
  unfold canonical_word_bound; apply canonical_word_sub_value;
    [reflexivity|apply rect_constant_type| |apply rect_constant_evaluation].
  eapply eval_Ebinop; [constructor; exact WORD|constructor; exact WORD|].
  change (Some (Vint (Int.add (Int.repr count) (Int.repr count))) = Some (Vint (Int.repr (count+count)))).
  rewrite rect_integer_add; reflexivity.
Qed.

Theorem canonical_bound_execution fe ge locals temps memory bound output count :
  0 <= count -> signed_range count -> temps!bound = Some (Vint (Int.repr count)) ->
  exec_stmt fe ge locals temps memory (canonical_bound_statement bound output) E0
    (PTree.set output (Vint (Int.repr (canonical_difference_bound count))) temps) memory Out_normal.
Proof.
  intros NONNEG RANGE WORD.
  destruct (@canonical_word_less_value ge locals temps memory
    (canonical_word_register bound) (rect_constant 1) count 1
    eq_refl (rect_constant_type 1) ltac:(constructor; exact WORD)
    (rect_constant_evaluation ge locals temps memory 1) RANGE ltac:(change (-2147483648 <= 1 <= 2147483647); lia))
    as [value [EVAL BOOL]].
  unfold canonical_bound_statement; destruct (count <? 1) eqn:TEST.
  - apply Z.ltb_lt in TEST; assert (ZERO : count=0) by lia; subst count.
    change (canonical_difference_bound 0) with 0.
    eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor; apply rect_constant_evaluation].
  - apply Z.ltb_ge in TEST.
    unfold canonical_difference_bound; rewrite Z.max_r by lia.
    eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor; apply canonical_word_bound_value; exact WORD].
Qed.

Lemma canonical_difference_signed count :
  0 <= count -> 2*count-1 <= Int.max_signed -> signed_range (canonical_difference_bound count).
Proof.
  intros NONNEG UPPER; unfold canonical_difference_bound,signed_range.
  pose proof Int.min_signed_neg; pose proof Int.max_signed_pos.
  destruct (Z_le_dec (2*count-1) 0); [rewrite Z.max_l by lia|rewrite Z.max_r by lia]; lia.
Qed.

Definition canonical_axis_statement bound position left right :=
  Sifthenelse (canonical_word_less (canonical_word_register position) (canonical_word_center bound))
    (Ssequence (Sset left (rect_constant 0))
      (Sset right (canonical_word_sub (canonical_word_center bound) (canonical_word_register position))))
    (Ssequence (Sset left (canonical_word_sub (canonical_word_register position) (canonical_word_center bound)))
      (Sset right (rect_constant 0))).

Theorem canonical_axis_execution fe ge locals temps memory bound position left right count index :
  left <> bound -> left <> position ->
  0 <= count -> signed_range count -> 2*count-1 <= Int.max_signed ->
  0 <= index < canonical_difference_bound count ->
  temps!bound = Some (Vint (Int.repr count)) ->
  temps!position = Some (Vint (Int.repr index)) ->
  exec_stmt fe ge locals temps memory (canonical_axis_statement bound position left right) E0
    (PTree.set right (Vint (Int.repr (canonical_difference_right count index)))
      (PTree.set left (Vint (Int.repr (canonical_difference_left count index))) temps)) memory Out_normal.
Proof.
  intros BOUND_FRESH POSITION_FRESH NONNEG COUNT UPPER INDEX BOUND POSITION.
  assert (INDEX_SIGNED : signed_range index).
  { pose proof (canonical_difference_signed NONNEG UPPER);
      unfold signed_range in *; pose proof Int.min_signed_neg; lia. }
  assert (CENTER_SIGNED : signed_range (count-1)).
  { unfold signed_range in *; change Int.min_signed with (-2147483648); lia. }
  destruct (@canonical_word_less_value ge locals temps memory
    (canonical_word_register position) (canonical_word_center bound) index (count-1)
    eq_refl eq_refl ltac:(constructor; exact POSITION)
    (@canonical_word_center_value ge locals temps memory bound count BOUND) INDEX_SIGNED CENTER_SIGNED)
    as [value [EVAL BOOL]].
  unfold canonical_axis_statement; destruct (index <? count-1) eqn:TEST.
  - apply Z.ltb_lt in TEST; unfold canonical_difference_left,canonical_difference_right.
    rewrite (@Z.max_l 0 (index-(count-1)) ltac:(lia)),
      (@Z.max_r 0 ((count-1)-index) ltac:(lia)).
    eapply exec_Sifthenelse; [exact EVAL|exact BOOL|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
    + constructor; apply rect_constant_evaluation.
    + constructor; apply canonical_word_sub_value; [reflexivity|reflexivity| |].
      * apply canonical_word_center_value; rewrite PTree.gso by congruence; exact BOUND.
      * constructor; rewrite PTree.gso by congruence; exact POSITION.
  - apply Z.ltb_ge in TEST; unfold canonical_difference_left,canonical_difference_right.
    rewrite (@Z.max_r 0 (index-(count-1)) ltac:(lia)),
      (@Z.max_l 0 ((count-1)-index) ltac:(lia)).
    eapply exec_Sifthenelse; [exact EVAL|exact BOOL|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
    + constructor; apply canonical_word_sub_value; [reflexivity|reflexivity|constructor; exact POSITION|].
      apply canonical_word_center_value; exact BOUND.
    + constructor; apply rect_constant_evaluation.
Qed.

Print Assumptions canonical_integer_sub.
Print Assumptions canonical_word_sub_value.
Print Assumptions canonical_word_less_value.
Print Assumptions canonical_word_center_value.
Print Assumptions canonical_word_bound_value.
Print Assumptions canonical_bound_execution.
Print Assumptions canonical_difference_signed.
Print Assumptions canonical_axis_execution.
