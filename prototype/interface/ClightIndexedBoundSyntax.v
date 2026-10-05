From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightPureExpr ClightSameAddress
  ClightCountedLoop ClightLoopExecution ClightStraightLine ClightTempFrame ClightLoopSyntax ClightRegionProgress.
From GuardInterface Require Import ClightStrictLoopProgress ClightIndexedLoadBody ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition indexed_bound_value bound := Ecast (word_load bound) type_int32s.
Definition indexed_bound_test iterator bound :=
  Ebinop Olt (Etempvar iterator type_int32s) (indexed_bound_value bound) type_int32s.
Definition indexed_bound_body out iterator := Sassign (indexed_word_lvalue out iterator)
  (Ebinop Oadd (Ecast (Etempvar iterator type_int32s) type_int32u)
    (Econst_int Int.one type_int32u) type_int32u).
Definition indexed_bound_loop iterator bound body := strict_frontend_loop iterator (indexed_bound_test iterator bound) body.

Lemma indexed_bound_value_inverse ge locals le memory bound value :
  eval_expr ge locals le memory (indexed_bound_value bound) (Vint value) ->
  exists block offset, le ! bound = Some (Vptr block offset) /\ Mem.loadv Mint32 memory (Vptr block offset) = Some (Vint value).
Proof.
  intro RUN; unfold indexed_bound_value in RUN; inversion RUN; subst.
  all: try (match goal with LV : eval_lvalue _ _ _ _ (Ecast _ _) _ _ _ |- _ => inversion LV end).
  match goal with LOAD : eval_expr _ _ _ _ (word_load bound) _, CAST : sem_cast _ _ _ _ = _ |- _ =>
    apply word_load_inv in LOAD; destruct LOAD as [block [offset [POINTER READ]]];
    destruct v1; cbn in CAST; try discriminate; inversion CAST; subst;
    exists block, offset; split; assumption end.
Qed.
Lemma indexed_bound_value_evaluation ge locals le memory bound block offset value :
  le ! bound = Some (Vptr block offset) -> Mem.loadv Mint32 memory (Vptr block offset) = Some (Vint value) ->
  eval_expr ge locals le memory (indexed_bound_value bound) (Vint value).
Proof.
  intros BOUND READ; eapply eval_Ecast with (v1 := Vint value); [|reflexivity].
  apply eval_Elvalue with (loc := block) (ofs := offset) (bf := Full).
  - apply eval_Ederef, eval_Etempvar; exact BOUND.
  - apply deref_loc_value with (chunk := Mint32); [reflexivity|exact READ].
Qed.
Theorem indexed_bound_test_facts ge locals le memory iterator bound flag :
  expression_test (indexed_bound_test iterator bound) (Entry ge locals le memory) flag ->
  exists i n block offset, le ! iterator = Some (Vint i) /\ le ! bound = Some (Vptr block offset) /\
    Mem.loadv Mint32 memory (Vptr block offset) = Some (Vint n) /\ flag = Int.lt i n.
Proof.
  intros [value [EVAL BOOL]]; apply scalar_binary_inv in EVAL.
  destruct EVAL as [i [n [I [N OP]]]]; apply scalar_temp_inv in I.
  destruct i, n; try discriminate OP.
  destruct (indexed_bound_value_inverse N) as [block [offset [BOUND READ]]].
  change (Some (Val.of_bool (Int.lt i i0)) = Some value) in OP; injection OP as VALUE; subst value.
  rewrite bool_of_bool in BOOL; exists i, i0, block, offset; repeat split; try assumption; congruence.
Qed.
Theorem indexed_bound_test_strict ge locals le memory iterator bound :
  expression_test (indexed_bound_test iterator bound) (Entry ge locals le memory) true -> strict_counter_active iterator le.
Proof.
  intro TEST; destruct (indexed_bound_test_facts TEST) as [i [n [b [ofs [I [Q [READ LT]]]]]]].
  exists i; split; [exact I|].
  unfold Int.lt in LT; destruct (zlt (Int.signed i) (Int.signed n)); pose proof (Int.signed_range n); try discriminate; lia.
Qed.
Lemma indexed_bound_test_eval ge locals le memory iterator bound i n block offset :
  le ! iterator = Some (Vint i) -> le ! bound = Some (Vptr block offset) ->
  Mem.loadv Mint32 memory (Vptr block offset) = Some (Vint n) ->
  expression_test (indexed_bound_test iterator bound) (Entry ge locals le memory) (Int.lt i n).
Proof.
  intros I Q READ; exists (Val.of_bool (Int.lt i n)); split; [|apply bool_of_bool].
  eapply eval_Ebinop with (v1 := Vint i) (v2 := Vint n); [constructor; exact I| |reflexivity].
  eapply indexed_bound_value_evaluation; eassumption.
Qed.
Lemma indexed_bound_body_store fe ge locals le memory out iterator word trace after final outcome :
  le ! iterator = Some (Vint word) ->
  exec_stmt fe ge locals le memory (indexed_bound_body out iterator) trace after final outcome ->
  exists block base value, le ! out = Some (Vptr block base) /\
    Mem.storev Mint32 memory (Vptr block (indexed_word_offset base word)) value = Some final.
Proof.
  intros ITER RUN; inversion RUN; subst.
  match goal with LV : eval_lvalue _ _ _ _ (indexed_word_lvalue _ _) _ _ _ |- _ => inversion LV; subst end.
  match goal with ADDRESS : eval_expr _ _ _ _ (indexed_word_pointer _ _) (Vptr _ _) |- _ =>
    destruct (@indexed_pointer_inverse ge locals _ memory out (Etempvar iterator type_int32s) _ _ word
      ltac:(constructor; exact ITER) eq_refl ADDRESS) as [base [OUT OFFSET]]; subst end.
  match goal with STORE : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion STORE; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  do 3 eexists; split; eassumption.
Qed.
Print Assumptions indexed_bound_test_strict.
Print Assumptions indexed_bound_body_store.
