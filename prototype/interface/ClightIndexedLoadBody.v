From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightPureExpr ClightSameAddress
  ClightTempFrame ClightTempFootprint ClightProjectedExecution.
From GuardInterface Require Import ClightReadonlyCellSwap ClightStableLoadBody ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition indexed_word_offset base word :=
  Ptrofs.add base (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints word)).
Definition indexed_word_pointer out index :=
  Ebinop Oadd (pointer_temp out) index word_pointer.
Definition indexed_word_lvalue out iterator :=
  Ederef (indexed_word_pointer out (Etempvar iterator type_int32s)) type_int32u.
Definition indexed_load_body out parameter iterator :=
  Sassign (indexed_word_lvalue out iterator) (stable_load_rhs (word_load parameter) iterator).
Definition indexed_cached_body out cache iterator :=
  Sassign (indexed_word_lvalue out iterator) (stable_load_rhs (Etempvar cache type_int32u) iterator).

Theorem indexed_pointer_evaluation ge locals le memory out expression block base word :
  le ! out = Some (Vptr block base) -> eval_expr ge locals le memory expression (Vint word) ->
  typeof expression = type_int32s ->
  eval_expr ge locals le memory (indexed_word_pointer out expression) (Vptr block (indexed_word_offset base word)).
Proof.
  intros OUT INDEX TYPE; unfold indexed_word_pointer; eapply eval_Ebinop with (v1 := Vptr block base) (v2 := Vint word).
  - constructor; exact OUT.
  - exact INDEX.
  - rewrite TYPE; reflexivity.
Qed.

Theorem indexed_pointer_inverse ge locals le memory out expression block offset word :
  eval_expr ge locals le memory expression (Vint word) -> typeof expression = type_int32s ->
  eval_expr ge locals le memory (indexed_word_pointer out expression) (Vptr block offset) ->
  exists base, le ! out = Some (Vptr block base) /\ offset = indexed_word_offset base word.
Proof.
  intros INDEX TYPE RUN; unfold indexed_word_pointer in RUN; apply scalar_binary_inv in RUN.
  destruct RUN as [pointer [index [POINTER [POINT OP]]]].
  apply scalar_temp_inv in POINTER.
  pose proof (proj1 (expressions_determinate ge locals le memory) _ _ INDEX _ POINT) as SAME; subst index.
  rewrite TYPE in OP; destruct pointer; cbn in OP; try discriminate.
  inversion OP; subst; exists i; split; [exact POINTER|reflexivity].
Qed.

Theorem indexed_load_body_facts fe ge locals le memory out parameter iterator word after final :
  le ! iterator = Some (Vint word) ->
  exec_stmt fe ge locals le memory (indexed_load_body out parameter iterator) E0 after final Out_normal ->
  exists b1 base b2 offset loaded stored,
    le ! out = Some (Vptr b1 base) /\ le ! parameter = Some (Vptr b2 offset) /\
    Mem.loadv Mint32 memory (Vptr b2 offset) = Some loaded /\
    Mem.storev Mint32 memory (Vptr b1 (indexed_word_offset base word)) stored = Some final.
Proof.
  intros ITER RUN; inversion RUN; subst.
  match goal with LV : eval_lvalue _ _ _ _ (indexed_word_lvalue _ _) _ _ _ |- _ => inversion LV; subst end.
  match goal with ADDRESS : eval_expr _ _ _ _ (indexed_word_pointer _ _) (Vptr _ _) |- _ =>
    destruct (@indexed_pointer_inverse ge locals _ memory out (Etempvar iterator type_int32s) _ _ word
      ltac:(constructor; exact ITER) eq_refl ADDRESS) as [base [OUT OFFSET]]; subst end.
  match goal with RHS : eval_expr _ _ _ _ (stable_load_rhs _ _) _ |- _ => rename RHS into PAYLOAD end.
  unfold stable_load_rhs in PAYLOAD; apply scalar_binary_inv in PAYLOAD.
  destruct PAYLOAD as [sum [one [SUM [CONST OP]]]].
  apply scalar_binary_inv in SUM; destruct SUM as [loaded [index [LOAD [INDEX ADD]]]].
  apply word_load_inv in LOAD; destruct LOAD as [b [offset [PARAMETER READ]]].
  match goal with STORE : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion STORE; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  do 6 eexists; repeat split; eassumption.
Qed.

Theorem indexed_load_body_cached fe ge locals le target memory out parameter cache iterator b offset loaded final :
  le ! parameter = Some (Vptr b offset) -> Mem.loadv Mint32 memory (Vptr b offset) = Some loaded ->
  target ! cache = Some loaded -> temp_agree [out;iterator] le target ->
  exec_stmt fe ge locals le memory (indexed_load_body out parameter iterator) E0 le final Out_normal ->
  exec_stmt fe ge locals target memory (indexed_cached_body out cache iterator) E0 target final Out_normal.
Proof.
  intros POINTER READ CACHE FRAME RUN; unfold indexed_load_body, indexed_cached_body in *.
  inversion RUN; subst; eapply exec_Sassign.
  - eapply lvalue_temp_transport with (live := [out;iterator]);
      [unfold expression_scope; cbn; intros id IN; cbn in IN |- *; tauto|exact FRAME|eassumption].
  - eapply stable_load_rhs_cached; [exact POINTER|exact READ|exact CACHE| |eassumption].
    eapply temp_agree_weaken; [|exact FRAME]; intros id IN; cbn in IN |- *; tauto.
  - eassumption.
  - eassumption.
Qed.

Theorem indexed_load_body_preserves_parameter fe ge locals le memory out parameter iterator word
  b1 base b2 offset loaded final :
  le ! iterator = Some (Vint word) -> le ! out = Some (Vptr b1 base) -> le ! parameter = Some (Vptr b2 offset) ->
  Mem.loadv Mint32 memory (Vptr b2 offset) = Some loaded ->
  Vptr b1 (indexed_word_offset base word) <> Vptr b2 offset ->
  exec_stmt fe ge locals le memory (indexed_load_body out parameter iterator) E0 le final Out_normal ->
  Mem.loadv Mint32 final (Vptr b2 offset) = Some loaded.
Proof.
  intros ITER OUT PARAMETER READ APART RUN.
  destruct (indexed_load_body_facts ITER RUN) as [other [other_base [q [qofs [old [stored [P [Q [LOAD STORE]]]]]]]]].
  assert (P_SAME : Vptr other other_base = Vptr b1 base) by congruence; injection P_SAME; intros; subst.
  assert (Q_SAME : Vptr q qofs = Vptr b2 offset) by congruence; injection Q_SAME; intros; subst.
  eapply mint32_load_survives_apart_store; [exact STORE|exact READ|exact APART].
Qed.
Print Assumptions indexed_pointer_evaluation.
Print Assumptions indexed_pointer_inverse.
Print Assumptions indexed_load_body_facts.
Print Assumptions indexed_load_body_cached.
Print Assumptions indexed_load_body_preserves_parameter.
