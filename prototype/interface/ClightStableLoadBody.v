From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightPureExpr ClightSameAddress
  ClightTempFrame ClightTempFootprint ClightProjectedExecution.
From GuardInterface Require Import ClightReadonlyCellSwap.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition stable_load_rhs value iterator :=
  Ebinop Oadd (Ebinop Oadd value (Ecast (Etempvar iterator type_int32s) type_int32u) type_int32u)
    (Econst_int Int.one type_int32u) type_int32u.
Definition stable_load_body out parameter iterator :=
  Sassign (word_load out) (stable_load_rhs (word_load parameter) iterator).
Definition cached_load_body out cache iterator :=
  Sassign (word_load out) (stable_load_rhs (Etempvar cache type_int32u) iterator).

Lemma aligned_word_pointers_apart b1 ofs1 b2 ofs2 :
  (4 | Ptrofs.unsigned ofs1) -> (4 | Ptrofs.unsigned ofs2) -> Vptr b1 ofs1 <> Vptr b2 ofs2 ->
  b1 <> b2 \/ Ptrofs.unsigned ofs1 + 4 <= Ptrofs.unsigned ofs2 \/
    Ptrofs.unsigned ofs2 + 4 <= Ptrofs.unsigned ofs1.
Proof.
  intros [x X] [y Y] DIFFERENT; destruct (peq b1 b2) as [SAME|APART]; [subst b2|auto].
  assert (OFFSETS : Ptrofs.unsigned ofs1 <> Ptrofs.unsigned ofs2).
  { intro EQ; apply DIFFERENT; f_equal.
    rewrite <- (Ptrofs.repr_unsigned ofs1), <- (Ptrofs.repr_unsigned ofs2); congruence. }
  right; lia.
Qed.

Theorem mint32_load_survives_apart_store memory b1 ofs1 b2 ofs2 value loaded final :
  Mem.storev Mint32 memory (Vptr b1 ofs1) value = Some final ->
  Mem.loadv Mint32 memory (Vptr b2 ofs2) = Some loaded ->
  Vptr b1 ofs1 <> Vptr b2 ofs2 ->
  Mem.loadv Mint32 final (Vptr b2 ofs2) = Some loaded.
Proof.
  intros STORE LOAD APART; destruct (@storev_word_facts _ _ _ _ _ STORE) as [[[_ ALIGN1] _] RAW].
  cbn [Mem.loadv] in LOAD |- *; destruct (zle (Ptrofs.unsigned ofs2 + size_chunk Mint32) Ptrofs.modulus);
    [|discriminate].
  destruct (Mem.load_valid_access _ _ _ _ _ LOAD) as [_ ALIGN2].
  change (4 | Ptrofs.unsigned ofs1) in ALIGN1; change (4 | Ptrofs.unsigned ofs2) in ALIGN2.
  erewrite Mem.load_store_other; [exact LOAD|exact RAW|].
  destruct (aligned_word_pointers_apart ALIGN1 ALIGN2 APART) as [BLOCK|[BEFORE|AFTER]];
    change (size_chunk Mint32) with 4; auto.
Qed.

Lemma stable_load_body_facts fe ge locals le memory out parameter iterator after final :
  exec_stmt fe ge locals le memory (stable_load_body out parameter iterator) E0 after final Out_normal ->
  exists b1 ofs1 b2 ofs2 loaded stored,
    le ! out = Some (Vptr b1 ofs1) /\ le ! parameter = Some (Vptr b2 ofs2) /\
    Mem.loadv Mint32 memory (Vptr b2 ofs2) = Some loaded /\
    Mem.storev Mint32 memory (Vptr b1 ofs1) stored = Some final.
Proof.
  unfold stable_load_body; intro RUN; inversion RUN; subst.
  match goal with LVALUE : eval_lvalue _ _ _ _ (word_load out) _ _ _ |- _ =>
    inversion LVALUE; subst end.
  match goal with POINTER : eval_expr _ _ _ _ (pointer_temp out) _ |- _ =>
    apply scalar_temp_inv in POINTER end.
  match goal with RHS : eval_expr _ _ _ _ (stable_load_rhs _ _) _ |- _ =>
    rename RHS into PAYLOAD end.
  unfold stable_load_rhs in PAYLOAD; apply scalar_binary_inv in PAYLOAD.
  destruct PAYLOAD as [sum [one [SUM [CONST OP]]]].
  apply scalar_binary_inv in SUM; destruct SUM as [loaded [index [LOAD [INDEX ADD]]]].
  apply word_load_inv in LOAD; destruct LOAD as [b [offset [PARAMETER READ]]].
  match goal with STORE : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion STORE; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  do 6 eexists; repeat split; eassumption.
Qed.

Lemma stable_load_rhs_cached ge locals le target memory parameter cache iterator b offset loaded value :
  le ! parameter = Some (Vptr b offset) -> Mem.loadv Mint32 memory (Vptr b offset) = Some loaded ->
  target ! cache = Some loaded -> temp_agree [iterator] le target ->
  eval_expr ge locals le memory (stable_load_rhs (word_load parameter) iterator) value ->
  eval_expr ge locals target memory (stable_load_rhs (Etempvar cache type_int32u) iterator) value.
Proof.
  intros POINTER READ CACHE FRAME RUN; unfold stable_load_rhs in *.
  apply scalar_binary_inv in RUN; destruct RUN as [sum [one [SUM [CONST OP]]]].
  apply scalar_binary_inv in SUM; destruct SUM as [old [index [LOAD [INDEX ADD]]]].
  apply word_load_inv in LOAD; destruct LOAD as [other [other_offset [PARAMETER OTHER_READ]]].
  assert (SAME : Vptr other other_offset = Vptr b offset) by congruence.
  injection SAME; intros; subst; assert (OLD : old = loaded) by congruence; subst old.
  eapply eval_Ebinop.
  - eapply eval_Ebinop; [apply eval_Etempvar; exact CACHE| |exact ADD].
    eapply expression_temp_transport; [unfold expression_scope; cbn; apply incl_refl|exact FRAME|exact INDEX].
  - eapply expression_temp_transport; [unfold expression_scope; cbn; intros id BAD; contradiction|exact FRAME|exact CONST].
  - exact OP.
Qed.

Theorem stable_load_body_cached fe ge locals le target memory out parameter cache iterator b offset loaded final :
  le ! parameter = Some (Vptr b offset) -> Mem.loadv Mint32 memory (Vptr b offset) = Some loaded ->
  target ! cache = Some loaded -> temp_agree [out;iterator] le target ->
  exec_stmt fe ge locals le memory (stable_load_body out parameter iterator) E0 le final Out_normal ->
  exec_stmt fe ge locals target memory (cached_load_body out cache iterator) E0 target final Out_normal.
Proof.
  intros POINTER READ CACHE FRAME RUN; unfold stable_load_body, cached_load_body in *.
  inversion RUN; subst.
  eapply exec_Sassign.
  - eapply lvalue_temp_transport with (live := [out;iterator]);
      [unfold expression_scope; cbn; intros id IN; cbn in IN |- *; tauto|exact FRAME|eassumption].
  - eapply stable_load_rhs_cached; [exact POINTER|exact READ|exact CACHE| |eassumption].
    eapply temp_agree_weaken; [|exact FRAME]; intros id IN; cbn in IN |- *; tauto.
  - eassumption.
  - eassumption.
Qed.

Theorem stable_load_body_preserves_parameter fe ge locals le memory out parameter iterator b offset loaded final :
  le ! parameter = Some (Vptr b offset) -> Mem.loadv Mint32 memory (Vptr b offset) = Some loaded ->
  le ! out <> le ! parameter ->
  exec_stmt fe ge locals le memory (stable_load_body out parameter iterator) E0 le final Out_normal ->
  Mem.loadv Mint32 final (Vptr b offset) = Some loaded.
Proof.
  intros PARAMETER READ APART RUN.
  destruct (stable_load_body_facts RUN) as [b1 [ofs1 [b2 [ofs2 [old [stored [P [Q [LOAD STORE]]]]]]]]].
  assert (SAME : Vptr b2 ofs2 = Vptr b offset) by congruence; injection SAME; intros; subst.
  eapply mint32_load_survives_apart_store; [exact STORE|exact READ|].
  intro EQ; apply APART; congruence.
Qed.

Print Assumptions mint32_load_survives_apart_store.
Print Assumptions stable_load_body_cached.
Print Assumptions stable_load_body_preserves_parameter.
