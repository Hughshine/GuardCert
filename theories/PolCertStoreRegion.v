From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Ctypes Cop Csem Clight ClightBigstep.
From polcert.src Require Import PolyBase CTy CState CInstr.
From Guard Require Import ClightGuard ClightNoWrap ClightCondition PolCertMemoryModel
  PolCertArrayClight PolCertScheduleRegion.
Import ListNotations.
Open Scope Z_scope.
Set Implicit Arguments.

Module PolCertStoreRegion (Names : C_INSTR_NAMES).
Module A := PolCertArrayClight Names.
Module R := PolCertScheduleRegion Names.
Module I := R.I.

Definition array_base (ge : Clight.genv) (e : Clight.env) id count b :=
  e ! id = Some (b, A.array_type count) \/
  (e ! id = None /\ Genv.find_symbol ge id = Some b).

Lemma array_value_inv ge e le m id count value :
  Clight.eval_expr ge e le m (Evar id (A.array_type count)) value ->
  exists b, value = Vptr b Ptrofs.zero /\ array_base ge e id count b.
Proof.
  intro RUN; inversion RUN; subst.
  match goal with LV : Clight.eval_lvalue _ _ _ _ (Evar _ _) _ _ _ |- _ =>
    inversion LV; subst end.
  all: match goal with READ : deref_loc _ _ _ _ _ _ |- _ => inversion READ; subst end.
  all: try discriminate.
  all: eexists; split; [reflexivity | unfold array_base; eauto].
Qed.

Lemma array_base_unique ge e id count first second :
  array_base ge e id count first -> array_base ge e id count second -> first = second.
Proof. unfold array_base; intros [A|[A B]] [C|[C D]]; congruence. Qed.

Lemma constant_lvalue_inv ge e le m id count index b offset bf :
  0 <= index < count -> A.array_bound_ok count = true ->
  Clight.eval_lvalue ge e le m
    (A.array_lvalue id count (Econst_int (Int.repr index) type_int32s)) b offset bf ->
  array_base ge e id count b /\ offset = Ptrofs.repr (4 * index) /\ bf = Full.
Proof.
  intros RANGE BOUND RUN; unfold A.array_lvalue in RUN; inversion RUN; subst.
  match goal with ADD : Clight.eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ =>
    inversion ADD; subst end.
  2: match goal with BAD : Clight.eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ =>
    inversion BAD end.
  match goal with BASE : Clight.eval_expr _ _ _ _ (Evar _ _) _ |- _ =>
    destruct (array_value_inv BASE) as [base [VALUE ADDRESS]]; subst end.
  match goal with CONST : Clight.eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply eval_const_inv in CONST; subst end.
  match goal with OP : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
    cbn [typeof] in OP;
    rewrite (proj1 (@A.pointer_index ge base count index m RANGE BOUND)) in OP;
    inversion OP; subst end.
  auto.
Qed.

Definition constant_store id count index value :=
  Sassign (A.array_lvalue id count (Econst_int (Int.repr index) type_int32s))
    (Econst_int value type_int32s).

Lemma constant_store_inv fe ge e le m id count index value le' m' :
  0 <= index < count -> A.array_bound_ok count = true ->
  exec_stmt fe ge e le m (constant_store id count index value) E0 le' m' Out_normal ->
  exists b, array_base ge e id count b /\ le' = le /\
    Mem.store Mint32 m b (4 * index) (Vint value) = Some m'.
Proof.
  intros RANGE BOUND RUN; inversion RUN; subst.
  match goal with LV : Clight.eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (constant_lvalue_inv RANGE BOUND LV) as [BASE [OFFSET FIELD]]; subst end.
  match goal with CONST : Clight.eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply eval_const_inv in CONST; subst end.
  match goal with CAST : sem_cast _ _ _ _ = Some ?result |- _ =>
    change (Some (Vint value) = Some result) in CAST; inversion CAST; subst end.
  match goal with WRITE : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion WRITE; subst end.
  all: try discriminate.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  eexists; split; [exact BASE | split; [reflexivity |]].
  match goal with STORE : Mem.storev _ _ (Vptr ?storeblock _) _ = Some _ |- _ =>
    cbn [Mem.storev] in STORE;
    rewrite (proj2 (@A.pointer_index ge storeblock count index m RANGE BOUND)) in STORE;
    destruct (zle (4 * index + size_chunk Mint32) Ptrofs.modulus) in STORE;
      [exact STORE | discriminate]
  end.
Qed.

Lemma constant_lvalue_run ge e le m id count index b :
  0 <= index < count -> A.array_bound_ok count = true -> array_base ge e id count b ->
  Clight.eval_lvalue ge e le m
    (A.array_lvalue id count (Econst_int (Int.repr index) type_int32s))
    b (Ptrofs.repr (4 * index)) Full.
Proof.
  intros RANGE BOUND BASE; apply eval_Ederef;
    eapply eval_Ebinop with (v1 := Vptr b Ptrofs.zero) (v2 := Vint (Int.repr index)).
  - eapply eval_Elvalue; [|apply deref_loc_reference; reflexivity].
    destruct BASE as [LOCAL|[LOCAL GLOBAL]];
      [apply eval_Evar_local | apply eval_Evar_global]; assumption.
  - constructor.
  - apply (proj1 (@A.pointer_index ge b count index m RANGE BOUND)).
Qed.

Lemma constant_store_run fe ge e le m id count index value b m' :
  0 <= index < count -> A.array_bound_ok count = true -> array_base ge e id count b ->
  Mem.store Mint32 m b (4 * index) (Vint value) = Some m' ->
  exec_stmt fe ge e le m (constant_store id count index value) E0 le m' Out_normal.
Proof.
  intros RANGE BOUND BASE STORE.
  eapply exec_Sassign with (v2 := Vint value) (v := Vint value).
  - eapply constant_lvalue_run; eauto.
  - constructor.
  - reflexivity.
  - eapply assign_loc_value with (chunk := Mint32); [reflexivity |].
    cbn [Mem.storev]; rewrite (proj2 (@A.pointer_index ge b count index m RANGE BOUND)).
    destruct (zle (4 * index + size_chunk Mint32) Ptrofs.modulus); [exact STORE |].
    destruct (A.array_bound_ok_sound count BOUND) as [_ [_ EXTENT]].
    unfold Ptrofs.max_unsigned in EXTENT; cbn [size_chunk] in *; lia.
Qed.

Print Assumptions constant_store_inv.
Print Assumptions constant_store_run.
End PolCertStoreRegion.
