From Stdlib Require Import ZArith Lia.
From compcert.lib Require Import Integers.
From compcert.common Require Import Values Memory.
From compcert.cfrontend Require Import Ctypes Cop.
From Guard Require Import BilateralTransport CompCertMemoryEquivalence.
Open Scope Z_scope.

Lemma identity_valid_pointer_extends first second : Mem.extends first second ->
  forall b ofs target delta, inject_id b = Some (target, delta) ->
  Mem.valid_pointer first b (Ptrofs.unsigned ofs) = true ->
  Mem.valid_pointer second target (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.
Proof.
  intros EXT b ofs target delta MAP VALID. unfold inject_id in MAP; inversion MAP; subst.
  rewrite Ptrofs.add_zero. eapply Mem.valid_pointer_extends; eauto.
Qed.

Lemma identity_weak_pointer_extends first second : Mem.extends first second ->
  forall b ofs target delta, inject_id b = Some (target, delta) ->
  Mem.weak_valid_pointer first b (Ptrofs.unsigned ofs) = true ->
  Mem.weak_valid_pointer second target (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.
Proof.
  intros EXT b ofs target delta MAP VALID. unfold inject_id in MAP; inversion MAP; subst.
  rewrite Ptrofs.add_zero. eapply Mem.weak_valid_pointer_extends; eauto.
Qed.

Lemma identity_weak_pointer_no_overflow first :
  forall b ofs target delta, inject_id b = Some (target, delta) ->
  Mem.weak_valid_pointer first b (Ptrofs.unsigned ofs) = true ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  intros b ofs target delta MAP VALID. unfold inject_id in MAP; inversion MAP; subst.
  change (Ptrofs.unsigned (Ptrofs.repr 0)) with 0. rewrite Z.add_0_r.
  apply Ptrofs.unsigned_range_2.
Qed.

Lemma identity_different_pointers first : forall b1 ofs1 b2 ofs2 target1 delta1 target2 delta2,
  b1 <> b2 -> Mem.valid_pointer first b1 (Ptrofs.unsigned ofs1) = true ->
  Mem.valid_pointer first b2 (Ptrofs.unsigned ofs2) = true ->
  inject_id b1 = Some (target1, delta1) -> inject_id b2 = Some (target2, delta2) ->
  target1 <> target2 \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <>
    Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).
Proof.
  intros b1 ofs1 b2 ofs2 target1 delta1 target2 delta2 DISTINCT V1 V2 M1 M2.
  unfold inject_id in M1, M2; inversion M1; inversion M2; subst; left; assumption.
Qed.

Lemma identity_value_injection v : Val.inject inject_id v v.
Proof. apply val_inject_id, Val.lessdef_refl. Qed.

Lemma memory_equivalent_cast first second v from to : memory_equivalent first second ->
  sem_cast v from to first = sem_cast v from to second.
Proof.
  intro EQ. eapply (@observation_mutual_transport mem val Mem.extends Val.lessdef
    (fun m => sem_cast v from to m) value_lessdef_antisymmetric); [|exact EQ].
  intros m result target RUN EXT.
  destruct (@sem_cast_inj inject_id m target (identity_weak_pointer_extends _ _ EXT)
    v from to result v RUN (identity_value_injection v)) as [value [EV LESS]].
  exists value; split; [exact EV | apply val_inject_id; exact LESS].
Qed.

Lemma memory_equivalent_unary first second op v ty : memory_equivalent first second ->
  sem_unary_operation op v ty first = sem_unary_operation op v ty second.
Proof.
  intro EQ. eapply (@observation_mutual_transport mem val Mem.extends Val.lessdef
    (fun m => sem_unary_operation op v ty m) value_lessdef_antisymmetric); [|exact EQ].
  intros m result target RUN EXT.
  destruct (@sem_unary_operation_inj inject_id m target (identity_weak_pointer_extends _ _ EXT)
    op v ty result v RUN (identity_value_injection v)) as [value [EV LESS]].
  exists value; split; [exact EV | apply val_inject_id; exact LESS].
Qed.

Lemma memory_equivalent_binary first second ce op left lty right rty : memory_equivalent first second ->
  sem_binary_operation ce op left lty right rty first =
    sem_binary_operation ce op left lty right rty second.
Proof.
  intro EQ. eapply (@observation_mutual_transport mem val Mem.extends Val.lessdef
    (fun m => sem_binary_operation ce op left lty right rty m) value_lessdef_antisymmetric); [|exact EQ].
  intros m result target RUN EXT.
  destruct (@sem_binary_operation_inj inject_id m target
    (identity_valid_pointer_extends _ _ EXT) (identity_weak_pointer_extends _ _ EXT)
    (identity_weak_pointer_no_overflow m) (identity_different_pointers m)
    ce op left lty right rty result left right RUN
    (identity_value_injection left) (identity_value_injection right)) as [value [EV LESS]].
  exists value; split; [exact EV | apply val_inject_id; exact LESS].
Qed.

Lemma memory_equivalent_bool first second v ty : memory_equivalent first second ->
  bool_val v ty first = bool_val v ty second.
Proof.
  intro EQ. eapply (@observation_mutual_transport mem bool Mem.extends (@eq bool)
    (fun m => bool_val v ty m) (fun a b AB _ => AB)); [|exact EQ].
  intros m result target RUN EXT. exists result; split; [|reflexivity].
  eapply (@bool_val_inj inject_id m target (identity_weak_pointer_extends _ _ EXT));
    [exact RUN | apply identity_value_injection].
Qed.

Print Assumptions memory_equivalent_binary.
