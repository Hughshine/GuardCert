From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From polcert.polygen Require Import InstrTy Loop.
From Guard Require Import PolCertLoopGuard ClightCondition ClightPureExpr.
Import ListNotations.
Open Scope Z_scope.
Set Implicit Arguments.

(** A checked, signed-32 affine subset of the actual mathematical Loop IR.
    Interval proposals are untrusted; the checker rejects every unsupported
    operation and every intermediate or coefficient outside machine range. *)
Module PolCertAffineClightFor (I : INSTR) (M : LOOP_MODEL I).
Module L := M.

Record interval := Interval { lower : Z; upper : Z }.
Definition contains (b : interval) (z : Z) := lower b <= z <= upper b.
Definition machine_range (z : Z) := Int.min_signed <= z <= Int.max_signed.
Definition interval_valid (b : interval) : bool :=
  (Int.min_signed <=? lower b) && (lower b <=? upper b) &&
  (upper b <=? Int.max_signed).
Definition checked (b : interval) : option interval :=
  if interval_valid b then Some b else None.

Lemma checked_sound b b' : checked b = Some b' ->
  b = b' /\ lower b <= upper b /\
  Int.min_signed <= lower b /\ upper b <= Int.max_signed.
Proof.
  unfold checked, interval_valid. destruct (_ && _ && _) eqn:VALID;
    try discriminate. intro EQ; inversion EQ; subst.
  repeat rewrite andb_true_iff in VALID. repeat rewrite Z.leb_le in VALID.
  tauto.
Qed.

Definition sum_interval (a b : interval) : interval :=
  Interval (lower a + lower b) (upper a + upper b).
Definition scaled_interval (k : Z) (a : interval) : interval :=
  if 0 <=? k then Interval (k * lower a) (k * upper a)
  else Interval (k * upper a) (k * lower a).

Fixpoint analyze (bounds : list interval) (e : L.expr) : option interval :=
  match e with
  | L.Constant z => checked (Interval z z)
  | L.Var n => match nth_error bounds n with Some b => checked b | None => None end
  | L.Sum x y =>
      match analyze bounds x, analyze bounds y with
      | Some a, Some b => checked (sum_interval a b) | _, _ => None end
  | L.Mult k x =>
      match checked (Interval k k), analyze bounds x with
      | Some _, Some a => checked (scaled_interval k a) | _, _ => None end
  | _ => None
  end.

Definition env_within (bounds : list interval) (env : list Z) : Prop :=
  forall n b, nth_error bounds n = Some b -> contains b (nth n env 0).

Fixpoint affine_safe (e : L.expr) (env : list Z) : Prop :=
  match e with
  | L.Constant z => machine_range z
  | L.Var n => machine_range (nth n env 0)
  | L.Sum x y => affine_safe x env /\ affine_safe y env /\
      machine_range (L.eval_expr env e)
  | L.Mult k x => machine_range k /\ affine_safe x env /\
      machine_range (L.eval_expr env e)
  | _ => False
  end.

Lemma interval_range b z :
  Int.min_signed <= lower b -> upper b <= Int.max_signed ->
  contains b z -> machine_range z.
Proof. unfold contains, machine_range; lia. Qed.

Theorem analyze_sound e : forall bounds b env,
  analyze bounds e = Some b -> env_within bounds env ->
  contains b (L.eval_expr env e) /\ affine_safe e env.
Proof.
  induction e; intros bounds b env ANAL VIEW;
    cbn [analyze] in ANAL; try discriminate.
  - apply checked_sound in ANAL. destruct ANAL as [<- [_ [LO HI]]].
    change ((z <= z <= z) /\ (Int.min_signed <= z <= Int.max_signed)).
    split; [split; apply Z.le_refl | split; assumption].
  - destruct (analyze bounds e1) as [a|] eqn:A; try discriminate.
    destruct (analyze bounds e2) as [c|] eqn:C; try discriminate.
    destruct (IHe1 _ _ _ A VIEW) as [EA SAFE_A].
    destruct (IHe2 _ _ _ C VIEW) as [EC SAFE_C].
    apply checked_sound in ANAL. destruct ANAL as [<- [_ [LO HI]]].
    assert (SUM : contains (sum_interval a c) (L.eval_expr env (L.Sum e1 e2))).
    { unfold contains, sum_interval in *. cbn [lower upper L.eval_expr] in *; lia. }
    split; [exact SUM |]. cbn [affine_safe].
    split; [exact SAFE_A |]. split; [exact SAFE_C |].
    exact (interval_range LO HI SUM).
  - destruct (checked (Interval z z)) as [coefficient|] eqn:K; try discriminate.
    destruct (analyze bounds e) as [a|] eqn:A; try discriminate.
    destruct (IHe _ _ _ A VIEW) as [EA SAFE_A].
    apply checked_sound in K. destruct K as [_ [_ [KLO KHI]]].
    cbn [lower upper] in KLO, KHI.
    apply checked_sound in ANAL. destruct ANAL as [<- [_ [LO HI]]].
    assert (PRODUCT : contains (scaled_interval z a) (L.eval_expr env (L.Mult z e))).
    { unfold scaled_interval. destruct (0 <=? z) eqn:SIGN;
        unfold contains in *; cbn [lower upper L.eval_expr] in *.
      - apply Z.leb_le in SIGN; nia.
      - apply Z.leb_gt in SIGN; nia. }
    split; [exact PRODUCT |]. cbn [affine_safe].
    split; [unfold machine_range; auto |]. split; [exact SAFE_A |].
    exact (interval_range LO HI PRODUCT).
  - destruct (nth_error bounds n) as [a|] eqn:A; try discriminate.
    apply checked_sound in ANAL. destruct ANAL as [<- [_ [LO HI]]].
    pose proof (VIEW _ _ A) as CONTAINS.
    split; auto. cbn [L.eval_expr affine_safe].
    exact (interval_range LO HI CONTAINS).
Qed.

Fixpoint lower_expr (layout : list ident) (e : L.expr) : option Clight.expr :=
  match e with
  | L.Constant z =>
      if interval_valid (Interval z z)
      then Some (Econst_int (Int.repr z) type_int32s) else None
  | L.Var n =>
      match nth_error layout n with
      | Some id => Some (Etempvar id type_int32s) | None => None end
  | L.Sum x y =>
      match lower_expr layout x, lower_expr layout y with
      | Some a, Some b => Some (Ebinop Oadd a b type_int32s) | _, _ => None end
  | L.Mult k x =>
      if interval_valid (Interval k k) then
      match lower_expr layout x with
      | Some a => Some (Ebinop Omul (Econst_int (Int.repr k) type_int32s)
          a type_int32s) | None => None end else None
  | _ => None
  end.

Lemma lower_expr_type e : forall layout c,
  lower_expr layout e = Some c -> typeof c = type_int32s.
Proof.
  induction e; intros layout c LOWER; cbn [lower_expr] in LOWER;
    repeat match type of LOWER with
      | context [match ?x with _ => _ end] => let EQ := fresh "CASE" in destruct x eqn:EQ
      end; try discriminate; inversion LOWER; reflexivity.
Qed.

Arguments lower_expr_type e {layout c} _.

Lemma lower_expr_pure e : forall layout c,
  lower_expr layout e = Some c -> pure_scalar c.
Proof.
  induction e; intros layout c LOWER; cbn [lower_expr] in LOWER;
    repeat match type of LOWER with
      | context [match ?x with _ => _ end] => let EQ := fresh "CASE" in destruct x eqn:EQ
      end; try discriminate; inversion LOWER; subst; constructor; eauto;
      constructor.
Qed.

Arguments lower_expr_pure e {layout c} _.

Definition typed_view (layout : list ident) (env : list Z) (le : temp_env) : Prop :=
  forall n id, nth_error layout n = Some id ->
  exists value, le ! id = Some (Vint value) /\ Int.signed value = nth n env 0.

Lemma affine_safe_range e env : affine_safe e env -> machine_range (L.eval_expr env e).
Proof. destruct e; cbn [affine_safe L.eval_expr]; tauto. Qed.

Theorem lower_expr_correct e : forall layout c env le,
  lower_expr layout e = Some c -> affine_safe e env -> typed_view layout env le ->
  forall ge locals m,
  eval_expr ge locals le m c (Vint (Int.repr (L.eval_expr env e))).
Proof.
  induction e; intros layout c env le LOWER SAFE VIEW ge locals m;
    cbn [lower_expr] in LOWER; cbn [affine_safe] in SAFE; try contradiction.
  - destruct (interval_valid (Interval z z)); try discriminate.
    inversion LOWER; subst. constructor.
  - destruct (lower_expr layout e1) as [a|] eqn:A; try discriminate.
    destruct (lower_expr layout e2) as [b|] eqn:B; try discriminate.
    inversion LOWER; subst. destruct SAFE as [SA [SB SR]].
    eapply eval_Ebinop.
    + eapply IHe1; eauto.
    + eapply IHe2; eauto.
    + rewrite (lower_expr_type e1 A), (lower_expr_type e2 B).
      change (Some (Vint (Int.add (Int.repr (L.eval_expr env e1))
        (Int.repr (L.eval_expr env e2)))) =
        Some (Vint (Int.repr (L.eval_expr env (L.Sum e1 e2))))).
      rewrite Int.add_signed, !Int.signed_repr.
      * reflexivity.
      * destruct e2; cbn [affine_safe] in SB; tauto.
      * destruct e1; cbn [affine_safe] in SA; tauto.
  - destruct (interval_valid (Interval z z)); try discriminate.
    destruct (lower_expr layout e) as [a|] eqn:A; try discriminate.
    inversion LOWER; subst. destruct SAFE as [SK [SA SR]].
    eapply eval_Ebinop.
    + constructor.
    + eapply IHe; eauto.
    + rewrite (lower_expr_type e A). cbn [typeof].
      change (Some (Vint (Int.mul (Int.repr z) (Int.repr (L.eval_expr env e)))) =
        Some (Vint (Int.repr (L.eval_expr env (L.Mult z e))))).
      rewrite Int.mul_signed, !Int.signed_repr.
      * reflexivity.
      * destruct e; cbn [affine_safe] in SA; tauto.
      * exact SK.
  - destruct (nth_error layout n) as [id|] eqn:ID; try discriminate.
    inversion LOWER; subst.
    destruct (VIEW _ _ ID) as [value [TEMP SIGNED]].
    cbn [L.eval_expr]. rewrite <- SIGNED, Int.repr_signed. constructor; auto.
Qed.

Definition compile_expr (layout : list ident) (bounds : list interval) (e : L.expr) :
  option (Clight.expr * interval) :=
  match analyze bounds e, lower_expr layout e with
  | Some b, Some c => Some (c, b) | _, _ => None end.

Theorem compile_expr_sound layout bounds e c b env le :
  compile_expr layout bounds e = Some (c, b) ->
  env_within bounds env -> typed_view layout env le ->
  typeof c = type_int32s /\ machine_range (L.eval_expr env e) /\
  contains b (L.eval_expr env e) /\
  forall ge locals m,
    eval_expr ge locals le m c (Vint (Int.repr (L.eval_expr env e))).
Proof.
  unfold compile_expr. destruct (analyze bounds e) as [ib|] eqn:ANAL; try discriminate.
  destruct (lower_expr layout e) as [code|] eqn:LOWER; try discriminate.
  intros EQ ENV VIEW. inversion EQ; subst.
  destruct (analyze_sound e ANAL ENV) as [CONTAINS SAFE].
  split; [eapply lower_expr_type; eauto |].
  split; [apply affine_safe_range; auto |].
  split; auto. eapply lower_expr_correct; eauto.
Qed.

Lemma compiled_expr_pure layout bounds e c b :
  compile_expr layout bounds e = Some (c, b) -> pure_scalar c.
Proof.
  unfold compile_expr. destruct (analyze bounds e); try discriminate.
  destruct (lower_expr layout e) eqn:LOWER; try discriminate.
  intro EQ; inversion EQ; subst. eapply lower_expr_pure; eauto.
Qed.

Fixpoint lower_test (layout : list ident) (bounds : list interval) (t : L.test) :
  option decision_tree :=
  match t with
  | L.LE x y | L.EQ x y =>
      match compile_expr layout bounds x, compile_expr layout bounds y with
      | Some (a, _), Some (b, _) =>
          Some (Test (Ebinop (match t with L.LE _ _ => Ole | _ => Oeq end)
            a b type_int32s) (Decision true) (Decision false))
      | _, _ => None end
  | L.And x y =>
      match lower_test layout bounds x, lower_test layout bounds y with
      | Some a, Some b => Some (decision_bind a b (Decision false)) | _, _ => None end
  | L.Or x y =>
      match lower_test layout bounds x, lower_test layout bounds y with
      | Some a, Some b => Some (decision_bind a (Decision true) b) | _, _ => None end
  | L.Not x =>
      match lower_test layout bounds x with
      | Some a => Some (decision_bind a (Decision false) (Decision true)) | _ => None end
  | L.TConstantTest b => Some (Decision b)
  end.

Lemma signed_le_exact x y : machine_range x -> machine_range y ->
  Int.cmp Cle (Int.repr x) (Int.repr y) = (x <=? y).
Proof.
  intros RX RY. unfold Int.cmp, Int.lt.
  rewrite !Int.signed_repr by assumption.
  destruct (zlt y x); simpl; symmetry.
  - apply Z.leb_gt; auto.
  - apply Z.leb_le; lia.
Qed.

Lemma signed_eq_exact x y : machine_range x -> machine_range y ->
  Int.cmp Ceq (Int.repr x) (Int.repr y) = (x =? y).
Proof.
  intros RX RY. cbn [Int.cmp]. rewrite Int.eq_signed.
  rewrite !Int.signed_repr by assumption.
  destruct (zeq x y); simpl; symmetry.
  - apply Z.eqb_eq; auto.
  - apply Z.eqb_neq; auto.
Qed.

Lemma lower_test_pure t : forall layout bounds tree,
  lower_test layout bounds t = Some tree -> pure_tree tree.
Proof.
  induction t; intros layout bounds tree LOWER; cbn [lower_test] in LOWER.
  - destruct (compile_expr layout bounds e) as [[a ia]|] eqn:A; try discriminate.
    destruct (compile_expr layout bounds e0) as [[b ib]|] eqn:B; try discriminate.
    inversion LOWER; subst. apply pure_test.
    + apply pure_binary; eapply compiled_expr_pure; eauto.
    + constructor.
    + constructor.
  - destruct (compile_expr layout bounds e) as [[a ia]|] eqn:A; try discriminate.
    destruct (compile_expr layout bounds e0) as [[b ib]|] eqn:B; try discriminate.
    inversion LOWER; subst. apply pure_test.
    + apply pure_binary; eapply compiled_expr_pure; eauto.
    + constructor.
    + constructor.
  - destruct (lower_test layout bounds t1) eqn:A; try discriminate.
    destruct (lower_test layout bounds t2) eqn:B; try discriminate.
    inversion LOWER; subst. apply pure_decision_bind; eauto; constructor.
  - destruct (lower_test layout bounds t1) eqn:A; try discriminate.
    destruct (lower_test layout bounds t2) eqn:B; try discriminate.
    inversion LOWER; subst. apply pure_decision_bind; eauto; constructor.
  - destruct (lower_test layout bounds t) eqn:A; try discriminate.
    inversion LOWER; subst. apply pure_decision_bind; eauto; constructor.
  - inversion LOWER; subst; constructor.
Qed.

Theorem lower_test_correct t : forall layout bounds tree env le,
  lower_test layout bounds t = Some tree ->
  env_within bounds env -> typed_view layout env le -> forall ge locals m,
  decision_run (Entry ge locals le m) tree (L.eval_test env t).
Proof.
  induction t; intros layout bounds tree env le LOWER ENV VIEW ge locals m;
    cbn [lower_test] in LOWER.
  - destruct (compile_expr layout bounds e) as [[a ia]|] eqn:A; try discriminate.
    destruct (compile_expr layout bounds e0) as [[b ib]|] eqn:B; try discriminate.
    inversion LOWER; subst.
    destruct (compile_expr_sound e A ENV VIEW) as [TA [RA [_ EA]]].
    destruct (compile_expr_sound e0 B ENV VIEW) as [TB [RB [_ EB]]].
    eapply run_test with (b := L.eval_test env (L.LE e e0));
      [|destruct (L.eval_test env (L.LE e e0)); constructor].
    unfold expression_test. exists (Val.of_bool (L.eval_test env (L.LE e e0))). split.
    + eapply eval_Ebinop; [apply EA | apply EB |].
      rewrite TA, TB. change
        (Some (Val.of_bool (Int.cmp Cle (Int.repr (L.eval_expr env e))
          (Int.repr (L.eval_expr env e0)))) =
         Some (Val.of_bool (L.eval_test env (L.LE e e0)))).
      rewrite signed_le_exact by assumption; reflexivity.
    + destruct (L.eval_test env (L.LE e e0)); reflexivity.
  - destruct (compile_expr layout bounds e) as [[a ia]|] eqn:A; try discriminate.
    destruct (compile_expr layout bounds e0) as [[b ib]|] eqn:B; try discriminate.
    inversion LOWER; subst.
    destruct (compile_expr_sound e A ENV VIEW) as [TA [RA [_ EA]]].
    destruct (compile_expr_sound e0 B ENV VIEW) as [TB [RB [_ EB]]].
    eapply run_test with (b := L.eval_test env (L.EQ e e0));
      [|destruct (L.eval_test env (L.EQ e e0)); constructor].
    unfold expression_test. exists (Val.of_bool (L.eval_test env (L.EQ e e0))). split.
    + eapply eval_Ebinop; [apply EA | apply EB |].
      rewrite TA, TB. change
        (Some (Val.of_bool (Int.cmp Ceq (Int.repr (L.eval_expr env e))
          (Int.repr (L.eval_expr env e0)))) =
         Some (Val.of_bool (L.eval_test env (L.EQ e e0)))).
      rewrite signed_eq_exact by assumption; reflexivity.
    + destruct (L.eval_test env (L.EQ e e0)); reflexivity.
  - destruct (lower_test layout bounds t1) as [a|] eqn:A; try discriminate.
    destruct (lower_test layout bounds t2) as [b|] eqn:B; try discriminate.
    inversion LOWER; subst. cbn [L.eval_test]. eapply decision_bind_run.
    + eapply IHt1; eauto.
    + destruct (L.eval_test env t1); cbn [andb]; [eapply IHt2; eauto | constructor].
  - destruct (lower_test layout bounds t1) as [a|] eqn:A; try discriminate.
    destruct (lower_test layout bounds t2) as [b|] eqn:B; try discriminate.
    inversion LOWER; subst. cbn [L.eval_test]. eapply decision_bind_run.
    + eapply IHt1; eauto.
    + destruct (L.eval_test env t1); cbn [orb]; [constructor | eapply IHt2; eauto].
  - destruct (lower_test layout bounds t) as [a|] eqn:A; try discriminate.
    inversion LOWER; subst. cbn [L.eval_test]. eapply decision_bind_run.
    + eapply IHt; eauto.
    + destruct (L.eval_test env t); constructor.
  - inversion LOWER; subst; constructor.
Qed.

Theorem lower_test_exact t layout bounds tree env le ge locals m result :
  lower_test layout bounds t = Some tree ->
  env_within bounds env -> typed_view layout env le ->
  (decision_run (Entry ge locals le m) tree result <-> result = L.eval_test env t).
Proof.
  intros LOWER ENV VIEW. split.
  - intro RUN. eapply pure_tree_determinate; [eapply lower_test_pure; eauto | exact RUN |].
    eapply lower_test_correct; eauto.
  - intro EQ; subst; eapply lower_test_correct; eauto.
Qed.

Example doubled_plus_one_boundary :
  analyze [Interval 0 1073741823] (L.Sum (L.Mult 2 (L.Var 0)) (L.Constant 1)) =
    Some (Interval 1 2147483647).
Proof. vm_compute; reflexivity. Qed.

Example doubled_plus_one_full_range_refused :
  analyze [Interval (-2147483648) 2147483647]
    (L.Sum (L.Mult 2 (L.Var 0)) (L.Constant 1)) = None.
Proof. vm_compute; reflexivity. Qed.

Example negative_coefficient :
  analyze [Interval (-3) 4] (L.Mult (-2) (L.Var 0)) = Some (Interval (-8) 6).
Proof. vm_compute; reflexivity. Qed.

Example negation_minimum_overflow_refused :
  analyze [Interval (-2147483648) 2147483647] (L.Mult (-1) (L.Var 0)) = None.
Proof. vm_compute; reflexivity. Qed.

Example unsupported_division_refused :
  analyze [Interval 0 10] (L.Div (L.Var 0) 2) = None.
Proof. vm_compute; reflexivity. Qed.

End PolCertAffineClightFor.

Module PolCertAffineClight (I : INSTR).
Module ConcreteLoop := Loop I.
Include PolCertAffineClightFor I ConcreteLoop.

Print Assumptions analyze_sound.
Print Assumptions lower_expr_correct.
Print Assumptions compile_expr_sound.
Print Assumptions lower_test_exact.

End PolCertAffineClight.
