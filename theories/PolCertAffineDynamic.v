From Stdlib Require Import Bool List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From polcert.polygen Require Import InstrTy Loop.
From Guard Require Import AbstractGuard SemanticFacts PolCertLoopGuard PolCertAffineClight ClightCondition
  ClightPureExpr ClightWideGuard.
Set Implicit Arguments.
Open Scope Z_scope.

(** No proposed input intervals: checks follow expression dependencies, and
    wider operations are reached only after signed32 operand safety succeeds. *)
Module PolCertAffineDynamicFor (I : INSTR) (M : LOOP_MODEL I).
Module L := M.
Module A := PolCertAffineClightFor I M.

Fixpoint safety_bool e env : bool :=
  match e with
  | L.Constant z => word_range_bool z
  | L.Var n => word_range_bool (nth n env 0)
  | L.Sum x y => safety_bool x env && safety_bool y env && word_range_bool (L.eval_expr env e)
  | L.Mult k x => word_range_bool k && safety_bool x env && word_range_bool (L.eval_expr env e)
  | _ => false end.

Lemma safety_bool_spec e env : safety_bool e env = true <-> A.affine_safe e env.
Proof.
  induction e; cbn [safety_bool A.affine_safe];
    try (split; [discriminate | tauto]).
  - apply word_range_bool_spec.
  - rewrite !andb_true_iff, word_range_bool_spec, IHe1, IHe2; tauto.
  - rewrite !andb_true_iff, !word_range_bool_spec, IHe; tauto.
  - apply word_range_bool_spec.
Qed.

Fixpoint compile_dynamic layout e : option (expr * decision_tree) :=
  match e with
  | L.Constant _ | L.Var _ =>
      match A.lower_expr layout e with Some code => Some (code, Decision true) | None => None end
  | L.Sum x y =>
      match compile_dynamic layout x, compile_dynamic layout y with
      | Some (a, tree_left), Some (b, tree_right) =>
          Some (Ebinop Oadd a b type_int32s,
            decision_bind tree_left (decision_bind tree_right (wide_bounds_tree (wide_add a b))
              (Decision false)) (Decision false))
      | _, _ => None end
  | L.Mult k x =>
      match A.lower_expr layout (L.Constant k), compile_dynamic layout x with
      | Some coefficient, Some (a, child) =>
          Some (Ebinop Omul coefficient a type_int32s,
            decision_bind child (wide_bounds_tree (wide_mul coefficient a)) (Decision false))
      | _, _ => None end
  | _ => None end.

Lemma compile_dynamic_lower e : forall layout code tree,
  compile_dynamic layout e = Some (code, tree) -> A.lower_expr layout e = Some code.
Proof.
  induction e; intros layout code tree COMPILE; cbn [compile_dynamic] in COMPILE;
    try discriminate.
  - destruct (A.lower_expr layout (L.Constant z)) eqn:LOWER; try discriminate.
    inversion COMPILE; subst; reflexivity.
  - destruct (compile_dynamic layout e1) as [[a tree_left]|] eqn:LEFT; try discriminate.
    destruct (compile_dynamic layout e2) as [[b tree_right]|] eqn:RIGHT; try discriminate.
    inversion COMPILE; subst. cbn [A.lower_expr].
    rewrite (IHe1 _ _ _ LEFT), (IHe2 _ _ _ RIGHT); reflexivity.
  - destruct (A.lower_expr layout (L.Constant z)) eqn:COEFFICIENT; try discriminate.
    destruct (compile_dynamic layout e) as [[a child]|] eqn:CHILD; try discriminate.
    inversion COMPILE; subst. cbn [A.lower_expr] in COEFFICIENT |- *.
    destruct (A.interval_valid (A.Interval z z)); try discriminate.
    inversion COEFFICIENT; subst. rewrite (IHe _ _ _ CHILD); reflexivity.
  - destruct (A.lower_expr layout (L.Var n)) eqn:LOWER; try discriminate.
    inversion COMPILE; subst; reflexivity.
Qed.

Arguments compile_dynamic_lower e {layout code tree} _.

Lemma compile_dynamic_pure e : forall layout code tree,
  compile_dynamic layout e = Some (code, tree) -> pure_tree tree.
Proof.
  induction e; intros layout code tree COMPILE; cbn [compile_dynamic] in COMPILE;
    try discriminate.
  - destruct (A.lower_expr layout (L.Constant z)); try discriminate.
    inversion COMPILE; subst; constructor.
  - destruct (compile_dynamic layout e1) as [[a tree_left]|] eqn:LEFT; try discriminate.
    destruct (compile_dynamic layout e2) as [[b tree_right]|] eqn:RIGHT; try discriminate.
    inversion COMPILE; subst. apply pure_decision_bind; [eapply IHe1; eauto | | constructor].
    apply pure_decision_bind; [eapply IHe2; eauto | | constructor].
    apply wide_bounds_pure. constructor; constructor;
      eapply A.lower_expr_pure; eapply compile_dynamic_lower; eauto.
  - destruct (A.lower_expr layout (L.Constant z)) eqn:COEFFICIENT; try discriminate.
    destruct (compile_dynamic layout e) as [[a child]|] eqn:CHILD; try discriminate.
    inversion COMPILE; subst. apply pure_decision_bind; [eapply IHe; eauto | | constructor].
    apply wide_bounds_pure. constructor; constructor;
      eapply A.lower_expr_pure; eauto using compile_dynamic_lower.
  - destruct (A.lower_expr layout (L.Var n)); try discriminate.
    inversion COMPILE; subst; constructor.
Qed.

Lemma lowered_constant_range layout z code : A.lower_expr layout (L.Constant z) = Some code ->
  word_range z.
Proof.
  cbn [A.lower_expr]. destruct (A.interval_valid (A.Interval z z)) eqn:VALID;
    try discriminate.
  intros _. unfold A.interval_valid in VALID.
  repeat rewrite andb_true_iff in VALID; repeat rewrite Z.leb_le in VALID.
  cbn [A.lower A.upper] in VALID. unfold word_range; tauto.
Qed.

Theorem compile_dynamic_run e : forall layout code tree env le,
  compile_dynamic layout e = Some (code, tree) -> A.typed_view layout env le ->
  forall ge locals m, decision_run (Entry ge locals le m) tree (safety_bool e env).
Proof.
  induction e; intros layout code tree env le COMPILE VIEW ge locals m;
    cbn [compile_dynamic] in COMPILE; try discriminate.
  - destruct (A.lower_expr layout (L.Constant z)) as [constant|] eqn:LOWER; try discriminate.
    inversion COMPILE; subst. cbn [safety_bool].
    assert (RANGE : word_range z) by (eapply lowered_constant_range; eauto).
    apply word_range_bool_spec in RANGE; rewrite RANGE; constructor.
  - destruct (compile_dynamic layout e1) as [[a tree_left]|] eqn:LEFT; try discriminate.
    destruct (compile_dynamic layout e2) as [[b tree_right]|] eqn:RIGHT; try discriminate.
    inversion COMPILE; subst. cbn [safety_bool].
    eapply decision_bind_run with (b := safety_bool e1 env).
    + eapply IHe1; eauto.
    + destruct (safety_bool e1 env) eqn:S1; cbn [andb]; [|constructor].
      eapply decision_bind_run with (b := safety_bool e2 env).
      * eapply IHe2; eauto.
      * destruct (safety_bool e2 env) eqn:S2; cbn [andb]; [|constructor].
        apply safety_bool_spec in S1, S2.
        pose proof (compile_dynamic_lower e1 LEFT) as LA.
        pose proof (compile_dynamic_lower e2 RIGHT) as LB.
        pose proof (A.affine_safe_range e1 env S1) as R1.
        pose proof (A.affine_safe_range e2 env S2) as R2.
        eapply wide_bounds_run.
        -- reflexivity.
        -- cbn [L.eval_expr]. apply word_sum_is_long; assumption.
        -- cbn [L.eval_expr]. eapply wide_add_eval.
           ++ eapply A.lower_expr_type; exact LA.
           ++ eapply A.lower_expr_type; exact LB.
           ++ exact R1.
           ++ exact R2.
           ++ eapply A.lower_expr_correct; eauto.
           ++ eapply A.lower_expr_correct; eauto.
  - destruct (A.lower_expr layout (L.Constant z)) as [coefficient|] eqn:COEFFICIENT;
      try discriminate.
    destruct (compile_dynamic layout e) as [[a child]|] eqn:CHILD; try discriminate.
    inversion COMPILE; subst. cbn [safety_bool].
    assert (RK : word_range z) by (eapply lowered_constant_range; eauto).
    assert (K : word_range_bool z = true) by (apply word_range_bool_spec; exact RK).
    rewrite K; cbn [andb].
    eapply decision_bind_run with (b := safety_bool e env).
    + eapply IHe; eauto.
    + destruct (safety_bool e env) eqn:S; cbn [andb]; [|constructor].
      apply safety_bool_spec in S. pose proof (A.affine_safe_range e env S) as R.
      pose proof (compile_dynamic_lower e CHILD) as LOWER.
      eapply wide_bounds_run.
      * reflexivity.
      * cbn [L.eval_expr]. apply word_product_is_long; assumption.
      * cbn [L.eval_expr]. eapply wide_mul_eval.
        -- eapply A.lower_expr_type; exact COEFFICIENT.
        -- eapply A.lower_expr_type; exact LOWER.
        -- exact RK.
        -- exact R.
        -- exact (@A.lower_expr_correct (L.Constant z) layout coefficient env le
             COEFFICIENT RK VIEW ge locals m).
        -- eapply A.lower_expr_correct; eauto.
  - destruct (A.lower_expr layout (L.Var n)) as [variable|] eqn:LOWER; try discriminate.
    inversion COMPILE; subst. cbn [A.lower_expr] in LOWER.
    destruct (nth_error layout n) as [id|] eqn:INDEX; try discriminate.
    destruct (VIEW _ _ INDEX) as [value [LOOKUP SIGNED]].
    cbn [safety_bool]. rewrite <- SIGNED.
    assert (RANGE : word_range_bool (Int.signed value) = true).
    { apply word_range_bool_spec. apply Int.signed_range. }
    rewrite RANGE; constructor.
Qed.

Theorem compile_dynamic_exact e layout code tree env le ge locals m result :
  compile_dynamic layout e = Some (code, tree) -> A.typed_view layout env le ->
  (decision_run (Entry ge locals le m) tree result <-> result = safety_bool e env).
Proof.
  intros COMPILE VIEW; split.
  - intro RUN. eapply pure_tree_determinate;
      [eapply compile_dynamic_pure; eauto | exact RUN | eapply compile_dynamic_run; eauto].
  - intro EQ; subst; eapply compile_dynamic_run; eauto.
Qed.

Theorem compile_dynamic_accepted e layout code tree env le ge locals m :
  compile_dynamic layout e = Some (code, tree) -> A.typed_view layout env le ->
  decision_run (Entry ge locals le m) tree true ->
  A.affine_safe e env /\ eval_expr ge locals le m code (Vint (Int.repr (L.eval_expr env e))).
Proof.
  intros COMPILE VIEW ACCEPT.
  pose proof (proj1 (@compile_dynamic_exact e layout code tree env le ge locals m true
    COMPILE VIEW) ACCEPT) as SAFE.
  symmetry in SAFE. apply safety_bool_spec in SAFE. split; auto.
  eapply A.lower_expr_correct; eauto using compile_dynamic_lower.
Qed.

Definition dynamic_decide layout env e (_ : clight_entry) :=
  match compile_dynamic layout e with Some _ => Some (safety_bool e env) | None => None end.

Definition dynamic_domain layout env (s : clight_entry) :=
  A.typed_view layout env (entry_temps s).

Definition dynamic_dimension layout env :
  property_dimension clight_entry L.expr (dynamic_domain layout env).
Proof.
  refine {| atom_property := fun e _ => A.affine_safe e env;
    decide_atom := dynamic_decide layout env |}.
  intros e s result VIEW CHECK. unfold dynamic_decide in CHECK.
  destruct (compile_dynamic layout e); try discriminate.
  inversion CHECK; subst. destruct (safety_bool e env) eqn:SAFE; cbn [decision_evidence].
  - apply safety_bool_spec; exact SAFE.
  - intro SAFE'. apply safety_bool_spec in SAFE'; congruence.
Defined.

Definition dynamic_validity layout e :=
  Decision (match compile_dynamic layout e with Some _ => true | None => false end).
Definition dynamic_value layout e :=
  match compile_dynamic layout e with Some (_, tree) => tree | None => Decision false end.

Definition dynamic_primitives layout env :
  check_primitives decision_test_language (dynamic_domain layout env) (dynamic_decide layout env).
Proof.
  refine (@CheckPrimitives clight_entry L.expr decision_test_language
    (dynamic_domain layout env) (dynamic_decide layout env)
    (dynamic_validity layout) (dynamic_value layout) _ _).
  - intros e s result VIEW. cbn [decision_test_language].
    unfold dynamic_validity, dynamic_decide.
    destruct (compile_dynamic layout e); cbn [checked_valid]; split; intro RUN;
      try (inversion RUN; reflexivity); subst; constructor.
  - intros e s result expected VIEW CHECK. cbn [decision_test_language].
    unfold dynamic_decide in CHECK. destruct (compile_dynamic layout e) as [[code tree]|]
      eqn:COMPILE; try discriminate.
    inversion CHECK; subst expected. unfold dynamic_value; rewrite COMPILE.
    destruct s as [ge locals le m].
    exact (@compile_dynamic_exact e layout code tree env le ge locals m result COMPILE VIEW).
Defined.

Definition dynamic_formula_guard layout (p : formula L.expr) : decision_tree :=
  compile_condition (dynamic_primitives layout nil) p (Decision true) (Decision false) (Decision false).

Lemma dynamic_compile_environment layout env p : forall yes no unknown,
  compile_condition (dynamic_primitives layout nil) p yes no unknown =
    compile_condition (dynamic_primitives layout env) p yes no unknown.
Proof.
  induction p; intros yes no unknown; cbn [compile_condition]; try reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - apply IHp.
Qed.

Theorem dynamic_formula_guard_exact layout env p s result : dynamic_domain layout env s ->
  (decision_run s (dynamic_formula_guard layout p) result <->
    result = formula_accepts (dynamic_decide layout env) p s).
Proof.
  intro DOMAIN. unfold dynamic_formula_guard. rewrite (dynamic_compile_environment layout env p).
  change (command_run decision_test_language
    (compile_condition (dynamic_primitives layout env) p
      (Decision true) (Decision false) (Decision false)) s result <->
    result = formula_accepts (dynamic_decide layout env) p s).
  rewrite compile_condition_correct by exact DOMAIN.
  unfold formula_accepts. destruct (formula_execute (dynamic_decide layout env) p s)
    as [value|]; [destruct value|]; cbn [selected_command decision_test_language];
    split; intro RUN; try (inversion RUN; reflexivity); subst; constructor.
Qed.

Theorem dynamic_formula_guard_property layout env p s : dynamic_domain layout env s ->
  decision_run s (dynamic_formula_guard layout p) true ->
  formula_property (fun e _ => A.affine_safe e env) p s.
Proof.
  intros DOMAIN GUARD.
  pose proof (proj1 (@dynamic_formula_guard_exact layout env p s true DOMAIN) GUARD) as RUN.
  unfold formula_accepts in RUN.
  destruct (formula_execute (dynamic_decide layout env) p s) as [value|] eqn:EXEC;
    try discriminate. destruct value; try discriminate.
  exact (@formula_property_decision clight_entry L.expr (dynamic_domain layout env)
    (dynamic_dimension layout env) p s true DOMAIN EXEC).
Qed.

Example doubled_plus_one_dynamic_boundary :
  safety_bool (L.Sum (L.Mult 2 (L.Var 0)) (L.Constant 1)) (1073741823 :: nil) = true /\
  safety_bool (L.Sum (L.Mult 2 (L.Var 0)) (L.Constant 1)) (1073741824 :: nil) = false.
Proof. vm_compute; split; reflexivity. Qed.

Example safe_final_value_unsafe_intermediate :
  safety_bool (L.Sum (L.Sum (L.Var 0) (L.Constant 1)) (L.Constant (-1)))
    (2147483647 :: nil) = false.
Proof. vm_compute; reflexivity. Qed.

Example unsupported_under_complement env s :
  formula_execute (dynamic_decide (1%positive :: nil) env)
    (Complement (Fact (L.Div (L.Var 0) 2))) s = None.
Proof. reflexivity. Qed.

End PolCertAffineDynamicFor.

Module PolCertAffineDynamic (I : INSTR).
Module ConcreteLoop := Loop I.
Include PolCertAffineDynamicFor I ConcreteLoop.
Print Assumptions safety_bool_spec.
Print Assumptions compile_dynamic_exact.
Print Assumptions compile_dynamic_accepted.
Print Assumptions dynamic_primitives.
Print Assumptions dynamic_formula_guard_property.
End PolCertAffineDynamic.
