From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From polcert.polygen Require Import InstrTy Loop.
From Guard Require Import AbstractGuard SemanticFacts PolCertLoopGuard
  ClightCondition ClightPureExpr PolCertAffineClight.
Import ListNotations.
Open Scope Z_scope.
Set Implicit Arguments.

(** This dimension observes only signed integer temporaries. Its executable
    encoding does not depend on the mathematical environment used in proofs.
    Unsupported layouts and invalid interval proposals return unknown. *)
Module PolCertAffineGuardFor (I : INSTR) (M : LOOP_MODEL I).
Module A := PolCertAffineClightFor I M.
Module L := M.
Import A.

Record range_atom := RangeAtom { range_index : nat; lower_side : bool }.

Definition binding layout bounds a : option (ident * interval) :=
  match nth_error layout (range_index a), nth_error bounds (range_index a) with
  | Some id, Some b => if interval_valid b then Some (id, b) else None
  | _, _ => None end.

Lemma binding_sound layout bounds a id b : binding layout bounds a = Some (id, b) ->
  nth_error layout (range_index a) = Some id /\
  nth_error bounds (range_index a) = Some b /\ interval_valid b = true.
Proof.
  unfold binding. destruct (nth_error layout _) as [temp|] eqn:ID; try discriminate.
  destruct (nth_error bounds _) as [bound|] eqn:BOUND; try discriminate.
  destruct (interval_valid bound) eqn:VALID; try discriminate.
  intro EQ; inversion EQ; subst; auto.
Qed.

Arguments binding_sound {layout bounds a id b} _.

Definition atom_value env a b :=
  if lower_side a then lower b <=? nth (range_index a) env 0
  else nth (range_index a) env 0 <=? upper b.

Definition range_property bounds env a (_ : clight_entry) : Prop :=
  match nth_error bounds (range_index a) with
  | Some b => if lower_side a then lower b <= nth (range_index a) env 0
              else nth (range_index a) env 0 <= upper b
  | None => False end.

Definition atom_decide layout bounds env a (_ : clight_entry) : option bool :=
  match binding layout bounds a with
  | Some (_, b) => Some (atom_value env a b) | None => None end.

Definition range_domain layout env (s : clight_entry) :=
  typed_view layout env (entry_temps s).

Definition range_dimension (layout : list ident) (bounds : list interval) (env : list Z) :
  property_dimension clight_entry range_atom (range_domain layout env).
Proof.
  refine {| atom_property := range_property bounds env;
            decide_atom := atom_decide layout bounds env |}.
  intros a s result VIEW CHECK. unfold atom_decide in CHECK.
  destruct (binding layout bounds a) as [[id b]|] eqn:BIND; try discriminate.
  inversion CHECK; subst. destruct (binding_sound BIND) as [_ [BOUND _]].
  unfold range_property; rewrite BOUND. unfold atom_value.
  destruct (lower_side a); cbn [decision_evidence];
    destruct (_ <=? _) eqn:LE; cbn;
    [apply Z.leb_le in LE | apply Z.leb_gt in LE |
     apply Z.leb_le in LE | apply Z.leb_gt in LE]; lia.
Defined.

Definition boolean_expr (b : bool) :=
  Econst_int (if b then Int.one else Int.zero) type_int32s.

Lemma boolean_expr_test s value result :
  expression_test (boolean_expr value) s result <-> result = value.
Proof.
  assert (KNOWN : expression_test (boolean_expr value) s value).
  { unfold expression_test, boolean_expr.
    exists (Vint (if value then Int.one else Int.zero)).
    split; [constructor | destruct value; reflexivity]. }
  split.
  - intro RUN. eapply pure_test_determinate; [constructor | exact RUN | exact KNOWN].
  - intro EQ; subst; exact KNOWN.
Qed.

Definition validity_expr layout bounds a :=
  boolean_expr (match binding layout bounds a with Some _ => true | None => false end).

Definition value_expr layout bounds a :=
  match binding layout bounds a with
  | Some (id, b) =>
      if lower_side a then Ebinop Ole (Econst_int (Int.repr (lower b)) type_int32s)
        (Etempvar id type_int32s) type_int32s
      else Ebinop Ole (Etempvar id type_int32s)
        (Econst_int (Int.repr (upper b)) type_int32s) type_int32s
  | None => boolean_expr false end.

Lemma value_expr_pure layout bounds a : pure_scalar (value_expr layout bounds a).
Proof.
  unfold value_expr. destruct (binding layout bounds a) as [[id b]|];
    [destruct (lower_side a) |]; constructor; constructor.
Qed.

Lemma value_expr_run layout bounds env a s id b :
  binding layout bounds a = Some (id, b) -> range_domain layout env s ->
  expression_test (value_expr layout bounds a) s (atom_value env a b).
Proof.
  intros BIND VIEW. destruct s as [ge locals le m]; cbn in *.
  destruct (binding_sound BIND) as [ID [BOUND VALID]].
  destruct (VIEW _ _ ID) as [value [LOOKUP SIGNED]].
  assert (RANGE : machine_range (nth (range_index a) env 0)).
  { rewrite <- SIGNED. apply Int.signed_range. }
  assert (LO : machine_range (lower b)).
  { unfold interval_valid in VALID.
    repeat rewrite andb_true_iff in VALID; repeat rewrite Z.leb_le in VALID.
    unfold machine_range; lia. }
  assert (HI : machine_range (upper b)).
  { unfold interval_valid in VALID.
    repeat rewrite andb_true_iff in VALID; repeat rewrite Z.leb_le in VALID.
    unfold machine_range; lia. }
  assert (TEMP : eval_expr ge locals le m (Etempvar id type_int32s)
    (Vint (Int.repr (nth (range_index a) env 0)))).
  { rewrite <- SIGNED, Int.repr_signed. constructor; exact LOOKUP. }
  unfold value_expr; rewrite BIND. unfold atom_value.
  unfold expression_test; cbn [entry_ge entry_env entry_temps entry_memory].
  destruct (lower_side a).
  - exists (Val.of_bool (lower b <=? nth (range_index a) env 0)); split.
    + eapply eval_Ebinop; [constructor | exact TEMP |].
      cbn [typeof]. change (Some (Val.of_bool (Int.cmp Cle (Int.repr (lower b))
        (Int.repr (nth (range_index a) env 0)))) =
        Some (Val.of_bool (lower b <=? nth (range_index a) env 0))).
      rewrite signed_le_exact by assumption; reflexivity.
    + destruct (_ <=? _); reflexivity.
  - exists (Val.of_bool (nth (range_index a) env 0 <=? upper b)); split.
    + eapply eval_Ebinop; [exact TEMP | constructor |].
      cbn [typeof]. change (Some (Val.of_bool (Int.cmp Cle
        (Int.repr (nth (range_index a) env 0)) (Int.repr (upper b)))) =
        Some (Val.of_bool (nth (range_index a) env 0 <=? upper b))).
      rewrite signed_le_exact by assumption; reflexivity.
    + destruct (_ <=? _); reflexivity.
Qed.

Definition range_primitives layout bounds env :
  check_primitives decision_language (range_domain layout env)
    (atom_decide layout bounds env).
Proof.
  refine (@CheckPrimitives clight_entry range_atom decision_language
    (range_domain layout env) (atom_decide layout bounds env)
    (validity_expr layout bounds) (value_expr layout bounds) _ _).
  - intros a s result VIEW. cbn [decision_language]. unfold validity_expr.
    rewrite boolean_expr_test. unfold atom_decide.
    destruct (binding layout bounds a) as [[id b]|]; reflexivity.
  - intros a s result expected VIEW CHECK. cbn [decision_language].
    unfold atom_decide in CHECK.
    destruct (binding layout bounds a) as [[id b]|] eqn:BIND; try discriminate.
    inversion CHECK; subst expected. split.
    + intro RUN. eapply pure_test_determinate;
        [apply value_expr_pure | exact RUN | eapply value_expr_run; eauto].
    + intro EQ; subst result; eapply value_expr_run; eauto.
Defined.

Definition bounds_formula (bounds : list interval) : formula range_atom :=
  fold_right Conjunction (Constant true)
    (map (fun n => Conjunction (Fact (RangeAtom n true)) (Fact (RangeAtom n false)))
      (seq 0 (length bounds))).

Lemma conjunction_member {S X} (property : X -> S -> Prop) ps s p :
  formula_property property (fold_right Conjunction (Constant true) ps) s ->
  In p ps -> formula_property property p s.
Proof.
  induction ps; cbn; [tauto |]. intros [FIRST REST] [<-|IN]; eauto.
Qed.

Arguments conjunction_member {S X property ps s p} _ _.

Theorem bounds_formula_sound bounds env s :
  formula_property (range_property bounds env) (bounds_formula bounds) s ->
  env_within bounds env.
Proof.
  intros PROPERTY n b BOUND.
  assert (INDEX : (n < length bounds)%nat).
  { apply nth_error_Some. rewrite BOUND; discriminate. }
  assert (IN : In (Conjunction (Fact (RangeAtom n true)) (Fact (RangeAtom n false)))
    (map (fun n => Conjunction (Fact (RangeAtom n true)) (Fact (RangeAtom n false)))
      (seq 0 (length bounds)))).
  { apply in_map_iff. exists n; split; [reflexivity | apply in_seq; lia]. }
  pose proof (conjunction_member PROPERTY IN) as RANGE.
  cbn [formula_property] in RANGE. unfold range_property in RANGE.
  cbn [range_index lower_side] in RANGE.
  rewrite BOUND in RANGE. unfold contains; tauto.
Qed.

Definition range_guard layout bounds : decision_tree :=
  synthesize_tree (range_primitives layout bounds []) (bounds_formula bounds).

Lemma range_compile_environment layout bounds env p : forall yes no unknown,
  compile_condition (range_primitives layout bounds []) p yes no unknown =
    compile_condition (range_primitives layout bounds env) p yes no unknown.
Proof.
  induction p; intros yes no unknown; cbn [compile_condition]; try reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - apply IHp.
Qed.

Lemma range_guard_environment layout bounds env :
  range_guard layout bounds =
    synthesize_tree (range_primitives layout bounds env) (bounds_formula bounds).
Proof. unfold range_guard, synthesize_tree. apply range_compile_environment. Qed.

Theorem range_guard_sound layout bounds env s :
  typed_view layout env (entry_temps s) ->
  decision_run s (range_guard layout bounds) true -> env_within bounds env.
Proof.
  intros VIEW RUN. rewrite (range_guard_environment layout bounds env) in RUN.
  apply bounds_formula_sound with (s := s).
  eapply synthesized_tree_property with (D := range_dimension layout bounds env);
    eauto.
Qed.

Theorem guarded_affine_correct layout bounds e code b env le ge locals m :
  compile_expr layout bounds e = Some (code, b) -> typed_view layout env le ->
  decision_run (Entry ge locals le m) (range_guard layout bounds) true ->
  eval_expr ge locals le m code (Vint (Int.repr (L.eval_expr env e))).
Proof.
  intros COMPILE VIEW GUARD.
  assert (WITHIN : env_within bounds env).
  { eapply range_guard_sound with (layout := layout) (s := Entry ge locals le m);
      exact VIEW || exact GUARD. }
  destruct (compile_expr_sound e COMPILE WITHIN VIEW) as [_ [_ [_ RUN]]]; auto.
Qed.

Theorem guarded_test_correct layout bounds t tree env le ge locals m :
  lower_test layout bounds t = Some tree -> typed_view layout env le ->
  decision_run (Entry ge locals le m) (range_guard layout bounds) true ->
  decision_run (Entry ge locals le m) tree (L.eval_test env t).
Proof.
  intros LOWER VIEW GUARD. eapply lower_test_correct; eauto.
  eapply range_guard_sound with (layout := layout) (s := Entry ge locals le m);
    exact VIEW || exact GUARD.
Qed.

Theorem range_guard_total layout bounds env s :
  typed_view layout env (entry_temps s) -> exists result,
  decision_run s (range_guard layout bounds) result.
Proof.
  intro VIEW. rewrite (range_guard_environment layout bounds env).
  exists (formula_accepts (atom_decide layout bounds env) (bounds_formula bounds) s).
  apply synthesized_tree_correct; auto.
Qed.

Example missing_parameter_under_negation env s :
  formula_execute (atom_decide [] [Interval 0 10] env)
    (Complement (Fact (RangeAtom 0 true))) s = None.
Proof. reflexivity. Qed.

Example malformed_interval_under_negation env s :
  formula_execute (atom_decide [1%positive] [Interval 10 0] env)
    (Complement (Fact (RangeAtom 0 true))) s = None.
Proof. vm_compute; reflexivity. Qed.

End PolCertAffineGuardFor.

Module PolCertAffineGuard (I : INSTR).
Module ConcreteLoop := Loop I.
Include PolCertAffineGuardFor I ConcreteLoop.

Print Assumptions range_guard_sound.
Print Assumptions guarded_affine_correct.
Print Assumptions guarded_test_correct.
Print Assumptions range_guard_total.

End PolCertAffineGuard.
