From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightCondition ClightPureExpr ClightRectangularStore ClightNoWrap ClightTempFootprint.
From GuardInterface Require Import AffineBoxEnvelope ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A concrete language encoding. Intermediate operations have CompCert's
    modular integer semantics. The certified final range justifies using
    signed comparisons on the generated affine values. *)
Fixpoint affine_linear_code registers coefficients :=
  match registers,coefficients with
  | identifier::rest,coefficient::tail =>
      Ebinop Oadd
        (Ebinop Omul (Etempvar identifier type_int32s) (Econst_int (Int.repr coefficient) type_int32s) type_int32s)
        (affine_linear_code rest tail) type_int32s
  | _,_ => Econst_int Int.zero type_int32s
  end.
Definition affine_form_code registers (form : affine_form) :=
  Ebinop Oadd (affine_linear_code registers (fst form)) (Econst_int (Int.repr (snd form)) type_int32s) type_int32s.
Definition affine_registers_view registers values temps :=
  Forall2 (fun identifier value => temps ! identifier = Some (Vint (Int.repr value))) registers values.

Lemma affine_linear_code_type registers coefficients : typeof (affine_linear_code registers coefficients) = type_int32s.
Proof. destruct registers,coefficients; reflexivity. Qed.
Lemma affine_linear_code_pure registers coefficients : pure_scalar (affine_linear_code registers coefficients).
Proof.
  revert coefficients; induction registers; intros [|coefficient tail]; cbn [affine_linear_code];
    repeat constructor; apply IHregisters.
Qed.
Lemma affine_form_code_pure registers form : pure_scalar (affine_form_code registers form).
Proof. constructor; [apply affine_linear_code_pure|constructor]. Qed.

Theorem affine_linear_code_evaluation ge locals temps memory registers values coefficients :
  affine_registers_view registers values temps ->
  eval_expr ge locals temps memory (affine_linear_code registers coefficients)
    (Vint (Int.repr (affine_dot coefficients values))).
Proof.
  intro WORDS; revert coefficients; induction WORDS; intros [|coefficient coefficients];
    cbn [affine_linear_code affine_dot]; try solve [constructor].
  eapply eval_Ebinop with (v1 := Vint (Int.repr (coefficient*y)))
    (v2 := Vint (Int.repr (affine_dot coefficients l'))).
  - eapply eval_Ebinop with (v1 := Vint (Int.repr y)) (v2 := Vint (Int.repr coefficient)).
    + constructor; exact H.
    + constructor.
    + change (Some (Vint (Int.mul (Int.repr y) (Int.repr coefficient))) =
        Some (Vint (Int.repr (coefficient*y)))).
      rewrite rect_integer_multiply, Z.mul_comm; reflexivity.
  - apply IHWORDS.
  - rewrite affine_linear_code_type.
    change (Some (Vint (Int.add (Int.repr (coefficient*y)) (Int.repr (affine_dot coefficients l')))) =
      Some (Vint (Int.repr (coefficient*y + affine_dot coefficients l')))).
    rewrite rect_integer_add; reflexivity.
Qed.

Theorem affine_form_code_evaluation ge locals temps memory registers values form :
  affine_registers_view registers values temps ->
  eval_expr ge locals temps memory (affine_form_code registers form) (Vint (Int.repr (affine_value form values))).
Proof.
  intro WORDS; unfold affine_form_code,affine_value.
  eapply eval_Ebinop; [apply affine_linear_code_evaluation; exact WORDS|constructor|].
  rewrite affine_linear_code_type.
  change (Some (Vint (Int.add (Int.repr (affine_dot (fst form) values)) (Int.repr (snd form)))) =
    Some (Vint (Int.repr (affine_dot (fst form) values + snd form)))).
  rewrite rect_integer_add; reflexivity.
Qed.

Definition compile_affine_comparison registers limits first second : option expr :=
  if Nat.eqb (length registers) (length limits) &&
    affine_form_range_check Int.min_signed Int.max_signed limits first &&
    affine_form_range_check Int.min_signed Int.max_signed limits second
  then Some (Ebinop Olt (affine_form_code registers first) (affine_form_code registers second) type_int32s)
  else None.

Theorem compiled_affine_comparison_exact ge locals temps memory registers limits values first second code accepted :
  compile_affine_comparison registers limits first second = Some code ->
  affine_registers_view registers values temps ->
  Forall2 (fun value limit => 0 <= value < limit) values limits ->
  (expression_test code (Entry ge locals temps memory) accepted <->
    accepted = (affine_value first values <? affine_value second values)).
Proof.
  unfold compile_affine_comparison.
  destruct (_ && _ && _) eqn:VALID; [|discriminate].
  intros COMPILE WORDS RANGES; injection COMPILE as <-.
  rewrite !andb_true_iff in VALID; destruct VALID as [[ARITY FIRST] SECOND].
  pose proof (@checked_affine_form_range Int.min_signed Int.max_signed limits first values FIRST RANGES) as FIRST_RANGE.
  pose proof (@checked_affine_form_range Int.min_signed Int.max_signed limits second values SECOND RANGES) as SECOND_RANGE.
  set (answer := affine_value first values <? affine_value second values).
  assert (CMP : Int.lt (Int.repr (affine_value first values)) (Int.repr (affine_value second values)) = answer).
  { unfold Int.lt; rewrite !Int.signed_repr by assumption; unfold answer.
    destruct (zlt (affine_value first values) (affine_value second values));
      [symmetry; apply Z.ltb_lt|symmetry; apply Z.ltb_ge]; lia. }
  assert (EVAL : eval_expr ge locals temps memory
    (Ebinop Olt (affine_form_code registers first) (affine_form_code registers second) type_int32s) (Val.of_bool answer)).
  { eapply eval_Ebinop; [apply affine_form_code_evaluation; exact WORDS|apply affine_form_code_evaluation; exact WORDS|].
    change (Some (Val.of_bool (Int.lt (Int.repr (affine_value first values))
      (Int.repr (affine_value second values)))) = Some (Val.of_bool answer)).
    rewrite CMP; reflexivity. }
  split.
  - intros [value [RUN BOOL]].
    pose proof ((proj1 (expressions_determinate ge locals temps memory)) _ _ EVAL _ RUN) as SAME.
    subst value; change (bool_val (Val.of_bool answer) type_int32s memory = Some accepted) in BOOL.
    rewrite bool_of_bool in BOOL; congruence.
  - intro SAME; subst accepted; exists (Val.of_bool answer); split; [exact EVAL|apply bool_of_bool].
Qed.

Print Assumptions affine_form_code_evaluation.
Print Assumptions compiled_affine_comparison_exact.

Definition compile_affine_interval_comparison registers ranges first second : option expr :=
  if Nat.eqb (length registers) (length ranges) &&
    affine_interval_range_check Int.min_signed Int.max_signed ranges first &&
    affine_interval_range_check Int.min_signed Int.max_signed ranges second
  then Some (Ebinop Olt (affine_form_code registers first) (affine_form_code registers second) type_int32s)
  else None.

Theorem compiled_affine_interval_comparison_exact ge locals temps memory registers ranges values first second code accepted :
  compile_affine_interval_comparison registers ranges first second = Some code ->
  affine_registers_view registers values temps ->
  Forall2 (fun value range => fst range <= value <= snd range) values ranges ->
  (expression_test code (Entry ge locals temps memory) accepted <->
    accepted = (affine_value first values <? affine_value second values)).
Proof.
  unfold compile_affine_interval_comparison.
  destruct (_ && _ && _) eqn:VALID; [|discriminate].
  intros COMPILE WORDS RANGES; injection COMPILE as <-.
  rewrite !andb_true_iff in VALID; destruct VALID as [[ARITY FIRST] SECOND].
  pose proof (@checked_affine_interval_range Int.min_signed Int.max_signed ranges first values FIRST RANGES) as FIRST_RANGE.
  pose proof (@checked_affine_interval_range Int.min_signed Int.max_signed ranges second values SECOND RANGES) as SECOND_RANGE.
  set (answer := affine_value first values <? affine_value second values).
  assert (CMP : Int.lt (Int.repr (affine_value first values)) (Int.repr (affine_value second values)) = answer).
  { unfold Int.lt; rewrite !Int.signed_repr by assumption; unfold answer.
    destruct (zlt (affine_value first values) (affine_value second values));
      [symmetry; apply Z.ltb_lt|symmetry; apply Z.ltb_ge]; lia. }
  assert (EVAL : eval_expr ge locals temps memory
    (Ebinop Olt (affine_form_code registers first) (affine_form_code registers second) type_int32s) (Val.of_bool answer)).
  { eapply eval_Ebinop; [apply affine_form_code_evaluation; exact WORDS|apply affine_form_code_evaluation; exact WORDS|].
    change (Some (Val.of_bool (Int.lt (Int.repr (affine_value first values))
      (Int.repr (affine_value second values)))) = Some (Val.of_bool answer)).
    rewrite CMP; reflexivity. }
  split.
  - intros [value [RUN BOOL]].
    pose proof ((proj1 (expressions_determinate ge locals temps memory)) _ _ EVAL _ RUN) as SAME.
    subst value; change (bool_val (Val.of_bool answer) type_int32s memory = Some accepted) in BOOL.
    rewrite bool_of_bool in BOOL; congruence.
  - intro SAME; subst accepted; exists (Val.of_bool answer); split; [exact EVAL|apply bool_of_bool].
Qed.
Lemma compiled_affine_interval_comparison_pure registers ranges first second code :
  compile_affine_interval_comparison registers ranges first second = Some code -> pure_scalar code.
Proof.
  unfold compile_affine_interval_comparison; destruct (_ && _ && _); [|discriminate].
  intro SAME; injection SAME as <-; constructor; apply affine_form_code_pure.
Qed.
Print Assumptions compiled_affine_interval_comparison_exact.
