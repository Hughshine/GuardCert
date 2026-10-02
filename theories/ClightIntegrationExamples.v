From Stdlib Require Import ZArith List.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Events Memory Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightGuard ClightGuardProof ClightEncodedRule ClightNoWrap GuardCompiler.
Import ListNotations.
Open Scope Z_scope.

Definition input_id : ident := 1%positive.
Definition yes_branch := Sreturn (Some (Econst_int (Int.repr 11) type_int32s)).
Definition no_branch := Sreturn (Some (Econst_int (Int.repr 22) type_int32s)).
Definition source_branch := Sifthenelse (wrap_test input_id) yes_branch no_branch.
Definition guarded_branch :=
  Sifthenelse (no_wrap_guard input_id) no_branch source_branch.

Example real_clight_rewrite :
  transform_statement select_no_wrap source_branch = guarded_branch.
Proof. reflexivity. Qed.

Example labels_block_versioning :
  let original := Sifthenelse (wrap_test input_id)
    (Slabel 9%positive yes_branch) no_branch in
  transform_statement select_no_wrap original = original.
Proof. reflexivity. Qed.

Definition frame : function :=
  mkfunction type_int32s cc_default [] [] [(input_id, type_int32u)] source_branch.
Definition temp_with (x : Int.int) : temp_env :=
  PTree.set input_id (Vint x) (PTree.empty val).

Lemma wrap_test_evaluates : forall ge e le m id x,
  le!id = Some (Vint x) ->
  eval_expr ge e le m (wrap_test id) (Val.of_bool (Int.ltu (Int.add x Int.one) x)).
Proof.
  intros. unfold wrap_test. eapply eval_Ebinop.
  - eapply eval_Ebinop; [apply eval_Etempvar; eauto|constructor|reflexivity].
  - apply eval_Etempvar; eauto.
  - reflexivity.
Qed.

(** These are actual Clight transitions, for arbitrary global environments,
    memories and surrounding continuations, rather than a second interpreter. *)
Example safe_input_takes_fast_path : forall ge k m,
  adapter_step true ge
    (State frame guarded_branch k empty_env (temp_with (Int.repr 254)) m) E0
    (State frame no_branch k empty_env (temp_with (Int.repr 254)) m).
Proof.
  intros. unfold guarded_branch. eapply step_ifthenelse with
    (v1 := Val.of_bool (no_wrap_flag (Int.repr 254))) (b := true).
  - apply no_wrap_guard_evaluates. apply PTree.gss.
  - reflexivity.
Qed.

Example wrapping_input_takes_fallback : forall ge k m,
  plus (adapter_step true) ge
    (State frame guarded_branch k empty_env (temp_with Int.mone) m) E0
    (State frame yes_branch k empty_env (temp_with Int.mone) m).
Proof.
  intros. eapply plus_two.
  - eapply step_ifthenelse with (v1 := Val.of_bool (no_wrap_flag Int.mone)) (b := false).
    + apply no_wrap_guard_evaluates. apply PTree.gss.
    + reflexivity.
  - eapply step_ifthenelse with
      (v1 := Val.of_bool (Int.ltu (Int.add Int.mone Int.one) Int.mone)) (b := true).
    + apply wrap_test_evaluates. apply PTree.gss.
    + reflexivity.
  - reflexivity.
Qed.

Example safe_input_before_boundary_takes_fast_path :
  no_wrap_flag (Int.repr 4294967294) = true.
Proof. reflexivity. Qed.

(** A contradictory presumption lowers to false, so the candidate is never
    selected, even for a source condition whose then-branch is reachable. *)
Definition select_impossible (_ : expr) : option expr :=
  Some (Econst_int Int.zero type_int32s).

Example impossible_presumption_condition : forall x,
  Synthesis.execute Int.modulus (word_view x) (Synthesis.synthesize Presumption.Falsity) =
    Some false.
Proof. reflexivity. Qed.

Definition falsity_encoding : @Synthesis.presumption_encoding temp_env Int.modulus
  (fun _ => word_view Int.zero) (fun _ => False).
Proof.
  refine {| Synthesis.encoded_presumption := Presumption.Falsity |}.
  intro le; unfold Presumption.holds; simpl. split; [discriminate|contradiction].
Defined.

Definition truth_encoding : @Synthesis.presumption_encoding temp_env Int.modulus
  (fun _ => word_view Int.zero) (fun _ => True).
Proof.
  refine {| Synthesis.encoded_presumption := Presumption.Truth |}.
  intro le; unfold Presumption.holds; simpl; split; auto.
Defined.

Lemma impossible_contract : forall a,
  guard_contract a (Econst_int Int.zero type_int32s).
Proof.
  intro a; apply encoded_branch_rule_sound.
  refine {| rule_modulus := Int.modulus; rule_view := fun _ => word_view Int.zero;
    rule_obligation := fun _ => False;
    rule_encoding := falsity_encoding |}.
  - intros ge e le m v b EVAL BOOL. exists (Vint Int.zero), false.
    split; [constructor|]. split; reflexivity.
  - intros; contradiction.
Qed.

Example impossible_compiler_correct : forall p tp,
  compile_with_guards select_impossible p = Errors.OK tp ->
  backward_simulation (Csem.semantics p) (Asm.semantics tp).
Proof.
  apply compile_with_guards_correct. intros a g H; inversion H; subst.
  apply impossible_contract.
Qed.

Definition select_dead_literal (a : expr) : option expr :=
  match a with
  | Econst_int n (Tint I32 Signed {| attr_volatile := false; attr_alignas := None |}) =>
      if Int.eq n Int.zero then Some (Econst_int Int.one type_int32s) else None
  | _ => None
  end.

Example dead_literal_presumption_condition : forall x,
  Synthesis.execute Int.modulus (word_view x) (Synthesis.synthesize Presumption.Truth) =
    Some true.
Proof. reflexivity. Qed.

Lemma dead_literal_contract :
  guard_contract (Econst_int Int.zero type_int32s) (Econst_int Int.one type_int32s).
Proof.
  apply encoded_branch_rule_sound.
  refine {| rule_modulus := Int.modulus; rule_view := fun _ => word_view Int.zero;
    rule_obligation := fun _ => True;
    rule_encoding := truth_encoding |}.
  - intros ge e le m v b EVAL BOOL. exists (Vint Int.one), true.
    split; [constructor|]. split; reflexivity.
  - intros ge e le m v b EVAL BOOL Q. apply eval_const_inv in EVAL; subst v.
    change (Some false = Some b) in BOOL. congruence.
Qed.

Lemma select_dead_literal_sound : forall a g,
  select_dead_literal a = Some g -> guard_contract a g.
Proof.
  intros a g H; unfold select_dead_literal in H.
  repeat match type of H with
  | context [if ?x then _ else _] =>
      destruct x eqn:?; cbn beta iota zeta in H; try discriminate
  | context [match ?x with _ => _ end] =>
      destruct x; cbn beta iota zeta in H; try discriminate
  end.
  match goal with H : Int.eq _ _ = true |- _ => apply Int.same_if_eq in H; subst end.
  inversion H; subst. apply dead_literal_contract.
Qed.

Example dead_literal_compiler_correct : forall p tp,
  compile_with_guards select_dead_literal p = Errors.OK tp ->
  backward_simulation (Csem.semantics p) (Asm.semantics tp).
Proof. apply compile_with_guards_correct. apply select_dead_literal_sound. Qed.

Print Assumptions impossible_compiler_correct.
Print Assumptions dead_literal_compiler_correct.
