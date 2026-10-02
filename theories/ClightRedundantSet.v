From Stdlib Require Import Bool ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts ClightGuard ClightNoWrap
  ClightCondition ClightPureExpr ClightDecisionRule ClightRegionRewrite ClightRegionRule
  ClightStraightLine.
Import ListNotations.
Set Implicit Arguments.

(** A conditional region rewrite: keep the computation that reads [x], then
    omit [x = c] if the entry value of [x] already equals [c]. *)
Definition redundant_set_source result x c :=
  Ssequence (Sset result (wrap_test x)) (Sset x (Econst_int c type_int32u)).
Definition redundant_set_candidate result x := Sset result (wrap_test x).
Definition register_domain x (s : clight_entry) :=
  exists n, (entry_temps s) ! x = Some (Vint n).
Definition register_equals x c (_ : unit) (s : clight_entry) :=
  (entry_temps s) ! x = Some (Vint c).
Definition register_flag x c s := Int.eq (temp_word x (entry_temps s)) c.
Definition register_guard x c :=
  Ebinop Oeq (Etempvar x type_int32u) (Econst_int c type_int32u) type_int32s.
Definition register_tree x c := Test (register_guard x c) (Decision true) (Decision false).

Definition register_dimension x (c : Int.int) : property_dimension clight_entry unit (register_domain x).
Proof.
  refine (@positive_dimension clight_entry unit (register_domain x)
    (register_equals x c) (fun _ s => register_flag x c s) _).
  intros [] s [n LOOKUP] ACCEPT.
  unfold register_flag, temp_word in ACCEPT; rewrite LOOKUP in ACCEPT.
  apply Int.same_if_eq in ACCEPT; subst n; exact LOOKUP.
Defined.

Lemma register_tree_pure x c : pure_tree (register_tree x c).
Proof. repeat constructor. Qed.

Lemma register_tree_run x c s : register_domain x s ->
  decision_run s (register_tree x c) (register_flag x c s).
Proof.
  intros [n LOOKUP]. unfold register_tree. eapply run_test.
  - exists (Val.of_bool (Int.eq n c)); split.
    + eapply eval_Ebinop; [constructor; exact LOOKUP | constructor | reflexivity].
    + apply bool_of_bool.
  - unfold register_flag, temp_word; rewrite LOOKUP.
    destruct (Int.eq n c); constructor.
Qed.

Definition register_primitives x c :
  check_primitives decision_test_language (register_domain x)
    (decide_atom (register_dimension x c)).
Proof.
  refine (@CheckPrimitives clight_entry unit decision_test_language (register_domain x)
    (decide_atom (register_dimension x c)) (fun _ => register_tree x c)
    (fun _ => Decision true) _ _).
  - intros [] s b INV. cbn [decision_test_language].
    assert (RUN := register_tree_run c INV).
    assert (EXACT : decision_run s (register_tree x c) b <-> b = register_flag x c s).
    { split; [intro OTHER; eapply pure_tree_determinate; eauto using register_tree_pure |].
      intro EQ; subst; exact RUN. }
    rewrite EXACT. unfold register_dimension; cbn [positive_dimension decide_atom].
    destruct (register_flag x c s); reflexivity.
  - intros [] s b expected INV CHECK. cbn [decision_test_language].
    unfold register_dimension in CHECK; cbn [positive_dimension decide_atom] in CHECK.
    destruct (register_flag x c s); try discriminate.
    injection CHECK as CHECK; subst expected. split;
      [intro RUN; inversion RUN; reflexivity | intro EQ; subst; constructor].
Defined.

Lemma redundant_set_source_inv fe ge e le m result x c le' m' :
  exec_stmt fe ge e le m (redundant_set_source result x c) E0 le' m' Out_normal ->
  exists v, eval_expr ge e le m (wrap_test x) v /\ m' = m /\
    le' = PTree.set x (Vint c) (PTree.set result v le).
Proof.
  intro SOURCE; inversion SOURCE; subst.
  - match goal with FIRST : exec_stmt _ _ _ _ _ (Sset result _) _ _ _ _ |- _ =>
      inversion FIRST; subst end.
    match goal with SECOND : exec_stmt _ _ _ _ _ (Sset x _) _ _ _ _ |- _ =>
      inversion SECOND; subst end.
    match goal with CONST : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
      apply eval_const_inv in CONST; subst end.
    eexists; repeat split; eauto.
  - contradiction.
Qed.

Definition redundant_set_rule result x c (DISTINCT : result <> x) :
  encoded_region_rule (redundant_set_source result x c) (redundant_set_candidate result x).
Proof.
  refine {| region_rule_atoms := unit; region_rule_domain := register_domain x;
    region_rule_dimension := register_dimension x c; region_rule_primitives := register_primitives x c;
    region_rule_formula := Fact tt |}.
  - intros temps p e le m le' m' SOURCE.
    apply redundant_set_source_inv in SOURCE as [v [EV _]].
    apply wrap_test_eval_inv in EV as [n [LOOKUP VALUE]]. exists n; exact LOOKUP.
  - intros temps p e le m le' m' SOURCE SAME.
    apply redundant_set_source_inv in SOURCE as [v [EV [MEM TEMPS]]]. subst m' le'.
    change (le ! x = Some (Vint c)) in SAME.
    assert (LOOKUP : (PTree.set result v le) ! x = Some (Vint c)).
    { rewrite PTree.gso by (intro EQ; apply DISTINCT; symmetry; exact EQ); exact SAME. }
    rewrite (PTree.gsident x (PTree.set result v le) LOOKUP).
    constructor; exact EV.
Defined.

Definition redundant_set_region result x c (DISTINCT : result <> x) :=
  generated_region (redundant_set_rule c DISTINCT).

Definition redundant_set_region_for source result x c (DISTINCT : result <> x) :=
  tree_statement (generated_region_tree (redundant_set_rule c DISTINCT))
    (redundant_set_candidate result x) source.

Lemma redundant_set_flat_sound source result x c (DISTINCT : result <> x) :
  flatten_region source = [Sset result (wrap_test x); Sset x (Econst_int c type_int32u)] ->
  region_contract source (redundant_set_region_for source c DISTINCT).
Proof.
  intro FLAT. apply guarded_fragment_region_contract.
  intros temps p e le m le' m' SOURCE.
  eapply (encoded_region_rule_guarded (redundant_set_rule c DISTINCT)).
  eapply flattened_pair_execution; eauto.
Qed.

Definition select_redundant_set (s : statement) : option statement :=
  match flatten_region s with
  | [Sset result
      (Ebinop Olt
        (Ebinop Oadd (Etempvar x (Tint I32 Unsigned a1))
          (Econst_int one (Tint I32 Unsigned a2)) (Tint I32 Unsigned a3))
        (Etempvar x' (Tint I32 Unsigned a4)) (Tint I32 Signed a5));
      Sset x'' (Econst_int c (Tint I32 Unsigned a6))] =>
      if attr_eq a1 noattr then if attr_eq a2 noattr then if attr_eq a3 noattr then
      if attr_eq a4 noattr then if attr_eq a5 noattr then if attr_eq a6 noattr then
      if ident_eq x x' then if ident_eq x x'' then
      if Int.eq one Int.one then
        match ident_eq result x with
        | left _ => None
        | right DISTINCT => Some (redundant_set_region_for s c DISTINCT)
        end
      else None else None else None else None else None else None else None else None else None
  | _ => None
  end.

Theorem select_redundant_set_sound s target :
  select_redundant_set s = Some target -> region_contract s target.
Proof.
  unfold select_redundant_set.
  repeat match goal with
  | |- context [match ?x with _ => _ end] =>
      let E := fresh "CASE" in destruct x eqn:E; try discriminate
  | |- context [if ?x then _ else _] => destruct x; try discriminate
  end.
  all: intros SEL; inversion SEL; subst;
    repeat match goal with H : Int.eq _ _ = true |- _ => apply Int.same_if_eq in H; subst end;
    apply redundant_set_flat_sound; assumption.
Qed.

Example selected_redundant_set :
  exists code, select_redundant_set (redundant_set_source 1%positive 2%positive (Int.repr 7)) = Some code.
Proof. eexists; vm_compute; reflexivity. Qed.
Example refuse_overlapping_temporaries :
  select_redundant_set (redundant_set_source 1%positive 1%positive (Int.repr 7)) = None.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions select_redundant_set_sound.
