From Stdlib Require Import Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightPureExpr
  ClightWideGuard ClightDecisionRule ClightTreeRule ClightTreeRewrite ClightNoWrap ClightSignedCancel ClightSameAddress ClightSyntaxEquality.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition variable_cancel_source x y :=
  Ebinop Odiv(Ebinop Omul(signed_temp x)(signed_temp y)type_int32s)(signed_temp y)type_int32s.
Lemma variable_cancel_value nx ny :
  Int.signed ny<>0 -> word_range(Int.signed nx*Int.signed ny) ->
  Int.divs(Int.mul nx ny) ny=nx.
Proof.
  intros NONZERO RANGE; unfold Int.divs; rewrite Int.mul_signed.
  rewrite Int.signed_repr by exact RANGE.
  rewrite Z.quot_mul by exact NONZERO; apply Int.repr_signed.
Qed.

Inductive variable_cancel_atom := VariableNonzero | VariableProductRange.
Definition variable_cancel_domain x y (state:clight_entry) :=
  exists nx ny, (entry_temps state)!x=Some(Vint nx) /\ (entry_temps state)!y=Some(Vint ny).
Definition variable_cancel_property x y atom(state:clight_entry) :=
  exists nx ny, (entry_temps state)!x=Some(Vint nx) /\ (entry_temps state)!y=Some(Vint ny) /\
    match atom with VariableNonzero=>Int.eq ny Int.zero=false
    | VariableProductRange=>word_range(Int.signed nx*Int.signed ny) end.
Definition variable_cancel_decide x y atom(state:clight_entry) : option bool :=
  match(entry_temps state)!x,(entry_temps state)!y with
  | Some(Vint nx),Some(Vint ny)=>Some(match atom with
      VariableNonzero=>negb(Int.eq ny Int.zero)
    | VariableProductRange=>word_range_bool(Int.signed nx*Int.signed ny) end)
  | _,_=>None end.
Definition variable_cancel_nonzero_test y :=
  Ebinop One(signed_temp y)(Econst_int Int.zero type_int32s)type_int32s.
Definition variable_cancel_atom_tree x y atom := match atom with
  | VariableNonzero=>Test(variable_cancel_nonzero_test y)(Decision true)(Decision false)
  | VariableProductRange=>wide_bounds_tree(wide_mul(signed_temp x)(signed_temp y)) end.

Lemma variable_cancel_nonzero_run y ge locals temps memory ny : temps!y=Some(Vint ny) ->
  expression_test(variable_cancel_nonzero_test y)(Entry ge locals temps memory)(negb(Int.eq ny Int.zero)).
Proof.
  intro LOOKUP; exists(Val.of_bool(negb(Int.eq ny Int.zero))); split.
  - eapply eval_Ebinop; [constructor; exact LOOKUP|constructor|reflexivity].
  - destruct(Int.eq ny Int.zero); reflexivity.
Qed.

Lemma variable_cancel_atom_pure x y atom : pure_tree(variable_cancel_atom_tree x y atom).
Proof. destruct atom; cbn [variable_cancel_atom_tree]; [repeat constructor|apply wide_bounds_pure; repeat constructor]. Qed.
Lemma variable_cancel_atom_run x y atom ge locals temps memory nx ny :
  temps!x=Some(Vint nx) -> temps!y=Some(Vint ny) ->
  decision_run(Entry ge locals temps memory)(variable_cancel_atom_tree x y atom)
    (match atom with VariableNonzero=>negb(Int.eq ny Int.zero)
      | VariableProductRange=>word_range_bool(Int.signed nx*Int.signed ny) end).
Proof.
  intros X Y; destruct atom; cbn [variable_cancel_atom_tree].
  - eapply run_test with(b:=negb(Int.eq ny Int.zero)).
    + apply variable_cancel_nonzero_run; exact Y.
    + destruct(Int.eq ny Int.zero); constructor.
  - eapply wide_bounds_run.
    + reflexivity.
    + apply word_product_is_long; apply Int.signed_range.
    + eapply wide_mul_eval; try reflexivity; try apply Int.signed_range;
        rewrite Int.repr_signed; constructor; assumption.
Qed.

Definition variable_cancel_dimension x y :
  property_dimension clight_entry variable_cancel_atom(variable_cancel_domain x y).
Proof.
  refine {| atom_property:=variable_cancel_property x y; decide_atom:=variable_cancel_decide x y |}.
  intros atom state result [nx [ny [X Y]]] CHECK.
  unfold variable_cancel_decide in CHECK; rewrite X,Y in CHECK; inversion CHECK; subst result.
  destruct atom; cbn [decision_evidence].
  - destruct(Int.eq ny Int.zero) eqn:ZERO; cbn [negb decision_evidence].
    + intros [nx' [ny' [X' [Y' NONZERO]]]]; assert(ny'=ny) by congruence; subst ny'; congruence.
    + exists nx,ny; auto.
  - destruct(word_range_bool(Int.signed nx*Int.signed ny)) eqn:RANGE; cbn [decision_evidence].
    + exists nx,ny; repeat split; try assumption; apply word_range_bool_spec; exact RANGE.
    + intros [nx' [ny' [X' [Y' SAFE]]]]; assert(nx'=nx /\ ny'=ny) by (split; congruence).
      destruct H; subst; apply word_range_bool_spec in SAFE; congruence.
Defined.
Print Assumptions variable_cancel_value.

Lemma variable_cancel_source_inv ge locals le memory x y value :
  eval_expr ge locals le memory(variable_cancel_source x y) value ->
  exists nx ny, le!x=Some(Vint nx) /\ le!y=Some(Vint ny) /\
    value=Vint(Int.divs(Int.mul nx ny) ny).
Proof.
  intro SOURCE; apply scalar_binary_inv in SOURCE as [product [divisor [MULTIPLY [DIVISOR DIVIDE]]]].
  apply scalar_binary_inv in MULTIPLY as [first [second [FIRST [SECOND MULTIPLY]]]].
  apply scalar_temp_inv in FIRST,SECOND,DIVISOR.
  assert(divisor=second) by congruence; subst divisor.
  destruct first; destruct second; try discriminate MULTIPLY.
  change(Some(Vint(Int.mul i i0))=Some product) in MULTIPLY.
  inversion MULTIPLY; subst product.
  change((if Int.eq i0 Int.zero || Int.eq(Int.mul i i0)(Int.repr Int.min_signed) && Int.eq i0 Int.mone
    then None else Some(Vint(Int.divs(Int.mul i i0) i0)))=Some value) in DIVIDE.
  destruct(Int.eq i0 Int.zero || Int.eq(Int.mul i i0)(Int.repr Int.min_signed) && Int.eq i0 Int.mone);
    [discriminate|].
  inversion DIVIDE; subst value; eauto.
Qed.

Definition variable_cancel_primitives x y :
  check_primitives decision_test_language(variable_cancel_domain x y)
    (decide_atom(variable_cancel_dimension x y)).
Proof.
  refine(@CheckPrimitives clight_entry variable_cancel_atom decision_test_language
    (variable_cancel_domain x y)(decide_atom(variable_cancel_dimension x y))
    (fun _=>Decision true)(variable_cancel_atom_tree x y) _ _).
  - intros atom state result [nx [ny [X Y]]].
    cbn [decision_test_language]; unfold variable_cancel_dimension; cbn [decide_atom].
    unfold variable_cancel_decide; rewrite X,Y; cbn [checked_valid].
    split; intro RUN; [inversion RUN; reflexivity|subst; constructor].
  - intros atom state result expected [nx [ny [X Y]]] CHECK.
    cbn [decision_test_language].
    change(variable_cancel_decide x y atom state=Some expected) in CHECK.
    unfold variable_cancel_decide in CHECK; rewrite X,Y in CHECK; inversion CHECK; subst expected.
    destruct state as [ge locals temps memory]; cbn in X,Y.
    split.
    + intro RUN; eapply pure_tree_determinate;
        [apply variable_cancel_atom_pure|exact RUN|apply variable_cancel_atom_run; assumption].
    + intro SAME; subst result; apply variable_cancel_atom_run; assumption.
Defined.

Definition variable_cancel_rule x y : encoded_decision_rule(variable_cancel_source x y)(signed_temp x).
Proof.
  refine {| decision_rule_atoms:=variable_cancel_atom;
    decision_rule_domain:=variable_cancel_domain x y;
    decision_rule_dimension:=variable_cancel_dimension x y;
    decision_rule_primitives:=variable_cancel_primitives x y;
    decision_rule_formula:=Conjunction(Fact VariableNonzero)(Fact VariableProductRange) |}.
  - reflexivity.
  - intros [ge locals temps memory] [value SOURCE]; cbn in *.
    apply variable_cancel_source_inv in SOURCE as [nx [ny [X [Y VALUE]]]].
    exists nx,ny; auto.
  - intros [ge locals temps memory] value SOURCE PROPERTY.
    apply variable_cancel_source_inv in SOURCE as [nx [ny [X [Y VALUE]]]].
    change(variable_cancel_property x y VariableNonzero(Entry ge locals temps memory) /\
           variable_cancel_property x y VariableProductRange(Entry ge locals temps memory)) in PROPERTY.
    destruct PROPERTY as [[nx1 [ny1 [X1 [Y1 NONZERO]]]] [nx2 [ny2 [X2 [Y2 RANGE]]]]].
    cbn in X,Y,X1,Y1,X2,Y2; assert(nx1=nx /\ ny1=ny /\ nx2=nx /\ ny2=ny) by (repeat split; congruence).
    destruct H as [-> [-> [-> ->]]].
    assert(SIGNED: Int.signed ny<>0).
    { intro ZERO; assert(ny=Int.zero).
      { rewrite <-(Int.repr_signed ny),ZERO; reflexivity. }
      subst ny; rewrite Int.eq_true in NONZERO; discriminate. }
    subst value; rewrite variable_cancel_value by assumption; constructor; exact X.
Defined.
Definition variable_cancel_tree x y := generated_decision_tree(variable_cancel_rule x y).
Print Assumptions variable_cancel_rule.

Definition select_variable_cancel source : option(decision_tree*expr) := match source with
  | Ebinop Odiv(Ebinop Omul(Etempvar x _)(Etempvar y _)_) _ _=>
      if expression_eq source(variable_cancel_source x y)
      then Some(variable_cancel_tree x y,signed_temp x) else None
  | _=>None end.
Theorem select_variable_cancel_sound source guard candidate :
  select_variable_cancel source=Some(guard,candidate) -> expression_contract source guard candidate.
Proof.
  unfold select_variable_cancel; intro SELECT.
  repeat match type of SELECT with
  | context[match ?term with _=>_ end]=>destruct term; cbn beta iota zeta in SELECT; try discriminate
  end.
  inversion SELECT; subst guard candidate.
  match goal with SAME:_=variable_cancel_source _ _ |- _=>rewrite SAME end.
  apply encoded_decision_rule_sound.
Qed.
Definition select_all_guardcert_root source :=
  match select_variable_cancel source with Some result=>Some result|None=>select_signed_memory_root source end.
Definition select_all_guardcert_rewrites := select_tree_deep select_all_guardcert_root.
Theorem select_all_guardcert_rewrites_sound source guard candidate :
  select_all_guardcert_rewrites source=Some(guard,candidate) -> expression_contract source guard candidate.
Proof.
  apply select_tree_deep_sound; intros source0 guard0 candidate0.
  unfold select_all_guardcert_root; destruct(select_variable_cancel source0) as [[g c]|] eqn:SELECT; intro RESULT.
  - inversion RESULT; subst; eapply select_variable_cancel_sound; exact SELECT.
  - eapply select_signed_memory_root_sound; exact RESULT.
Qed.
Print Assumptions select_all_guardcert_rewrites_sound.
