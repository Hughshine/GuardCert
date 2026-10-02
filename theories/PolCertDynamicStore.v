From Stdlib Require Import Bool List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events Smallstep Errors.
From compcert.cfrontend Require Import Ctypes Cop Csem Clight ClightBigstep.
From polcert.src Require Import CInstr.
From Guard Require Import AbstractGuard SemanticFacts CompCertMemoryEquivalence
  ClightGuard ClightCondition ClightPureExpr ClightIndexGuard ClightRegionRule
  ClightRegionRewrite ClightRegionRewriteProof ClightSyntaxEquality ClightStraightLine
  ClightNoWrap ClightSignedCancel RegionCompiler PolCertStoreSwap.
Import ListNotations.
Open Scope Z_scope.
Set Implicit Arguments.

Module PolCertDynamicStore (Names : C_INSTR_NAMES).
Module Stores := PolCertStoreSwap Names.
Module B := Stores.B.

Definition variable_store id count index value :=
  Sassign (B.A.array_lvalue id count (index_temp index)) (Econst_int value type_int32s).
Definition variable_pair id count first second left right :=
  Ssequence (variable_store id count first left) (variable_store id count second right).

Lemma variable_store_domain fe ge e le m id count index value trace le' m' outcome :
  exec_stmt fe ge e le m (variable_store id count index value) trace le' m' outcome ->
  exists n, le ! index = Some (Vint n) /\ trace = E0 /\ le' = le /\ outcome = Out_normal.
Proof.
  intro RUN; inversion RUN; subst.
  match goal with LV : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion LV; subst end.
  match goal with ADD : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ =>
    apply scalar_binary_inv in ADD as [base [operand [BASE [INDEX OP]]]] end.
  destruct (B.array_value_inv BASE) as [b [VALUE ADDRESS]]; subst base.
  apply scalar_temp_inv in INDEX.
  destruct operand; try discriminate OP.
  exists i; repeat split; assumption || reflexivity.
Qed.

Lemma variable_lvalue_constant ge e le m id count index n b offset bf :
  le ! index = Some (Vint n) ->
  eval_lvalue ge e le m (B.A.array_lvalue id count (index_temp index)) b offset bf <->
  eval_lvalue ge e le m
    (B.A.array_lvalue id count (Econst_int (Int.repr (Int.signed n)) type_int32s)) b offset bf.
Proof.
  rewrite Int.repr_signed. intro LOOKUP; split; intro RUN;
    unfold B.A.array_lvalue in RUN; inversion RUN; subst.
  all: match goal with ADD : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ =>
    apply scalar_binary_inv in ADD as [base [operand [BASE [INDEX OP]]]] end.
  - apply scalar_temp_inv in INDEX; assert (operand = Vint n) by congruence; subst operand.
    apply eval_Ederef. eapply eval_Ebinop; [exact BASE | constructor | exact OP].
  - apply scalar_const_inv in INDEX; subst operand.
    apply eval_Ederef. eapply eval_Ebinop; [exact BASE | constructor; exact LOOKUP | exact OP].
Qed.

Lemma variable_store_constant fe ge e le m id count index value n trace le' m' outcome :
  le ! index = Some (Vint n) ->
  exec_stmt fe ge e le m (variable_store id count index value) trace le' m' outcome <->
  exec_stmt fe ge e le m (B.constant_store id count (Int.signed n) value) trace le' m' outcome.
Proof.
  intro LOOKUP; split; intro RUN; inversion RUN; subst;
    eapply exec_Sassign; eauto.
  - apply (proj1 (@variable_lvalue_constant ge e _ m id count index n _ _ _ LOOKUP)); eassumption.
  - apply (proj2 (@variable_lvalue_constant ge e _ m id count index n _ _ _ LOOKUP)); eassumption.
Qed.

Lemma variable_pair_domain fe ge e le m id count first second left right le' m' :
  exec_stmt fe ge e le m (variable_pair id count first second left right) E0 le' m' Out_normal ->
  index_domain first second (Entry ge e le m) /\ le' = le.
Proof.
  intro RUN; inversion RUN; subst; [|contradiction].
  match goal with HEAD : exec_stmt _ _ _ _ _ (variable_store _ _ first _) _ _ _ _ |- _ =>
    destruct (variable_store_domain HEAD) as [x [X [TRACE [TEMPS OUT]]]]; subst end.
  match goal with TAIL : exec_stmt _ _ _ _ _ (variable_store _ _ second _) _ _ _ _ |- _ =>
    destruct (variable_store_domain TAIL) as [y [Y [TRACE2 [TEMPS2 OUT2]]]]; subst end.
  split; [exists x, y; split; assumption | reflexivity].
Qed.

Lemma variable_pair_constant fe ge e le m id count first second left right x y le' m' :
  le ! first = Some (Vint x) -> le ! second = Some (Vint y) ->
  exec_stmt fe ge e le m (variable_pair id count first second left right) E0 le' m' Out_normal <->
  exec_stmt fe ge e le m (Stores.store_pair id count (Int.signed x) (Int.signed y) left right)
    E0 le' m' Out_normal.
Proof.
  intros X Y; split; intro RUN; inversion RUN; subst; [|contradiction | |contradiction].
  - match goal with HEAD : exec_stmt _ _ _ _ _ (variable_store _ _ first _) _ _ _ _ |- _ =>
      destruct (variable_store_domain HEAD) as [n [_ [TRACE [TEMPS OUT]]]]; subst;
      apply (proj1 (@variable_store_constant fe ge e le m id count first left x _ _ _ _ X)) in HEAD end.
    match goal with TAIL : exec_stmt _ _ _ _ _ (variable_store _ _ second _) _ _ _ _ |- _ =>
      apply (proj1 (@variable_store_constant fe ge e le _ id count second right y _ _ _ _ Y)) in TAIL end.
    eapply exec_Sseq_1; eauto.
  - match goal with HEAD : exec_stmt _ _ _ _ _ (B.constant_store _ _ (Int.signed x) _) _ _ _ _ |- _ =>
      assert (TEMPS : le1 = le) by (inversion HEAD; reflexivity); subst le1;
      apply (proj2 (@variable_store_constant fe ge e le m id count first left x _ _ _ _ X)) in HEAD end.
    match goal with TAIL : exec_stmt _ _ _ _ _ (B.constant_store _ _ (Int.signed y) _) _ _ _ _ |- _ =>
      apply (proj2 (@variable_store_constant fe ge e le _ id count second right y _ _ _ _ Y)) in TAIL end.
    eapply exec_Sseq_1; eauto.
Qed.

Definition dynamic_rule id count first second left right
  (BOUND : B.A.array_bound_ok count = true) :
  encoded_region_rule (variable_pair id count first second left right)
    (variable_pair id count second first right left).
Proof.
  assert (COUNT : Int.min_signed <= count <= Int.max_signed).
  { destruct (B.A.array_bound_ok_sound count BOUND) as [POS [UP _]].
    change (count <= 2147483647) in UP.
    change (-2147483648 <= count <= 2147483647); lia. }
  refine {| region_rule_atoms := index_atom;
    region_rule_domain := index_domain first second;
    region_rule_dimension := index_dimension count first second;
    region_rule_primitives := index_primitives first second COUNT;
    region_rule_formula := independent_indices |}.
  - intros; eapply (proj1 (variable_pair_domain ltac:(eassumption))).
  - intros temps p e le m le' m' SOURCE PROPERTY.
    destruct (independent_indices_property PROPERTY) as [x [y [X [Y [RX [RY NE]]]]]].
    cbn [entry_temps] in X, Y.
    apply (proj1 (@variable_pair_constant (adapter_entry temps) (globalenv p) e le m
      id count first second left right x y le' m' X Y)) in SOURCE.
    destruct (Stores.store_pair_endpoint RX RY NE BOUND SOURCE) as [final [RUN EQ]].
    exists final; split; [|exact EQ].
    apply (proj2 (@variable_pair_constant (adapter_entry temps) (globalenv p) e le m
      id count second first right left y x le' final Y X)); exact RUN.
Defined.

Definition select_dynamic_pair id count first second left right source : option statement :=
  match Bool.bool_dec (B.A.array_bound_ok count) true with
  | left BOUND =>
    match flatten_region source with
    | [head; tail] =>
      if statement_eq (Ssequence head tail) (variable_pair id count first second left right)
      then Some (generated_region (dynamic_rule id count first second left right BOUND)) else None
    | _ => None end
  | right _ => None end.

Theorem select_dynamic_pair_sound id count first second left right source target :
  select_dynamic_pair id count first second left right source = Some target -> region_contract source target.
Proof.
  unfold select_dynamic_pair; destruct (Bool.bool_dec (B.A.array_bound_ok count) true) as [BOUND|];
    try discriminate.
  destruct (flatten_region source) as [|head [|tail [|extra rest]]] eqn:FLAT; try discriminate.
  destruct (statement_eq (Ssequence head tail) (variable_pair id count first second left right)) as [EQ|];
    try discriminate.
  intro SELECT; inversion SELECT; subst target.
  intros temps p e le m le' m' SOURCE f k.
  assert (RUN : exec_stmt (adapter_entry temps) (globalenv p) e le m
    (variable_pair id count first second left right) E0 le' m' Out_normal).
  { rewrite <- EQ; eapply flattened_pair_execution; eauto. }
  exact (@encoded_region_rule_sound _ _ (dynamic_rule id count first second left right BOUND)
    temps p e le m le' m' RUN f k).
Qed.

Definition compile_dynamic_pair id count first second left right :=
  compile_with_regions select_no_wrap select_signed_memory_rewrites
    (select_dynamic_pair id count first second left right).

Theorem compile_dynamic_pair_correct id count first second left right p target :
  compile_dynamic_pair id count first second left right p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof.
  unfold compile_dynamic_pair; apply compile_with_regions_correct.
  - exact select_no_wrap_sound.
  - exact (select_dynamic_pair_sound id count first second left right).
  - exact select_signed_memory_rewrites_sound.
Qed.

Goal True. idtac "GUARDCERT_DYNAMIC_STORE_BASELINE_BEGIN". exact Logic.I. Qed.
Print Assumptions Compiler.transf_c_program_correct.
Goal True. idtac "GUARDCERT_DYNAMIC_STORE_ADAPTER_BEGIN". exact Logic.I. Qed.
Print Assumptions dynamic_rule.
Print Assumptions compile_dynamic_pair_correct.
Goal True. idtac "GUARDCERT_DYNAMIC_STORE_ASSUMPTIONS_END". exact Logic.I. Qed.
End PolCertDynamicStore.
