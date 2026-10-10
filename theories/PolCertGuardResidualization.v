From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers.
From polcert.lib Require Import Misc.
From polcert.polygen Require Import InstrTy Loop.
From Guard Require Import PolCertLoopGuard PolCertAffineClight PolCertGuardedBodyPruning
  AbstractGuard SemanticFacts ResidualGuardCurrent.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Domain facts are scoped to binders and entered guards. The generic
    residualization library processes their Boolean combinations. Actual
    machine execution and private-parameter preservation remain host duties. *)
Module PolCertGuardResidualizationFor (I : INSTR) (M : LOOP_MODEL I).
Module L := M.
Module A := PolCertAffineClightFor I M.
Module B := PolCertGuardedBodyPruningFor I M.
Module IS := I.IterSem.

Fixpoint normalize_expr (e : L.expr) : L.expr :=
  match e with
  | L.Sum a b=>L.Sum (normalize_expr a) (normalize_expr b)
  | L.Mult k a=>L.Mult k (normalize_expr a)
  | L.Div a k=>if k=?1 then normalize_expr a else L.Div (normalize_expr a) k
  | L.Mod a k=>L.Mod (normalize_expr a) k
  | L.Max a b=>L.Max (normalize_expr a) (normalize_expr b)
  | L.Min a b=>L.Min (normalize_expr a) (normalize_expr b)
  | _=>e end.
Lemma normalize_expr_sound e env : L.eval_expr env (normalize_expr e)=L.eval_expr env e.
Proof.
  induction e; cbn [normalize_expr L.eval_expr]; try rewrite IHe; try rewrite IHe1,IHe2; try reflexivity.
  destruct (z=?1) eqn:ONE; [apply Z.eqb_eq in ONE; subst; rewrite IHe,Z.div_1_r|cbn [L.eval_expr]; rewrite IHe]; reflexivity.
Qed.
Fixpoint lift_expr (e : L.expr) : L.expr :=
  match e with
  | L.Var n=>L.Var (S n)
  | L.Sum a b=>L.Sum (lift_expr a) (lift_expr b)
  | L.Mult k a=>L.Mult k (lift_expr a)
  | L.Div a k=>L.Div (lift_expr a) k
  | L.Mod a k=>L.Mod (lift_expr a) k
  | L.Max a b=>L.Max (lift_expr a) (lift_expr b)
  | L.Min a b=>L.Min (lift_expr a) (lift_expr b)
  | _=>e end.
Lemma lift_expr_sound e x env : L.eval_expr (x::env) (lift_expr e)=L.eval_expr env e.
Proof. induction e; cbn [lift_expr L.eval_expr]; try rewrite IHe; try rewrite IHe1,IHe2; reflexivity. Qed.
Fixpoint normalize_test (test : L.test) : L.test :=
  match test with
  | L.LE a b=>L.LE (normalize_expr a) (normalize_expr b)
  | L.EQ a b=>L.EQ (normalize_expr a) (normalize_expr b)
  | L.And a b=>L.And (normalize_test a) (normalize_test b)
  | L.Or a b=>L.Or (normalize_test a) (normalize_test b)
  | L.Not a=>L.Not (normalize_test a)
  | _=>test end.
Lemma normalize_test_sound test env : L.eval_test env (normalize_test test)=L.eval_test env test.
Proof. induction test; cbn [normalize_test L.eval_test]; try rewrite !normalize_expr_sound; try rewrite IHtest; try rewrite IHtest1,IHtest2; reflexivity. Qed.
Fixpoint lift_test (test : L.test) : L.test :=
  match test with
  | L.LE a b=>L.LE (lift_expr a) (lift_expr b)
  | L.EQ a b=>L.EQ (lift_expr a) (lift_expr b)
  | L.And a b=>L.And (lift_test a) (lift_test b)
  | L.Or a b=>L.Or (lift_test a) (lift_test b)
  | L.Not a=>L.Not (lift_test a)
  | _=>test end.
Lemma lift_test_sound test x env : L.eval_test (x::env) (lift_test test)=L.eval_test env test.
Proof. induction test; cbn [lift_test L.eval_test]; try rewrite !lift_expr_sound; try rewrite IHtest; try rewrite IHtest1,IHtest2; reflexivity. Qed.
Definition test_eq_dec : forall a b : L.test, {a=b}+{a<>b}.
Proof. decide equality; apply B.expr_eq_dec || apply Bool.bool_dec. Defined.
Definition facts_hold facts env := Forall (fun fact=>L.eval_test env fact=true) facts.

Definition interval_atom bounds (atom : L.test) : option bool :=
  match atom with
  | L.LE a b=>match A.analyze bounds a,A.analyze bounds b with
    | Some a,Some b=>if A.upper a<=?A.lower b then Some true
      else if A.upper b<?A.lower a then Some false else None
    | _,_=>None end
  | _=>None end.
Lemma interval_atom_sound bounds atom env value : A.env_within bounds env ->
  interval_atom bounds atom=Some value -> L.eval_test env atom=value.
Proof.
  intros WITHIN CHECK; destruct atom; cbn [interval_atom] in CHECK; try discriminate.
  destruct (A.analyze bounds e) as [a|] eqn:FIRST;
    destruct (A.analyze bounds e0) as [b|] eqn:SECOND; try discriminate.
  destruct (A.analyze_sound _ FIRST WITHIN) as [LEFT _].
  destruct (A.analyze_sound _ SECOND WITHIN) as [RIGHT _].
  unfold A.contains in *; cbn [L.eval_test].
  destruct (A.upper a<=?A.lower b) eqn:TRUE; [inversion CHECK; subst; apply Z.leb_le in TRUE; apply Z.leb_le; lia|].
  destruct (A.upper b<?A.lower a) eqn:FALSE; try discriminate.
  inversion CHECK; subst; apply Z.ltb_lt in FALSE; apply Z.leb_gt; lia.
Qed.
Definition known_atom bounds facts atom :=
  if in_dec test_eq_dec atom facts then Some true else
  if in_dec test_eq_dec (L.Not atom) facts then Some false else interval_atom bounds atom.
Lemma known_atom_sound bounds facts atom env value :
  A.env_within bounds env -> facts_hold facts env ->
  known_atom bounds facts atom=Some value -> L.eval_test env atom=value.
Proof.
  intros WITHIN FACTS CHECK; unfold known_atom in CHECK.
  destruct (in_dec test_eq_dec atom facts) as [MEMBER|ABSENT].
  - inversion CHECK; subst; apply Forall_forall with (x:=atom) in FACTS; assumption.
  - destruct (in_dec test_eq_dec (L.Not atom) facts) as [MEMBER|ABSENT_NEGATIVE].
    + inversion CHECK; subst; apply Forall_forall with (x:=L.Not atom) in FACTS; [|exact MEMBER].
      cbn [L.eval_test] in FACTS; apply Bool.negb_true_iff; exact FACTS.
    + eapply interval_atom_sound; eauto.
Qed.

Fixpoint test_formula (test : L.test) : formula L.test :=
  match test with
  | L.TConstantTest value=>Constant value
  | L.And a b=>Conjunction (test_formula a) (test_formula b)
  | L.Or a b=>Disjunction (test_formula a) (test_formula b)
  | L.Not a=>Complement (test_formula a)
  | _=>Fact test end.
Fixpoint formula_test (expression : formula L.test) : L.test :=
  match expression with
  | Constant value=>L.TConstantTest value
  | Fact atom=>atom
  | Conjunction a b=>L.And (formula_test a) (formula_test b)
  | Disjunction a b=>L.Or (formula_test a) (formula_test b)
  | Complement a=>L.Not (formula_test a) end.
Lemma test_formula_property test env :
  formula_property (fun atom env=>L.eval_test env atom=true) (test_formula test) env <->
  L.eval_test env test=true.
Proof.
  induction test; cbn [test_formula formula_property L.eval_test]; try tauto.
  - rewrite IHtest1,IHtest2; symmetry; apply andb_true_iff.
  - rewrite IHtest1,IHtest2; symmetry; apply orb_true_iff.
  - rewrite IHtest; destruct (L.eval_test env test); cbn; intuition congruence.
  - destruct b; cbn; intuition congruence.
Qed.
Lemma formula_test_property expression env :
  L.eval_test env (formula_test expression)=true <->
  formula_property (fun atom env=>L.eval_test env atom=true) expression env.
Proof.
  induction expression; cbn [formula_test L.eval_test formula_property].
  - destruct value; cbn; intuition congruence.
  - tauto.
  - rewrite andb_true_iff,IHexpression1,IHexpression2; tauto.
  - rewrite orb_true_iff,IHexpression1,IHexpression2; tauto.
  - rewrite <- IHexpression; destruct (L.eval_test env (formula_test expression)); cbn; intuition congruence.
Qed.
Definition residual_test bounds facts test := formula_test
  (residualize (known_atom bounds facts) (test_formula (normalize_test test))).
Lemma residual_test_sound bounds facts test env : A.env_within bounds env -> facts_hold facts env ->
  L.eval_test env (residual_test bounds facts test)=L.eval_test env test.
Proof.
  intros WITHIN FACTS.
  assert (EQUIV : L.eval_test env (residual_test bounds facts test)=true <->L.eval_test env test=true).
  { unfold residual_test; rewrite formula_test_property.
    rewrite (@residualize_property (list Z) L.test
      (fun env=>A.env_within bounds env /\ facts_hold facts env)
      (fun atom env=>L.eval_test env atom=true) (known_atom bounds facts)).
    - rewrite test_formula_property,normalize_test_sound; reflexivity.
    - intros atom state value [RANGES HOLD] KNOWN.
      pose proof (@known_atom_sound bounds facts atom state value RANGES HOLD KNOWN) as VALUE.
      destruct value; cbn [decision_evidence]; [exact VALUE|rewrite VALUE; discriminate].
    - split; assumption. }
  destruct (L.eval_test env (residual_test bounds facts test)),(L.eval_test env test); intuition congruence.
Qed.

Fixpoint entered_facts (test : L.test) : list L.test :=
  match test with L.And a b=>entered_facts a++entered_facts b | _=>[test] end.
Lemma entered_facts_sound test env : L.eval_test env test=true ->facts_hold (entered_facts test) env.
Proof.
  induction test; cbn [entered_facts]; intro TRUE; try (constructor; [exact TRUE|constructor]).
  cbn [L.eval_test] in TRUE; apply andb_true_iff in TRUE as [FIRST SECOND].
  apply Forall_app; split; [exact (IHtest1 FIRST)|exact (IHtest2 SECOND)].
Qed.
Definition binder_facts facts lower upper := map lift_test facts++
  [L.LE (lift_expr (normalize_expr lower)) (L.Var O);
   L.LE (L.Sum (L.Var O) (L.Constant 1)) (lift_expr (normalize_expr upper))].
Lemma binder_facts_sound facts lower upper x env : facts_hold facts env ->
  In x (Zrange (L.eval_expr env lower) (L.eval_expr env upper)) ->
  facts_hold (binder_facts facts lower upper) (x::env).
Proof.
  intros FACTS MEMBER; apply Zrange_in in MEMBER; unfold binder_facts,facts_hold.
  apply Forall_app; split.
  - apply Forall_forall; intros test IN; apply in_map_iff in IN as [original [<- IN]].
    rewrite lift_test_sound; apply Forall_forall with (x:=original) in FACTS; assumption.
  - constructor.
    + change ((L.eval_expr (x::env) (lift_expr (normalize_expr lower))<=?x)=true).
      rewrite lift_expr_sound,normalize_expr_sound; apply Z.leb_le; exact (proj1 MEMBER).
    + constructor.
      * change ((x+1<=?L.eval_expr (x::env) (lift_expr (normalize_expr upper)))=true).
        rewrite lift_expr_sound,normalize_expr_sound; apply Z.leb_le; lia.
      * constructor.
Qed.

Definition residual_guard test body :=
  match test with L.TConstantTest true=>body | L.TConstantTest false=>L.Seq L.SNil
  | _=>L.Guard test body end.
Lemma residual_guard_execution test body env before after :
  L.loop_semantics (L.Guard test body) env before after ->
  L.loop_semantics (residual_guard test body) env before after.
Proof.
  destruct test; cbn [residual_guard]; try tauto.
  destruct b; intro RUN; inversion RUN; subst; cbn [L.eval_test] in *; try discriminate; auto; constructor.
Qed.
Fixpoint residual_statement bounds facts (statement : L.stmt) : L.stmt :=
  match statement with
  | L.Loop lower upper body=>match A.analyze bounds lower,A.analyze bounds upper with
    | Some lo,Some hi=>L.Loop (normalize_expr lower) (normalize_expr upper)
      (residual_statement (A.Interval (A.lower lo) (A.upper hi-1)::bounds)
        (binder_facts facts lower upper) body)
    | _,_=>statement end
  | L.Guard test body=>residual_guard (residual_test bounds facts test)
      (residual_statement bounds (facts++entered_facts (normalize_test test)) body)
  | L.Seq sequence=>L.Seq (residual_sequence bounds facts sequence)
  | _=>statement end
with residual_sequence bounds facts (sequence : L.stmt_list) : L.stmt_list :=
  match sequence with L.SNil=>L.SNil
  | L.SCons head tail=>L.SCons (residual_statement bounds facts head) (residual_sequence bounds facts tail) end.
Scheme residual_stmt_ind := Induction for L.stmt Sort Prop
with residual_list_ind := Induction for L.stmt_list Sort Prop.
Combined Scheme residual_ind from residual_stmt_ind,residual_list_ind.
Theorem residual_statement_sound :
  (forall statement bounds facts env before after,
    A.env_within bounds env -> facts_hold facts env ->L.loop_semantics statement env before after ->
    L.loop_semantics (residual_statement bounds facts statement) env before after) /\
  (forall sequence bounds facts env before after,
    A.env_within bounds env -> facts_hold facts env ->L.loop_semantics (L.Seq sequence) env before after ->
    L.loop_semantics (L.Seq (residual_sequence bounds facts sequence)) env before after).
Proof.
  apply residual_ind; intros.
  - cbn [residual_statement]; destruct (A.analyze bounds e) as [lo|] eqn:LOWER;
      destruct (A.analyze bounds e0) as [hi|] eqn:UPPER; try assumption.
    inversion H2; subst; apply L.LLoop; rewrite !normalize_expr_sound.
    eapply IS.iter_semantics_map with (P:=fun x=>L.loop_semantics s (x::env)); [|eassumption].
    intros x a b MEMBER RUN; apply H; [|apply binder_facts_sound; assumption|exact RUN].
    apply A.env_within_cons; [|exact H0].
    destruct (A.analyze_sound _ LOWER H0) as [LOW _].
    destruct (A.analyze_sound _ UPPER H0) as [HIGH _].
    apply Zrange_in in MEMBER; unfold A.contains in *; cbn; lia.
  - cbn [residual_statement]; assumption.
  - cbn [residual_statement]; eauto.
  - cbn [residual_statement]; apply residual_guard_execution.
    pose proof (@residual_test_sound bounds facts t env H0 H1) as TEST.
    inversion H2; subst.
    + apply L.LGuardTrue; [apply H|rewrite TEST; assumption]; try assumption.
      apply Forall_app; split; [exact H1|apply entered_facts_sound; rewrite normalize_test_sound; assumption].
    + apply L.LGuardFalse; rewrite TEST; assumption.
  - cbn [residual_sequence]; assumption.
  - cbn [residual_sequence]; inversion H3; subst; eapply L.LSeq; [eapply H|eapply H0]; eauto.
Qed.
Corollary residual_execution statement bounds env before after :
  A.env_within bounds env ->L.loop_semantics statement env before after ->
  L.loop_semantics (residual_statement bounds [] statement) env before after.
Proof. intros WITHIN RUN; eapply (proj1 residual_statement_sound); eauto; constructor. Qed.
End PolCertGuardResidualizationFor.
