From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Misc.
From polcert.polygen Require Import InstrTy Loop.
From Guard Require Import PolCertLoopGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Known mathematical parameters may be specialized before bound adaptation.
    Unknown iterators remain unknown under each binder. These facts do not
    license machine reads or replace a final candidate certificate. *)
Module PolCertParameterSpecializationFor (I : INSTR) (M : LOOP_MODEL I).
Module L := M.
Module IS := I.IterSem.
Definition facts_hold facts env := forall index value,
  nth_error facts index=Some (Some value) -> nth index env 0=value.
Definition singleton_facts ranges := map (fun range : Z*Z =>
  if fst range=?snd range then Some (fst range) else None) ranges.
Lemma singleton_facts_hold ranges env :
  Forall2 (fun range value=>fst range<=value<=snd range) ranges env ->
  facts_hold (singleton_facts ranges) env.
Proof.
  intro RANGES; induction RANGES; intros [|index] value KNOWN;
    cbn [singleton_facts map nth_error nth] in KNOWN |- *; try discriminate.
  - destruct (fst x=?snd x) eqn:EQUAL; try discriminate.
    apply Z.eqb_eq in EQUAL; inversion KNOWN; subst; lia.
  - eapply IHRANGES; exact KNOWN.
Qed.
Lemma unknown_binder facts env value : facts_hold facts env ->
  facts_hold (None::facts) (value::env).
Proof.
  intros KNOWN [|index] found MEMBER; cbn in MEMBER |- *; try discriminate.
  eapply KNOWN; exact MEMBER.
Qed.

Fixpoint expression facts e :=
  match e with
  | L.Constant _=>e
  | L.Var index=>match nth_error facts index with
    | Some (Some value)=>L.Constant value | _=>e end
  | L.Sum a b=>L.make_sum (expression facts a) (expression facts b)
  | L.Mult k a=>L.make_mult k (expression facts a)
  | L.Div a k=>L.make_div (expression facts a) k
  | L.Mod a k=>L.make_mod (expression facts a) k
  | L.Max a b=>L.make_max (expression facts a) (expression facts b)
  | L.Min a b=>L.make_min (expression facts a) (expression facts b) end.
Lemma expression_correct e facts env : facts_hold facts env ->
  L.eval_expr env (expression facts e)=L.eval_expr env e.
Proof.
  intro KNOWN; induction e; cbn [expression L.eval_expr]; try reflexivity;
    rewrite ?L.make_sum_correct, ?L.make_mult_correct, ?L.make_div_correct,
      ?L.make_mod_correct, ?L.make_max_correct, ?L.make_min_correct,
      ?IHe, ?IHe1, ?IHe2; try reflexivity.
  destruct (nth_error facts n) as [[value|]|] eqn:FOUND; cbn [L.eval_expr]; try reflexivity.
  symmetry; apply KNOWN; exact FOUND.
Qed.
Lemma arguments_correct args facts env : facts_hold facts env ->
  map (L.eval_expr env) (map (expression facts) args)=map (L.eval_expr env) args.
Proof.
  intro KNOWN; rewrite map_map; apply map_ext; intro e.
  apply expression_correct; exact KNOWN.
Qed.
Fixpoint test facts t :=
  match t with
  | L.LE a b=>L.LE (expression facts a) (expression facts b)
  | L.EQ a b=>L.EQ (expression facts a) (expression facts b)
  | L.And a b=>L.And (test facts a) (test facts b)
  | L.Or a b=>L.Or (test facts a) (test facts b)
  | L.Not a=>L.Not (test facts a)
  | L.TConstantTest _=>t end.
Lemma test_correct t facts env : facts_hold facts env ->
  L.eval_test env (test facts t)=L.eval_test env t.
Proof.
  intro KNOWN; induction t; cbn [test L.eval_test];
    rewrite ?expression_correct by exact KNOWN;
    rewrite ?IHt,?IHt1,?IHt2; reflexivity.
Qed.
Fixpoint statement facts body :=
  match body with
  | L.Loop lower upper body=>L.Loop (expression facts lower) (expression facts upper)
      (statement (None::facts) body)
  | L.Instr instruction args=>L.Instr instruction (map (expression facts) args)
  | L.Guard condition body=>L.Guard (test facts condition) (statement facts body)
  | L.Seq statements=>L.Seq (sequence facts statements) end
with sequence facts statements :=
  match statements with
  | L.SNil=>L.SNil
  | L.SCons head rest=>L.SCons (statement facts head) (sequence facts rest) end.
Scheme specialization_stmt_ind := Induction for L.stmt Sort Prop
with specialization_list_ind := Induction for L.stmt_list Sort Prop.
Combined Scheme specialization_ind from specialization_stmt_ind,specialization_list_ind.

Theorem statement_correct :
  (forall body facts env before after, facts_hold facts env ->
    (L.loop_semantics (statement facts body) env before after <->
     L.loop_semantics body env before after)) /\
  (forall bodies facts env before after, facts_hold facts env ->
    (L.loop_semantics (L.Seq (sequence facts bodies)) env before after <->
     L.loop_semantics (L.Seq bodies) env before after)).
Proof.
  apply specialization_ind.
  - intros lower upper body IH facts env before after KNOWN; cbn [statement].
    split; intro RUN; inversion RUN; subst; apply L.LLoop;
      rewrite ?expression_correct by exact KNOWN.
    + match goal with ITER : IS.iter_semantics _ _ _ _ |- _ =>
        rewrite !expression_correct in ITER by exact KNOWN;
        eapply IS.iter_semantics_map with (P:=fun x=>L.loop_semantics (statement (None::facts) body) (x::env));
          [|exact ITER] end.
      intros x a b MEMBER EXEC; apply (proj1 (IH _ _ _ _ (unknown_binder x KNOWN))); exact EXEC.
    + eapply IS.iter_semantics_map with (P:=fun x=>L.loop_semantics body (x::env)); [|eassumption].
      intros x a b MEMBER EXEC; apply (proj2 (IH _ _ _ _ (unknown_binder x KNOWN))); exact EXEC.
  - intros instruction args facts env before after KNOWN; cbn [statement].
    split; intro RUN; inversion RUN; subst; eapply L.LInstr;
      rewrite ?arguments_correct in * by exact KNOWN; eauto.
  - intros bodies IH facts env before after KNOWN; cbn [statement]; apply IH; exact KNOWN.
  - intros condition body IH facts env before after KNOWN; cbn [statement].
    split; intro RUN; inversion RUN; subst.
    + apply L.LGuardTrue; [apply (proj1 (IH _ _ _ _ KNOWN)); assumption|].
      rewrite test_correct in * by exact KNOWN; assumption.
    + apply L.LGuardFalse; rewrite test_correct in * by exact KNOWN; assumption.
    + apply L.LGuardTrue; [apply (proj2 (IH _ _ _ _ KNOWN)); assumption|].
      rewrite test_correct by exact KNOWN; assumption.
    + apply L.LGuardFalse; rewrite test_correct by exact KNOWN; assumption.
  - intros facts env before after KNOWN; cbn [sequence]; reflexivity.
  - intros head IH rest IHREST facts env before after KNOWN; cbn [sequence].
    split; intro RUN; inversion RUN; subst; eapply L.LSeq.
    + apply (proj1 (IH _ _ _ _ KNOWN)); eassumption.
    + apply (proj1 (IHREST _ _ _ _ KNOWN)); eassumption.
    + apply (proj2 (IH _ _ _ _ KNOWN)); eassumption.
    + apply (proj2 (IHREST _ _ _ _ KNOWN)); eassumption.
Qed.
End PolCertParameterSpecializationFor.
