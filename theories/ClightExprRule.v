From Stdlib Require Import ZArith.
From compcert.common Require Import Memory.
From compcert.cfrontend Require Import Clight Cop.
From Guard Require Import Presumption Synthesis ClightExprRewrite.

(** Full entry snapshots are available to a plugin's encoding.  This does not
    grant a guard permission to load memory: its lowering theorem must prove
    every guard evaluation defined, from a defined source evaluation. *)
Definition snapshot := (env * temp_env * mem)%type.

Record encoded_expression_rule (source guard candidate : expr) := {
  expression_modulus : Z;
  expression_view : snapshot -> Presumption.state;
  expression_obligation : snapshot -> Prop;
  expression_encoding : Synthesis.presumption_encoding
    expression_modulus expression_view expression_obligation;
  expression_type : typeof candidate = typeof source;
  expression_lowering : forall ge e le m v,
    eval_expr ge e le m source v ->
    exists vg b,
      eval_expr ge e le m guard vg /\ bool_val vg (typeof guard) m = Some b /\
      Synthesis.execute expression_modulus (expression_view (e, le, m))
        (Synthesis.synthesize (Synthesis.encoded_presumption expression_encoding)) = Some b;
  expression_local : forall ge e le m v,
    eval_expr ge e le m source v -> expression_obligation (e, le, m) ->
    eval_expr ge e le m candidate v
}.

Theorem encoded_expression_rule_sound : forall a g c,
  encoded_expression_rule a g c -> expression_contract a g c.
Proof.
  intros a g c [modulus view obligation encoding TYPE LOWER LOCAL].
  split; [exact TYPE|]. intros ge e le m v EV.
  destruct (LOWER ge e le m v EV) as [vg [b [EG [BG CHECK]]]].
  exists vg, b. split; [exact EG|]. split; [exact BG|].
  intro ACCEPT. eapply LOCAL; eauto.
  apply (proj1 (@Synthesis.encoded_condition_correct snapshot modulus view
    obligation encoding (e, le, m) b CHECK)); exact ACCEPT.
Qed.

Lemma expression_binop_inv : forall ge e le m op l r ty v,
  eval_expr ge e le m (Ebinop op l r ty) v ->
  exists vl vr, eval_expr ge e le m l vl /\ eval_expr ge e le m r vr /\
    sem_binary_operation ge op vl (typeof l) vr (typeof r) m = Some v.
Proof.
  intros ge e le m op l r ty v H; inversion H; subst; eauto.
  match goal with H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H end.
Qed.

Lemma lift_binop_left : forall a g c op r ty,
  expression_contract a g c ->
  expression_contract (Ebinop op a r ty) g (Ebinop op c r ty).
Proof.
  intros a g c op r ty [TYPE CONTRACT]. split; [reflexivity|].
  intros ge e le m v EV. apply expression_binop_inv in EV.
  destruct EV as [vl [vr [EL [ER OP]]]].
  destruct (CONTRACT ge e le m vl EL) as [vg [b [EG [BG LOCAL]]]].
  exists vg, b. repeat split; auto. intro ACCEPT.
  eapply eval_Ebinop; eauto. rewrite TYPE; exact OP.
Qed.

Lemma lift_binop_right : forall a g c op l ty,
  expression_contract a g c ->
  expression_contract (Ebinop op l a ty) g (Ebinop op l c ty).
Proof.
  intros a g c op l ty [TYPE CONTRACT]. split; [reflexivity|].
  intros ge e le m v EV. apply expression_binop_inv in EV.
  destruct EV as [vl [vr [EL [ER OP]]]].
  destruct (CONTRACT ge e le m vr ER) as [vg [b [EG [BG LOCAL]]]].
  exists vg, b. repeat split; auto. intro ACCEPT.
  eapply eval_Ebinop; eauto. rewrite TYPE; exact OP.
Qed.

Lemma lift_unop : forall a g c op ty,
  expression_contract a g c -> expression_contract (Eunop op a ty) g (Eunop op c ty).
Proof.
  intros a g c op ty [TYPE CONTRACT]. split; [reflexivity|].
  intros ge e le m v EV. inversion EV; subst.
  - match goal with INNER : eval_expr _ _ _ _ a v1 |- _ =>
      destruct (CONTRACT ge e le m v1 INNER) as [vg [b [EG [BG LOCAL]]]] end.
    exists vg, b. repeat split; auto. intro ACCEPT.
    eapply eval_Eunop; eauto. rewrite TYPE; assumption.
  - match goal with H : eval_lvalue _ _ _ _ (Eunop _ _ _) _ _ _ |- _ => inversion H end.
Qed.

Lemma lift_cast : forall a g c ty,
  expression_contract a g c -> expression_contract (Ecast a ty) g (Ecast c ty).
Proof.
  intros a g c ty [TYPE CONTRACT]. split; [reflexivity|].
  intros ge e le m v EV. inversion EV; subst.
  - match goal with INNER : eval_expr _ _ _ _ a v1 |- _ =>
      destruct (CONTRACT ge e le m v1 INNER) as [vg [b [EG [BG LOCAL]]]] end.
    exists vg, b. repeat split; auto. intro ACCEPT.
    eapply eval_Ecast; eauto. rewrite TYPE; assumption.
  - match goal with H : eval_lvalue _ _ _ _ (Ecast _ _) _ _ _ |- _ => inversion H end.
Qed.

(** One accepted rewrite per expression per pass, searching root, left, right.
    This is a bounded traversal, not a rewrite-to-fixpoint engine. *)
Fixpoint select_deep (select : expr -> option (expr * expr)) (a : expr)
  : option (expr * expr) :=
  match select a with
  | Some result => Some result
  | None => match a with
    | Ebinop op l r ty =>
        match select_deep select l with
        | Some (g, c) => Some (g, Ebinop op c r ty)
        | None => match select_deep select r with
                  | Some (g, c) => Some (g, Ebinop op l c ty)
                  | None => None end
        end
    | Eunop op x ty => match select_deep select x with
                      | Some (g, c) => Some (g, Eunop op c ty) | None => None end
    | Ecast x ty => match select_deep select x with
                   | Some (g, c) => Some (g, Ecast c ty) | None => None end
    | _ => None
    end
  end.

Theorem select_deep_sound : forall select,
  (forall a g c, select a = Some (g, c) -> expression_contract a g c) ->
  forall a g c, select_deep select a = Some (g, c) -> expression_contract a g c.
Proof.
  intros select SOUND a; induction a; intros g c SEL;
    cbn [select_deep] in SEL;
    destruct (select _) as [[g' c']|] eqn:ROOT;
    try solve [inversion SEL; subst; eapply SOUND; eauto]; try discriminate.
  - destruct (select_deep select a) as [[gg cc]|] eqn:CHILD; try discriminate.
    inversion SEL; subst; apply lift_unop; eauto.
  - destruct (select_deep select a1) as [[gg cc]|] eqn:LEFT.
    + inversion SEL; subst; apply lift_binop_left; eauto.
    + destruct (select_deep select a2) as [[gg cc]|] eqn:RIGHT; try discriminate.
      inversion SEL; subst; apply lift_binop_right; eauto.
  - destruct (select_deep select a) as [[gg cc]|] eqn:CHILD; try discriminate.
    inversion SEL; subst; apply lift_cast; eauto.
Qed.
