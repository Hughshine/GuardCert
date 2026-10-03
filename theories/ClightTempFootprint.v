From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Clight.
From Guard Require Import ClightTempFrame.
Import ListNotations.
Set Implicit Arguments.

Fixpoint expression_temps (a : expr) : list ident :=
  match a with
  | Etempvar id _ => [id]
  | Ederef a _ | Eaddrof a _ | Eunop _ a _ | Ecast a _ | Efield a _ _ => expression_temps a
  | Ebinop _ a b _ => expression_temps a ++ expression_temps b
  | _ => []
  end.
Definition optional_temp (id : option ident) := match id with Some x => [x] | None => [] end.
Definition optional_expression_temps (a : option expr) :=
  match a with Some x => expression_temps x | None => [] end.
Definition expressions_temps (args : list expr) := flat_map expression_temps args.
Fixpoint statement_temps (s : statement) : list ident :=
  match s with
  | Sassign a b => expression_temps a ++ expression_temps b
  | Sset id a => id :: expression_temps a
  | Scall id a args => optional_temp id ++ expression_temps a ++ expressions_temps args
  | Sbuiltin id _ _ args => optional_temp id ++ expressions_temps args
  | Ssequence a b | Sloop a b => statement_temps a ++ statement_temps b
  | Sifthenelse a b c => expression_temps a ++ statement_temps b ++ statement_temps c
  | Sreturn a => optional_expression_temps a
  | Sswitch a cases => expression_temps a ++ cases_temps cases
  | Slabel _ body => statement_temps body
  | _ => []
  end
with cases_temps cases : list ident :=
  match cases with LSnil => [] | LScons _ s rest => statement_temps s ++ cases_temps rest end.
Definition expression_scope live a := incl (expression_temps a) live.
Definition expressions_scope live args := incl (expressions_temps args) live.
Definition statement_scope live s := incl (statement_temps s) live.
Definition cases_scope live cases := incl (cases_temps cases) live.

Lemma scope_append_left {A} (a b live : list A) : incl (a ++ b) live -> incl a live.
Proof. intros S id IN; apply S, in_or_app; auto. Qed.
Lemma scope_append_right {A} (a b live : list A) : incl (a ++ b) live -> incl b live.
Proof. intros S id IN; apply S, in_or_app; auto. Qed.
Lemma scope_cons_tail {A} (a : A) b live : incl (a :: b) live -> incl b live.
Proof. intros S id IN; apply S; cbn; auto. Qed.
Lemma scope_cons_head {A} (a : A) b live : incl (a :: b) live -> In a live.
Proof. intro S; apply S; cbn; auto. Qed.
Local Hint Resolve scope_append_left scope_append_right scope_cons_tail scope_cons_head : core.

Lemma expressions_temp_transport ge locals le memory :
  (forall a v, eval_expr ge locals le memory a v -> forall live target,
    expression_scope live a -> temp_agree live le target -> eval_expr ge locals target memory a v) /\
  (forall a b ofs bf, eval_lvalue ge locals le memory a b ofs bf -> forall live target,
    expression_scope live a -> temp_agree live le target -> eval_lvalue ge locals target memory a b ofs bf).
Proof.
  apply eval_expr_lvalue_ind; unfold expression_scope; cbn; intros;
    try solve [econstructor; eauto 6].
  apply eval_Etempvar; rewrite H1 by (apply H0; cbn; auto); exact H.
Qed.
Lemma expression_temp_transport ge locals le memory a v live target :
  expression_scope live a -> temp_agree live le target ->
  eval_expr ge locals le memory a v -> eval_expr ge locals target memory a v.
Proof. intros S EQ RUN; eapply (proj1 (expressions_temp_transport ge locals le memory)); eauto. Qed.
Lemma lvalue_temp_transport ge locals le memory a b ofs bf live target :
  expression_scope live a -> temp_agree live le target ->
  eval_lvalue ge locals le memory a b ofs bf -> eval_lvalue ge locals target memory a b ofs bf.
Proof. intros S EQ RUN; eapply (proj2 (expressions_temp_transport ge locals le memory)); eauto. Qed.
Lemma exprlist_temp_transport ge locals le memory args tys values live target :
  expressions_scope live args -> temp_agree live le target ->
  eval_exprlist ge locals le memory args tys values -> eval_exprlist ge locals target memory args tys values.
Proof.
  intros S EQ RUN; revert S; induction RUN; intro S; [constructor|].
  unfold expressions_scope, expressions_temps in S; cbn in S.
  econstructor.
  - eapply expression_temp_transport; [unfold expression_scope; eapply scope_append_left; exact S|exact EQ|eassumption].
  - eassumption.
  - apply IHRUN; unfold expressions_scope, expressions_temps; eapply scope_append_right; exact S.
Qed.
Lemma temp_agree_set_both live le target id value : temp_agree live le target ->
  temp_agree live (PTree.set id value le) (PTree.set id value target).
Proof. intros EQ key IN; rewrite !PTree.gsspec; destruct (peq key id); auto. Qed.
Lemma temp_agree_opttemp live le target id value : temp_agree live le target ->
  temp_agree live (set_opttemp id value le) (set_opttemp id value target).
Proof. destruct id; cbn; auto using temp_agree_set_both. Qed.
Lemma temp_agree_undef_append live declarations extra :
  (forall id, In id live -> ~ In id (var_names extra)) ->
  temp_agree live (create_undef_temps declarations) (create_undef_temps (declarations ++ extra)).
Proof.
  intro FRESH; induction declarations as [|[id ty] rest IH]; cbn.
  - intros key IN; induction extra as [|[id ty] rest IH']; cbn.
    + rewrite !PTree.gempty; reflexivity.
    + rewrite PTree.gso by (intro SAME; apply (FRESH key IN); cbn; auto).
      apply IH'; intros k MEMBER ABSURD; apply (FRESH k MEMBER); cbn; auto.
  - apply temp_agree_set_both; exact IH.
Qed.
Lemma bind_parameters_temp_agree params values le target le' live :
  temp_agree live le target -> bind_parameter_temps params values le = Some le' ->
  exists target', bind_parameter_temps params values target = Some target' /\ temp_agree live le' target'.
Proof.
  revert values le target le'; induction params as [|[id ty] rest IH]; intros [|value values] le target le' EQ BIND;
    cbn in BIND |- *; try discriminate.
  - inversion BIND; subst; exists target; auto.
  - apply IH with (le := PTree.set id value le); auto using temp_agree_set_both.
Qed.

Definition function_temps f := var_names (fn_params f) ++ var_names (fn_temps f) ++
  var_names (fn_vars f) ++ statement_temps (fn_body f).
Definition fundef_temps fd := match fd with Internal f => function_temps f | _ => [] end.
Definition global_definition_temps (d : ident * globdef fundef type) :=
  match snd d with Gfun fd => fst d :: fundef_temps fd | Gvar _ => [fst d] end.
Definition program_temps p := flat_map global_definition_temps (prog_defs p).

Print Assumptions expression_temp_transport.
Print Assumptions bind_parameters_temp_agree.
