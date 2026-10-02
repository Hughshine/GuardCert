From Stdlib Require Import Bool List.
From compcert.lib Require Import Coqlib Maps.
From compcert.common Require Import AST Values Memory Globalenvs Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightGuard.

(** A pure expression rewrite preserves its type and value on acceptance.
    The guard must be defined whenever the source expression is defined.
    Evaluation leaves the entire memory, environment and trace unchanged. *)
Definition expression_contract (source guard candidate : expr) : Prop :=
  typeof candidate = typeof source /\
  forall ge e le m v, eval_expr ge e le m source v ->
  exists vg b,
    eval_expr ge e le m guard vg /\ bool_val vg (typeof guard) m = Some b /\
    (b = true -> eval_expr ge e le m candidate v).

Section TRANSFORM.
Variable select : expr -> option (expr * expr).

Definition version (a : expr) (context : expr -> statement) : statement :=
  match select a with
  | Some (g, candidate) => Sifthenelse g (context candidate) (context a)
  | None => context a
  end.

(** These three contexts contain no labels.  Wrapping them therefore needs no
    label barrier and is valid inside loops, switch cases and labeled bodies. *)
Fixpoint transform_statement (s : statement) : statement :=
  match s with
  | Sassign l r => version r (Sassign l)
  | Sset id a => version a (Sset id)
  | Sreturn (Some a) => version a (fun x => Sreturn (Some x))
  | Ssequence l r => Ssequence (transform_statement l) (transform_statement r)
  | Sifthenelse a l r => Sifthenelse a (transform_statement l) (transform_statement r)
  | Sloop l r => Sloop (transform_statement l) (transform_statement r)
  | Sswitch a cases => Sswitch a (transform_cases cases)
  | Slabel lbl body => Slabel lbl (transform_statement body)
  | _ => s
  end
with transform_cases (cases : labeled_statements) : labeled_statements :=
  match cases with
  | LSnil => LSnil
  | LScons tag s rest => LScons tag (transform_statement s) (transform_cases rest)
  end.

Definition transform_function (f : function) : function :=
  mkfunction (fn_return f) (fn_callconv f) (fn_params f) (fn_vars f)
    (fn_temps f) (transform_statement (fn_body f)).
Definition transform_fundef (fd : fundef) : fundef :=
  match fd with
  | Internal f => Internal (transform_function f)
  | External ef args res cc => External ef args res cc
  end.
Definition transform_program (p : program) : program :=
  {| prog_defs := List.map (AST.transform_program_globdef transform_fundef) (prog_defs p);
     prog_public := prog_public p; prog_main := prog_main p;
     prog_types := prog_types p; prog_comp_env := prog_comp_env p;
     prog_comp_env_eq := prog_comp_env_eq p |}.
End TRANSFORM.

Inductive match_statement : statement -> statement -> Prop :=
| ms_skip : match_statement Sskip Sskip
| ms_assign : forall l r, match_statement (Sassign l r) (Sassign l r)
| ms_assign_guard : forall l a g c, expression_contract a g c ->
    match_statement (Sassign l a) (Sifthenelse g (Sassign l c) (Sassign l a))
| ms_set : forall id a, match_statement (Sset id a) (Sset id a)
| ms_set_guard : forall id a g c, expression_contract a g c ->
    match_statement (Sset id a) (Sifthenelse g (Sset id c) (Sset id a))
| ms_call : forall id a args, match_statement (Scall id a args) (Scall id a args)
| ms_builtin : forall id ef tys args,
    match_statement (Sbuiltin id ef tys args) (Sbuiltin id ef tys args)
| ms_seq : forall l r tl tr, match_statement l tl -> match_statement r tr ->
    match_statement (Ssequence l r) (Ssequence tl tr)
| ms_if : forall a l r tl tr, match_statement l tl -> match_statement r tr ->
    match_statement (Sifthenelse a l r) (Sifthenelse a tl tr)
| ms_loop : forall l r tl tr, match_statement l tl -> match_statement r tr ->
    match_statement (Sloop l r) (Sloop tl tr)
| ms_break : match_statement Sbreak Sbreak
| ms_continue : match_statement Scontinue Scontinue
| ms_return : forall a, match_statement (Sreturn a) (Sreturn a)
| ms_return_guard : forall a g c, expression_contract a g c ->
    match_statement (Sreturn (Some a))
      (Sifthenelse g (Sreturn (Some c)) (Sreturn (Some a)))
| ms_switch : forall a cases tcases, match_cases cases tcases ->
    match_statement (Sswitch a cases) (Sswitch a tcases)
| ms_label : forall lbl s ts, match_statement s ts ->
    match_statement (Slabel lbl s) (Slabel lbl ts)
| ms_goto : forall lbl, match_statement (Sgoto lbl) (Sgoto lbl)
with match_cases : labeled_statements -> labeled_statements -> Prop :=
| mc_nil : match_cases LSnil LSnil
| mc_cons : forall tag s rest ts trest, match_statement s ts -> match_cases rest trest ->
    match_cases (LScons tag s rest) (LScons tag ts trest).

Scheme match_statement_ind2 := Induction for match_statement Sort Prop
with match_cases_ind2 := Induction for match_cases Sort Prop.
Combined Scheme match_statement_cases_ind from match_statement_ind2, match_cases_ind2.

Lemma transform_statement_matches : forall select,
  (forall a g c, select a = Some (g, c) -> expression_contract a g c) ->
  (forall s, match_statement s (transform_statement select s)) /\
  (forall cases, match_cases cases (transform_cases select cases)).
Proof.
  intros select SOUND. apply ClightGuard.statement_cases_ind; intros; simpl;
    try (constructor; auto).
  - unfold version. destruct (select e0) as [[g c]|] eqn:SEL; constructor; eauto.
  - unfold version. destruct (select e) as [[g c]|] eqn:SEL; constructor; eauto.
  - destruct o; simpl; [|constructor]. unfold version.
    destruct (select e) as [[g c]|] eqn:SEL; constructor; eauto.
Qed.
