From Stdlib Require Import Bool List.
From compcert.lib Require Import Coqlib Maps.
From compcert.common Require Import AST Values Memory Globalenvs Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight.

(** A first real IR adapter: eliminate the then-branch under a pure guard.
    The contract is relative to a defined evaluation of the original condition.
    No source-level assumption is required by the whole-program theorem. *)
Definition guard_contract (a g : expr) : Prop :=
  forall ge e le m v b,
  eval_expr ge e le m a v -> bool_val v (typeof a) m = Some b ->
  exists vg bg,
    eval_expr ge e le m g vg /\ bool_val vg (typeof g) m = Some bg /\
    (bg = true -> b = false).

(** Both Clight entry conventions are supported.  The executable compiler
    inserts this pass after SimplLocals, where scalar locals are temporaries. *)
Definition adapter_entry (temps : bool) (ge : genv) :=
  if temps then function_entry2 ge else function_entry1 ge.
Definition adapter_step (temps : bool) (ge : genv) := step ge (adapter_entry temps ge).
Definition adapter_semantics (temps : bool) (p : program) :=
  let ge := globalenv p in
  Smallstep.Semantics_gen (adapter_step temps) (initial_state p) final_state ge ge.

(** Duplicating a labeled branch could change a goto's first matching label.
    Reject that region, while allowing labels elsewhere in the program. *)
Fixpoint label_free (s : statement) : bool :=
  match s with
  | Ssequence l r | Sifthenelse _ l r | Sloop l r => label_free l && label_free r
  | Sswitch _ cases => labels_free cases
  | Slabel _ _ => false
  | _ => true
  end
with labels_free (cases : labeled_statements) : bool :=
  match cases with
  | LSnil => true
  | LScons _ s rest => label_free s && labels_free rest
  end.

Section TRANSFORM.
Variable select_guard : expr -> option expr.

Fixpoint transform_statement (s : statement) : statement :=
  match s with
  | Ssequence l r => Ssequence (transform_statement l) (transform_statement r)
  | Sifthenelse a l r =>
      match select_guard a with
      | Some g =>
          if label_free l && label_free r
          then Sifthenelse g r (Sifthenelse a l r)
          else Sifthenelse a (transform_statement l) (transform_statement r)
      | None => Sifthenelse a (transform_statement l) (transform_statement r)
      end
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
     prog_public := prog_public p;
     prog_main := prog_main p;
     prog_types := prog_types p;
     prog_comp_env := prog_comp_env p;
     prog_comp_env_eq := prog_comp_env_eq p |}.
End TRANSFORM.

(** This relation is independent of any optimization's recognizer.  Unchanged
    subtrees are related structurally, including in a fallback branch. *)
Inductive match_statement : statement -> statement -> Prop :=
| ms_skip : match_statement Sskip Sskip
| ms_assign : forall l r, match_statement (Sassign l r) (Sassign l r)
| ms_set : forall id a, match_statement (Sset id a) (Sset id a)
| ms_call : forall id a args, match_statement (Scall id a args) (Scall id a args)
| ms_builtin : forall id ef tys args,
    match_statement (Sbuiltin id ef tys args) (Sbuiltin id ef tys args)
| ms_seq : forall l r tl tr,
    match_statement l tl -> match_statement r tr ->
    match_statement (Ssequence l r) (Ssequence tl tr)
| ms_if : forall a l r tl tr,
    match_statement l tl -> match_statement r tr ->
    match_statement (Sifthenelse a l r) (Sifthenelse a tl tr)
| ms_guard : forall a g l r,
    guard_contract a g -> label_free l = true -> label_free r = true ->
    match_statement (Sifthenelse a l r) (Sifthenelse g r (Sifthenelse a l r))
| ms_loop : forall l r tl tr,
    match_statement l tl -> match_statement r tr ->
    match_statement (Sloop l r) (Sloop tl tr)
| ms_break : match_statement Sbreak Sbreak
| ms_continue : match_statement Scontinue Scontinue
| ms_return : forall a, match_statement (Sreturn a) (Sreturn a)
| ms_switch : forall a cases tcases,
    match_cases cases tcases -> match_statement (Sswitch a cases) (Sswitch a tcases)
| ms_label : forall lbl s ts,
    match_statement s ts -> match_statement (Slabel lbl s) (Slabel lbl ts)
| ms_goto : forall lbl, match_statement (Sgoto lbl) (Sgoto lbl)
with match_cases : labeled_statements -> labeled_statements -> Prop :=
| mc_nil : match_cases LSnil LSnil
| mc_cons : forall tag s rest ts trest,
    match_statement s ts -> match_cases rest trest ->
    match_cases (LScons tag s rest) (LScons tag ts trest).

Scheme statement_ind2 := Induction for statement Sort Prop
with cases_ind2 := Induction for labeled_statements Sort Prop.
Combined Scheme statement_cases_ind from statement_ind2, cases_ind2.
Scheme match_statement_ind2 := Induction for match_statement Sort Prop
with match_cases_ind2 := Induction for match_cases Sort Prop.
Combined Scheme match_statement_cases_ind from match_statement_ind2, match_cases_ind2.

Lemma match_statement_reflexive :
  (forall s, match_statement s s) /\ (forall cases, match_cases cases cases).
Proof. apply statement_cases_ind; intros; constructor; auto. Qed.

Lemma transform_statement_matches : forall select_guard,
  (forall a g, select_guard a = Some g -> guard_contract a g) ->
  (forall s, match_statement s (transform_statement select_guard s)) /\
  (forall cases, match_cases cases (transform_cases select_guard cases)).
Proof.
  intros select_guard SOUND. apply statement_cases_ind; intros; simpl;
    try (constructor; auto).
  destruct (select_guard e) as [g|] eqn:SEL; [|constructor; auto].
  destruct (label_free s && label_free s0) eqn:FREE; [|constructor; auto].
  apply andb_true_iff in FREE as [L R]. constructor; eauto.
Qed.
