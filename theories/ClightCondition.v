From Stdlib Require Import Bool List.
From compcert.common Require Import Values Memory Events Globalenvs Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts ClightGuard.
Set Implicit Arguments.

(** This IR contains only pure guard tests and two leaves.  Lowering replaces
    leaves by statements and branches by actual Clight Sifthenelse. *)
Inductive decision_tree :=
| Decision (accept : bool)
| Test (condition : expr) (yes no : decision_tree).

Record clight_entry := Entry {
  entry_ge : genv;
  entry_env : env;
  entry_temps : temp_env;
  entry_memory : mem
}.

Definition expression_test (a : expr) (s : clight_entry) (b : bool) : Prop :=
  exists v, eval_expr (entry_ge s) (entry_env s) (entry_temps s)
    (entry_memory s) a v /\ bool_val v (typeof a) (entry_memory s) = Some b.

Inductive decision_run (s : clight_entry) : decision_tree -> bool -> Prop :=
| run_decision : forall b, decision_run s (Decision b) b
| run_test : forall a yes no b result,
    expression_test a s b -> decision_run s (if b then yes else no) result ->
    decision_run s (Test a yes no) result.

Definition decision_language : language clight_entry.
Proof.
  refine {| command := decision_tree; test := expr; observation := bool;
    command_run := fun t s b => decision_run s t b;
    test_run := expression_test; conditional := Test |}.
  intros a yes no s result; split.
  - intro RUN; inversion RUN; subst; eauto.
  - intros [b [CHECK RUN]]; econstructor; eauto.
Defined.

Fixpoint tree_statement (t : decision_tree) (yes no : statement) : statement :=
  match t with
  | Decision b => if b then yes else no
  | Test a l r => Sifthenelse a (tree_statement l yes no) (tree_statement r yes no)
  end.

Lemma decision_dispatch : forall temps ge e le m t b,
  decision_run (Entry ge e le m) t b -> forall f k yes no,
  star (adapter_step temps) ge
    (State f (tree_statement t yes no) k e le m) E0
    (State f (if b then yes else no) k e le m).
Proof.
  intros temps ge e le m t b RUN; induction RUN; intros f k yes0 no0; simpl.
  - apply star_refl.
  - destruct H as [v [EV BOOL]].
    eapply star_left.
    + unfold adapter_step. eapply step_ifthenelse; exact EV || exact BOOL.
    + destruct b; exact (IHRUN f k yes0 no0).
    + reflexivity.
Qed.

Lemma decision_fragment_run function_entry ge e le m t b :
  decision_run (Entry ge e le m) t b -> forall yes no trace le' m' out,
  exec_stmt function_entry ge e le m (if b then yes else no) trace le' m' out ->
  exec_stmt function_entry ge e le m (tree_statement t yes no) trace le' m' out.
Proof.
  intro RUN; induction RUN; intros yes0 no0 trace0 le' m' out LEAF; cbn [tree_statement]; auto.
  destruct H as [v [EV BOOL]]. eapply exec_Sifthenelse; eauto.
  destruct b; cbn in *; eauto.
Qed.
(** Generated conditions are actual trees, with unknown directed to fallback.
    No trusted boolean-expression compiler or native overflow flag is assumed. *)
Definition synthesize_tree {A I E}
  (P : @check_primitives clight_entry A decision_language I E)
  (p : formula A) : decision_tree :=
  compile_condition P p (Decision true) (Decision false) (Decision false).

Theorem synthesized_tree_correct : forall A I E
  (P : @check_primitives clight_entry A decision_language I E) p s b,
  I s -> (decision_run s (synthesize_tree P p) b <->
          b = formula_accepts E p s).
Proof.
  intros A I E P p s b INV.
  change (command_run decision_language
    (compile_condition P p (Decision true) (Decision false) (Decision false)) s b
    <-> b = formula_accepts E p s).
  rewrite compile_condition_correct by exact INV.
  unfold formula_accepts.
  destruct (formula_execute E p s) as [v|]; [destruct v|];
    cbn [selected_command decision_language]; split; intro H;
    try (inversion H; reflexivity); subst; constructor.
Qed.

Theorem synthesized_tree_property : forall A I
  (D : property_dimension clight_entry A I)
  (P : check_primitives decision_language I (decide_atom D)) p s,
  I s -> decision_run s (synthesize_tree P p) true ->
  formula_property (atom_property D) p s.
Proof.
  intros A I D P p s INV RUN.
  apply synthesized_tree_correct in RUN; auto.
  unfold formula_accepts in RUN.
  destruct (formula_execute (decide_atom D) p s) as [v|] eqn:EX;
    try discriminate. destruct v; try discriminate.
  exact (@formula_property_decision clight_entry A I D p s true INV EX).
Qed.

(** A second language instance describes terminating Clight fragments.  Its
    observations retain trace, temps, memory and control outcome.  This theorem
    alone says nothing about divergence; the decision_dispatch lemma is what
    allows the whole-program small-step host to account for divergent programs. *)
Record fragment_observation := FragmentObservation {
  fragment_trace : trace;
  fragment_temps : temp_env;
  fragment_memory : mem;
  fragment_outcome : outcome
}.

Definition fragment_language
  (function_entry : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop)
  : language clight_entry.
Proof.
  refine {| command := statement; test := expr; observation := fragment_observation;
    command_run := fun c s o => exec_stmt function_entry (entry_ge s) (entry_env s)
      (entry_temps s) (entry_memory s) c (fragment_trace o) (fragment_temps o)
      (fragment_memory o) (fragment_outcome o);
    test_run := expression_test; conditional := Sifthenelse |}.
  intros a yes no s o; split.
  - intro RUN; inversion RUN; subst; eexists; split; eauto.
    unfold expression_test; eauto.
  - intros [b [[v [EV BOOL]] RUN]]. econstructor; eauto.
Defined.

Print Assumptions decision_dispatch.
Print Assumptions synthesized_tree_correct.
Print Assumptions fragment_language.
