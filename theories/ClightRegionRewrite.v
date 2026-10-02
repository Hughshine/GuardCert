From Stdlib Require Import Bool List Arith Lia.
From compcert.lib Require Import Coqlib Maps.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightFiniteRegion CompCertMemoryEquivalence.
Local Open Scope nat_scope.

(** The host consumes a local forward certificate.  It does not inspect the
    guard or require an optimization to use a particular property dimension. *)
Definition region_contract (source target : statement) : Prop :=
  forall temps p e le m le' m',
  exec_stmt (adapter_entry temps) (globalenv p) e le m source E0 le' m' Out_normal ->
  forall f k, exists target_memory,
    star (adapter_step temps) (globalenv p)
      (State f target k e le m) E0 (State f Sskip k e le' target_memory) /\
    memory_equivalent m' target_memory.

(** An optimization author supplies conditional local preservation; the
    shared decision compiler and region host handle fallback and composition. *)
Definition guarded_fragment_contract source guard candidate : Prop :=
  forall temps p e le m le' m',
  exec_stmt (adapter_entry temps) (globalenv p) e le m source E0 le' m' Out_normal ->
  exists b, decision_run (Entry (globalenv p) e le m) guard b /\
    (b = true -> exists target_memory,
      exec_stmt (adapter_entry temps) (globalenv p) e le m candidate E0 le' target_memory Out_normal /\
      memory_equivalent m' target_memory).

Lemma guarded_fragment_region_contract source guard candidate :
  guarded_fragment_contract source guard candidate ->
  region_contract source (tree_statement guard candidate source).
Proof.
  intros CONTRACT temps p e le m le' m' SOURCE f k.
  destruct (CONTRACT temps p e le m le' m' SOURCE) as [b [CHECK CANDIDATE]].
  assert (RUN : exists target_memory,
    exec_stmt (adapter_entry temps) (globalenv p) e le m
      (if b then candidate else source) E0 le' target_memory Out_normal /\
    memory_equivalent m' target_memory).
  { destruct b; [apply CANDIDATE; reflexivity |].
    exists m'; split; [exact SOURCE | apply memory_equivalent_refl]. }
  destruct RUN as [target_memory [RUN EQ]].
  destruct (exec_stmt_steps (adapter_entry temps) p _ _ _ _ _ _ _ _ RUN f k)
    as [next [STEPS EXIT]]. inversion EXIT; subst next.
  exists target_memory; split; [|exact EQ].
  eapply star_trans; [eapply decision_dispatch; exact CHECK | exact STEPS | reflexivity].
Qed.

Lemma tree_statement_label_free guard yes no :
  label_free yes = true -> label_free no = true ->
  label_free (tree_statement guard yes no) = true.
Proof.
  intros YES NO; induction guard; simpl; [destruct accept; assumption |].
  rewrite IHguard1, IHguard2; reflexivity.
Qed.

Definition region_eligible source target : bool :=
  finite_statement source && negb (Nat.eqb (statement_weight source) 0) &&
    label_free target.

Section TRANSFORM.
Variable select : statement -> option statement.
Definition region_version source fallback : statement :=
  match select source with
  | Some target => if region_eligible source target then target else fallback
  | None => fallback
  end.

Fixpoint transform_statement (s : statement) : statement :=
  region_version s
    (match s with
     | Ssequence l r => Ssequence (transform_statement l) (transform_statement r)
     | Sifthenelse a l r => Sifthenelse a (transform_statement l) (transform_statement r)
     | Sloop l r => Sloop (transform_statement l) (transform_statement r)
     | Sswitch a cases => Sswitch a (transform_cases cases)
     | Slabel lbl body => Slabel lbl (transform_statement body)
     | _ => s
     end)
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
| ms_set : forall id a, match_statement (Sset id a) (Sset id a)
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
| ms_switch : forall a cases tcases, match_cases cases tcases ->
    match_statement (Sswitch a cases) (Sswitch a tcases)
| ms_label : forall lbl s ts, match_statement s ts ->
    match_statement (Slabel lbl s) (Slabel lbl ts)
| ms_goto : forall lbl, match_statement (Sgoto lbl) (Sgoto lbl)
| ms_region : forall s ts, finite_statement s = true ->
    0 < statement_weight s -> label_free ts = true -> region_contract s ts ->
    match_statement s ts
with match_cases : labeled_statements -> labeled_statements -> Prop :=
| mc_nil : match_cases LSnil LSnil
| mc_cons : forall tag s rest ts trest, match_statement s ts -> match_cases rest trest ->
    match_cases (LScons tag s rest) (LScons tag ts trest).

Scheme match_statement_ind2 := Induction for match_statement Sort Prop
with match_cases_ind2 := Induction for match_cases Sort Prop.
Combined Scheme match_statement_cases_ind from match_statement_ind2, match_cases_ind2.

Lemma region_version_matches select :
  (forall s ts, select s = Some ts -> region_contract s ts) ->
  forall s fallback, match_statement s fallback ->
    match_statement s (region_version select s fallback).
Proof.
  intros SOUND s fallback DEFAULT. unfold region_version.
  destruct (select s) as [ts|] eqn:SEL; auto.
  destruct (region_eligible s ts) eqn:ELIGIBLE; auto.
  unfold region_eligible in ELIGIBLE.
  apply andb_true_iff in ELIGIBLE as [SOURCE LABEL].
  apply andb_true_iff in SOURCE as [FINITE POSITIVE].
  apply negb_true_iff, Nat.eqb_neq in POSITIVE.
  apply ms_region; [exact FINITE | lia | exact LABEL | eapply SOUND; eauto].
Qed.

Lemma transform_statement_matches : forall select,
  (forall s ts, select s = Some ts -> region_contract s ts) ->
  (forall s, match_statement s (transform_statement select s)) /\
  (forall cases, match_cases cases (transform_cases select cases)).
Proof.
  intros select SOUND. apply ClightGuard.statement_cases_ind; intros;
    cbn [transform_statement transform_cases];
    try (apply region_version_matches; [exact SOUND |]); constructor; auto.
Qed.
