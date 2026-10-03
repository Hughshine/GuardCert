From Stdlib Require Import Bool List Arith Lia.
From compcert.common Require Import AST Events Smallstep.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightRegionRewrite ClightRegionProgress
  ClightTempFrame ClightTempFootprint ClightTempScope CompCertMemoryEquivalence.
Import Ctypes.

(** This host classifies source progress independently of property guards. *)
Module PrivateRegion.
Definition region_eligible (supported : statement -> bool) source target : bool :=
  supported source && label_free target.

Definition projected_region_contract (live : list ident) (source target : statement) : Prop :=
  forall temps p e le tle m le' m',
  statement_scope live source -> temp_agree live le tle ->
  exec_stmt (adapter_entry temps) (globalenv p) e le m source E0 le' m' Out_normal ->
  forall f k, exists tle' target_memory,
    star (adapter_step temps) (globalenv p)
      (State f target k e tle m) E0 (State f Sskip k e tle' target_memory) /\
    temp_agree live le' tle' /\ memory_equivalent m' target_memory.

Section TRANSFORM.
Variable pool : list (ident * type).
Variable supported : statement -> bool.
Variable select : statement -> option statement.
Definition region_version source fallback : statement :=
  match select source with
  | Some target => if region_eligible supported source target then target else fallback
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
    (fn_temps f ++ pool) (transform_statement (fn_body f)).
Definition transform_fundef (fd : Clight.fundef) : Clight.fundef :=
  match fd with
  | Ctypes.Internal f => Ctypes.Internal (transform_function f)
  | Ctypes.External ef args res cc => Ctypes.External ef args res cc
  end.
Definition transform_program (p : Clight.program) : Clight.program :=
  {| prog_defs := List.map (AST.transform_program_globdef transform_fundef) (prog_defs p);
     prog_public := prog_public p; prog_main := prog_main p;
     prog_types := prog_types p; prog_comp_env := prog_comp_env p;
     prog_comp_env_eq := prog_comp_env_eq p |}.
End TRANSFORM.

Section MATCHING.
Variable live : list ident.
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
| ms_region : forall s ts (MODEL : region_progress s),
    label_free ts = true -> projected_region_contract live s ts -> match_statement s ts
with match_cases : labeled_statements -> labeled_statements -> Prop :=
| mc_nil : match_cases LSnil LSnil
| mc_cons : forall tag s rest ts trest, match_statement s ts -> match_cases rest trest ->
    match_cases (LScons tag s rest) (LScons tag ts trest).

Scheme match_statement_ind2 := Induction for match_statement Sort Prop
with match_cases_ind2 := Induction for match_cases Sort Prop.
Combined Scheme match_statement_cases_ind from match_statement_ind2, match_cases_ind2.

Lemma region_version_matches supported select :
  (forall s, supported s = true -> exists MODEL : region_progress s, True) ->
  (forall s ts, select s = Some ts -> projected_region_contract live s ts) ->
  forall s fallback, match_statement s fallback ->
    match_statement s (region_version supported select s fallback).
Proof.
  intros SUPPORTED SOUND s fallback DEFAULT. unfold region_version.
  destruct (select s) as [ts|] eqn:SEL; auto.
  destruct (region_eligible supported s ts) eqn:ELIGIBLE; auto.
  unfold region_eligible in ELIGIBLE.
  apply andb_true_iff in ELIGIBLE as [SOURCE LABEL].
  destruct (SUPPORTED s SOURCE) as [MODEL _].
  eapply (ms_region s ts MODEL); [exact LABEL | eapply SOUND; eauto].
Qed.

Lemma transform_statement_matches : forall supported select,
  (forall s, supported s = true -> exists MODEL : region_progress s, True) ->
  (forall s ts, select s = Some ts -> projected_region_contract live s ts) ->
  (forall s, match_statement s (transform_statement supported select s)) /\
  (forall cases, match_cases cases (transform_cases supported select cases)).
Proof.
  intros supported select SUPPORTED SOUND. apply ClightGuard.statement_cases_ind; intros;
    cbn [transform_statement transform_cases];
    try (apply region_version_matches; [exact SUPPORTED | exact SOUND |]); constructor; auto.
Qed.

End MATCHING.
End PrivateRegion.
