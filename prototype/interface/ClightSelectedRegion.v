From Stdlib Require Import List Bool PArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight Ctypes.
From Guard Require Import ClightGuard ClightPrivateRegion ClightRegionProgress.
Import ListNotations PrivateRegion.
Set Implicit Arguments.

(** Selection is occurrence-sensitive. Labels are retained as ordinary source
    control boundaries; only bodies under an explicitly selected label are
    offered to a checked region selector. The selector still has to establish
    the original host's semantic contract and progress obligations. *)
Definition selected_label (chosen : list ident) label :=
  existsb (Pos.eqb label) chosen.

Fixpoint selected_transform_statement (chosen : list ident) (supported : statement -> bool)
    (select : statement -> option statement) (active : bool) (s : statement) : statement :=
  match s with
  | Slabel label body => Slabel label
      (selected_transform_statement chosen supported select
        (active || selected_label chosen label) body)
  | _ =>
    let fallback := match s with
    | Ssequence l r => Ssequence
        (selected_transform_statement chosen supported select active l)
        (selected_transform_statement chosen supported select active r)
    | Sifthenelse a l r => Sifthenelse a
        (selected_transform_statement chosen supported select active l)
        (selected_transform_statement chosen supported select active r)
    | Sloop l r => Sloop
        (selected_transform_statement chosen supported select active l)
        (selected_transform_statement chosen supported select active r)
    | Sswitch a cases => Sswitch a
        (selected_transform_cases chosen supported select active cases)
    | _ => s end in
    if active then region_version supported select s fallback else fallback
  end
with selected_transform_cases (chosen : list ident) (supported : statement -> bool)
    (select : statement -> option statement) (active : bool) (cases : labeled_statements) : labeled_statements :=
  match cases with
  | LSnil => LSnil
  | LScons tag body rest => LScons tag
      (selected_transform_statement chosen supported select active body)
      (selected_transform_cases chosen supported select active rest)
  end.

Definition selected_transform_function chosen pool supported select f :=
  mkfunction (fn_return f) (fn_callconv f) (fn_params f) (fn_vars f)
    (fn_temps f ++ pool)
    (selected_transform_statement chosen supported select false (fn_body f)).
Definition selected_transform_fundef chosen pool supported select fd :=
  match fd with
  | Ctypes.Internal f => Ctypes.Internal (selected_transform_function chosen pool supported select f)
  | Ctypes.External ef args res cc => Ctypes.External ef args res cc end.
Definition selected_transform_program chosen pool supported select (p : Clight.program) :=
  {| prog_defs := map (AST.transform_program_globdef
       (selected_transform_fundef chosen pool supported select)) (prog_defs p);
     prog_public := prog_public p; prog_main := prog_main p;
     prog_types := prog_types p; prog_comp_env := prog_comp_env p;
     prog_comp_env_eq := prog_comp_env_eq p |}.

Lemma selected_transform_matches_active live chosen supported select :
  (forall s, supported s = true -> exists MODEL : region_progress s, True) ->
  (forall s ts, select s = Some ts -> projected_region_contract live s ts) ->
  (forall s active, match_statement live s
    (selected_transform_statement chosen supported select active s)) /\
  (forall cases active, match_cases live cases
    (selected_transform_cases chosen supported select active cases)).
Proof.
  intros SUPPORTED SOUND. apply ClightGuard.statement_cases_ind; intros;
    cbn [selected_transform_statement selected_transform_cases];
    try (destruct active; [apply region_version_matches; [exact SUPPORTED|exact SOUND|]|]);
    constructor; auto.
Qed.
Lemma selected_transform_matches live chosen supported select :
  (forall s, supported s = true -> exists MODEL : region_progress s, True) ->
  (forall s ts, select s = Some ts -> projected_region_contract live s ts) ->
  (forall s, match_statement live s
    (selected_transform_statement chosen supported select false s)) /\
  (forall cases, match_cases live cases
    (selected_transform_cases chosen supported select false cases)).
Proof.
  intros SUPPORTED SOUND.
  destruct (@selected_transform_matches_active live chosen supported select SUPPORTED SOUND) as [STMT CASES].
  split; intro; auto.
Qed.

Fixpoint selected_statement_candidates (chosen : list ident) (active : bool) (s : statement) : list statement :=
  match s with
  | Slabel label body => selected_statement_candidates chosen
      (active || selected_label chosen label) body
  | _ => (if active then [s] else []) ++ match s with
    | Ssequence l r | Sifthenelse _ l r | Sloop l r =>
        selected_statement_candidates chosen active l ++
        selected_statement_candidates chosen active r
    | Sswitch _ cases => selected_case_candidates chosen active cases
    | _ => [] end end
with selected_case_candidates (chosen : list ident) (active : bool) (cases : labeled_statements) : list statement :=
  match cases with
  | LSnil => []
  | LScons _ body rest => selected_statement_candidates chosen active body ++
      selected_case_candidates chosen active rest end.
Definition selected_program_candidates chosen (p : Clight.program) :=
  flat_map (fun definition => match snd definition with
    | Gfun (Ctypes.Internal f) => selected_statement_candidates chosen false (fn_body f)
    | _ => [] end) (Ctypes.prog_defs p).

(** This syntactic predicate states that no selected boundary occurs in the
    subtree. It does not express source safety or optimizer preconditions. *)
Fixpoint contains_selected_label chosen (s : statement) : bool :=
  match s with
  | Slabel label body => selected_label chosen label || contains_selected_label chosen body
  | Ssequence l r | Sifthenelse _ l r | Sloop l r =>
      contains_selected_label chosen l || contains_selected_label chosen r
  | Sswitch _ cases => cases_contain_selected_label chosen cases
  | _ => false end
with cases_contain_selected_label chosen cases : bool :=
  match cases with
  | LSnil => false
  | LScons _ body rest => contains_selected_label chosen body ||
      cases_contain_selected_label chosen rest end.
Lemma unselected_subtrees_unchanged chosen supported select :
  (forall s, contains_selected_label chosen s = false ->
    selected_transform_statement chosen supported select false s = s) /\
  (forall cases, cases_contain_selected_label chosen cases = false ->
    selected_transform_cases chosen supported select false cases = cases).
Proof.
  apply ClightGuard.statement_cases_ind; intros;
    cbn [contains_selected_label cases_contain_selected_label
      selected_transform_statement selected_transform_cases] in *;
    try (apply orb_false_iff in H1 as [LEFT RIGHT]);
    try (apply orb_false_iff in H0 as [LEFT RIGHT]);
    try (rewrite LEFT); f_equal; auto.
Qed.

Print Assumptions selected_transform_matches_active.
Print Assumptions selected_transform_matches.
Print Assumptions unselected_subtrees_unchanged.
