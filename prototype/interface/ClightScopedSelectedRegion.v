From Stdlib Require Import List Bool.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight Ctypes.
From Guard Require Import ClightGuard ClightRegionProgress ClightScopedPrivateRegion.
From GuardInterface Require Import ClightSelectedRegion.
Import ListNotations ScopedPrivateRegion.
Set Implicit Arguments.

(** Occurrence-sensitive selection reuses the existing annotated AST pass;
    only its semantic matching contract is scoped to actual program facts. *)
Module ScopedSelectedRegion.
Definition transform_statement chosen supported select source :=
  selected_transform_statement chosen supported select false source.
Definition transform_cases chosen supported select cases :=
  selected_transform_cases chosen supported select false cases.
Definition transform_function := selected_transform_function.
Definition transform_fundef := selected_transform_fundef.
Definition transform_program := selected_transform_program.

Lemma transform_matches_active live reference globals chosen supported select :
  (forall source, supported source=true -> exists MODEL : region_progress source, True) ->
  (forall source target, select source=Some target -> projected_region_contract live reference globals source target) ->
  (forall source active, match_statement live reference globals source
    (selected_transform_statement chosen supported select active source)) /\
  (forall cases active, match_cases live reference globals cases
    (selected_transform_cases chosen supported select active cases)).
Proof.
  intros SUPPORTED SELECT; apply ClightGuard.statement_cases_ind; intros;
    cbn [selected_transform_statement selected_transform_cases];
    try (destruct active; [apply ScopedPrivateRegion.region_version_matches; [exact SUPPORTED|exact SELECT|]|]);
    constructor; auto.
Qed.
Lemma transform_statement_matches live reference globals chosen supported select :
  (forall source, supported source=true -> exists MODEL : region_progress source, True) ->
  (forall source target, select source=Some target -> projected_region_contract live reference globals source target) ->
  (forall source, match_statement live reference globals source (transform_statement chosen supported select source)) /\
  (forall cases, match_cases live reference globals cases (transform_cases chosen supported select cases)).
Proof.
  intros SUPPORTED SELECT; destruct (@transform_matches_active live reference globals chosen supported select SUPPORTED SELECT)
    as [STATEMENTS CASES]; split.
  - intro source; exact (STATEMENTS source false).
  - intro cases; exact (CASES cases false).
Qed.
End ScopedSelectedRegion.
Print Assumptions ScopedSelectedRegion.transform_statement_matches.
