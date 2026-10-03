From Stdlib Require Import List Bool.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightPureExpr.
From GuardMemory Require Import GuardMemoryRuntime GuardMemorySequentialCondition GuardMemoryFiniteAliasCondition
  GuardMemoryActivatedAliasCondition GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerRegionGuard
  GuardMemoryRecursiveSource GuardMemoryRecursiveGuard GuardMemoryMultiPointerCells GuardMemoryMultiPointerFootprint.
Import ListNotations.
Set Implicit Arguments.

Fixpoint memory_compact_alias_tail code first items := match items with
  | [] => Sskip
  | item::rest => Ssequence (tree_statement (memory_activated_pair_tree code first item) Sskip Sbreak)
      (memory_compact_alias_tail code first rest) end.
Fixpoint memory_compact_alias_statement code items := match items with
  | [] => Sskip
  | item::rest => Ssequence (memory_compact_alias_tail code item rest) (memory_compact_alias_statement code rest) end.
Lemma memory_compact_alias_tail_execution fe code locations s active first items :
  memory_activated_item_domain code locations s active first ->
  Forall (memory_activated_item_domain code locations s active) items ->
  memory_check_statement_execution fe s (memory_compact_alias_tail code first items)
    (forallb (memory_activated_pair_check locations active first) items).
Proof.
  intros FIRST ITEMS; induction ITEMS as [|item items ITEM ITEMS IH]; cbn.
  - destruct s; constructor.
  - apply memory_sequence_check_statement.
    + apply memory_decision_check_statement.
      apply (proj2 (@memory_activated_pair_exact code locations s active first item
        (proj1 FIRST) (proj1 ITEM) (proj2 FIRST) (proj2 ITEM)
        (memory_activated_pair_check locations active first item))); reflexivity.
    + intro ACCEPT; exact IH.
Qed.
Theorem memory_compact_alias_statement_execution fe code locations s active items :
  Forall (memory_activated_item_domain code locations s active) items ->
  memory_check_statement_execution fe s (memory_compact_alias_statement code items)
    (memory_activated_alias_check locations active items).
Proof.
  intro ITEMS; induction ITEMS as [|item items ITEM ITEMS IH]; cbn.
  - destruct s; constructor.
  - apply memory_sequence_check_statement; [apply memory_compact_alias_tail_execution; assumption|intro ACCEPT; exact IH].
Qed.
Definition memory_multi_pointer_region_guard_statement source (package : memory_multi_pointer_region_package source) :=
  Ssequence (tree_statement (memory_recursive_guard_tree (multi_pointer_region_limit package) [] (multi_pointer_region_nest package)) Sskip Sbreak)
    (memory_compact_alias_statement memory_multi_pointer_cell_code (memory_multi_pointer_region_items package)).
Theorem memory_multi_pointer_region_guard_statement_execution source (package : memory_multi_pointer_region_package source) fe s :
  memory_multi_pointer_region_guard_domain package s ->
  memory_check_statement_execution fe s (memory_multi_pointer_region_guard_statement package)
    (memory_multi_pointer_region_guard_accept package s).
Proof.
  intros [DOMAIN ITEMS]; unfold memory_multi_pointer_region_guard_statement,memory_multi_pointer_region_guard_accept.
  apply memory_sequence_check_statement.
  - apply memory_decision_check_statement.
    apply (proj2 (@memory_recursive_guard_exact (multi_pointer_region_limit package) []
      (multi_pointer_region_nest package) s DOMAIN
      (memory_recursive_guard_accept (multi_pointer_region_limit package) [] (multi_pointer_region_nest package) s))); reflexivity.
  - intro ACCEPT; unfold memory_multi_pointer_region_alias_check;
      apply memory_compact_alias_statement_execution; apply ITEMS; exact ACCEPT.
Qed.
Print Assumptions memory_compact_alias_statement_execution.
Print Assumptions memory_multi_pointer_region_guard_statement_execution.
