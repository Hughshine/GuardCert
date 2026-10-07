From Stdlib Require Import List Bool PArith.
From compcert.common Require Import AST.
From compcert.lib Require Import Integers.
From compcert.cfrontend Require Import Clight Ctypes.
From Guard Require Import ClightFrontendLoopProtocol ClightSyntaxEquality.
From GuardMemory Require Import GuardMemoryTiledCompiler.
From GuardInterface Require Import ClightSelectedRegion.
Import ListNotations.

(** These are syntax-level occurrence tests. The host and compiler theorems,
    separately, require semantic contracts for the accepted table entries. *)
Definition selection_source := Sset 10%positive (Etempvar 10%positive type_int32s).
Definition selection_table := [(selection_source,Sskip)].
Definition selection_transform := selected_transform_statement [90%positive]
  (fun _=>true) (select_memory_tiled_table selection_table) false.

Example identical_unmarked_occurrence_unchanged :
  selection_transform (Ssequence (Slabel 90%positive selection_source) selection_source) =
    Ssequence (Slabel 90%positive Sskip) selection_source.
Proof. vm_compute; reflexivity. Qed.
Example two_marked_occurrences_selected :
  selected_transform_statement [90%positive;91%positive] (fun _=>true)
    (select_memory_tiled_table selection_table) false
    (Ssequence (Slabel 90%positive selection_source) (Slabel 91%positive selection_source)) =
    Ssequence (Slabel 90%positive Sskip) (Slabel 91%positive Sskip).
Proof. vm_compute; reflexivity. Qed.
Example unlisted_label_does_not_select :
  selection_transform (Slabel 91%positive selection_source) = Slabel 91%positive selection_source.
Proof. vm_compute; reflexivity. Qed.
Example marked_discovery_excludes_identical_unmarked :
  selected_statement_candidates [90%positive] false
    (Ssequence (Slabel 90%positive selection_source) selection_source) = [selection_source].
Proof. vm_compute; reflexivity. Qed.
Example refused_table_keeps_marked_source :
  selected_transform_statement [90%positive] (fun _=>true)
    (select_memory_tiled_table []) false (Slabel 90%positive selection_source) =
    Slabel 90%positive selection_source.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions identical_unmarked_occurrence_unchanged.
Print Assumptions two_marked_occurrences_selected.
Print Assumptions unlisted_label_does_not_select.
Print Assumptions marked_discovery_excludes_identical_unmarked.
Print Assumptions refused_table_keeps_marked_source.
