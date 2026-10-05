From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop ClightCountedProtocol
  ClightStraightLine ClightRectangularStore ClightRectangularGuard ClightRectangularRegion
  RectangularSchedule CompCertStoreSchedule.
From GuardInterface Require Import ClightReadonlyRewrite ClightLoadedBoundSyntax ClightStableLoadBody
  ClightReadonlyCellSwap ClightLoadedRectangleMemory ClightLoadedRectangleAtoms ClightDualRectanglePrefix.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** These witnesses are proof-only. Every generated probe operates on the
    unchanged entry; the witnesses record an actual source prefix instead. *)
Record dual_rect_state d row rows columns i entry := DualRectState {
  drs_rows_range : 0 < Int.signed (loaded_rectangle_word rows entry) <= rectangle_outer_limit d;
  drs_columns_range : 0 < Int.signed (loaded_rectangle_word columns entry) <= rectangle_stride d;
  drs_q : block; drs_qofs : ptrofs; drs_r : block; drs_rofs : ptrofs;
  drs_entry_rows : (entry_temps entry) ! rows = Some (Vptr drs_q drs_qofs);
  drs_entry_columns : (entry_temps entry) ! columns = Some (Vptr drs_r drs_rofs);
  drs_entry_rows_read : Mem.loadv Mint32 (entry_memory entry) (Vptr drs_q drs_qofs) =
    Some (Vint (loaded_rectangle_word rows entry));
  drs_entry_columns_read : Mem.loadv Mint32 (entry_memory entry) (Vptr drs_r drs_rofs) =
    Some (Vint (loaded_rectangle_word columns entry));
  drs_temps : temp_env; drs_memory : mem;
  drs_iterator : drs_temps ! row = Some (Vint (Int.repr i));
  drs_rows : drs_temps ! rows = Some (Vptr drs_q drs_qofs);
  drs_columns : drs_temps ! columns = Some (Vptr drs_r drs_rofs);
  drs_rows_read : Mem.loadv Mint32 drs_memory (Vptr drs_q drs_qofs) =
    Some (Vint (loaded_rectangle_word rows entry));
  drs_columns_read : Mem.loadv Mint32 drs_memory (Vptr drs_r drs_rofs) =
    Some (Vint (loaded_rectangle_word columns entry));
  drs_permissions_back : forall b ofs, writable_word drs_memory b ofs -> writable_word (entry_memory entry) b ofs
}.

Record dual_rect_outer_cursor fe d row rows columns outer i entry := DualRectOuterCursor {
  dro_state : dual_rect_state d row rows columns i entry;
  dro_after : temp_env; dro_final : mem;
  dro_tail : exec_stmt fe (entry_ge entry) (entry_env entry) (drs_temps dro_state) (drs_memory dro_state)
    (dual_rect_source row rows outer) E0 dro_after dro_final Out_normal
}.
Definition dual_rect_outer_invariant fe d row rows columns outer i entry :=
  0 <= i <= rectangle_outer_limit d /\ inhabited (dual_rect_outer_cursor fe d row rows columns outer i entry).

Record dual_rect_inner_cursor fe d row rows column columns body outer i j entry := DualRectInnerCursor {
  dri_state : dual_rect_state d row rows columns i entry;
  dri_iterator : (drs_temps dri_state) ! column = Some (Vint (Int.repr j));
  dri_exit : temp_env; dri_exit_memory : mem; dri_next : temp_env; dri_next_memory : mem;
  dri_after : temp_env; dri_final : mem;
  dri_inner : exec_stmt fe (entry_ge entry) (entry_env entry) (drs_temps dri_state) (drs_memory dri_state)
    (loaded_bound_loop column columns body) E0 dri_exit dri_exit_memory Out_normal;
  dri_increment : exec_stmt fe (entry_ge entry) (entry_env entry) dri_exit dri_exit_memory
    (Ssequence Sskip (counter_increment row)) E0 dri_next dri_next_memory Out_normal;
  dri_tail : exec_stmt fe (entry_ge entry) (entry_env entry) dri_next dri_next_memory
    (dual_rect_source row rows outer) E0 dri_after dri_final Out_normal
}.
Definition dual_rect_inner_invariant fe d row rows column columns body outer i j entry :=
  0 <= i < Int.signed (loaded_rectangle_word rows entry) /\ 0 <= j <= rectangle_stride d /\
  inhabited (dual_rect_inner_cursor fe d row rows column columns body outer i j entry).

Definition dual_rect_state_set d row rows columns i entry (state : dual_rect_state d row rows columns i entry)
  id (value : val) (IR : id <> row) (IQ : id <> rows) (IM : id <> columns) : dual_rect_state d row rows columns i entry.
Proof.
  refine {| drs_rows_range := drs_rows_range state; drs_columns_range := drs_columns_range state;
    drs_q := drs_q state; drs_qofs := drs_qofs state; drs_r := drs_r state; drs_rofs := drs_rofs state;
    drs_entry_rows := drs_entry_rows state; drs_entry_columns := drs_entry_columns state;
    drs_entry_rows_read := drs_entry_rows_read state; drs_entry_columns_read := drs_entry_columns_read state;
    drs_temps := PTree.set id value (drs_temps state); drs_memory := drs_memory state;
    drs_rows_read := drs_rows_read state; drs_columns_read := drs_columns_read state;
    drs_permissions_back := drs_permissions_back state |}.
  - rewrite PTree.gso by congruence; apply drs_iterator.
  - rewrite PTree.gso by congruence; apply drs_rows.
  - rewrite PTree.gso by congruence; apply drs_columns.
Defined.

Definition dual_rect_state_store d (VALID : rectangle_layout_valid d) row rows column columns i j entry
  (state : dual_rect_state d row rows columns i entry) block middle
  (RC : row <> column) (CN : column <> rows) (CM : column <> columns)
  (INDEX : 0 <= i*rectangle_stride d+j < rectangle_extent d)
  (STORE : store_action_run (rectangle_action block (rectangle_stride d) (rect_payload d) (i,j)) (drs_memory state) middle)
  (AQ : Vptr block (loaded_rectangle_offset d i j) <> Vptr (drs_q state) (drs_qofs state))
  (AM : Vptr block (loaded_rectangle_offset d i j) <> Vptr (drs_r state) (drs_rofs state)) :
  dual_rect_state d row rows columns i entry.
Proof.
  refine {| drs_rows_range := drs_rows_range state; drs_columns_range := drs_columns_range state;
    drs_q := drs_q state; drs_qofs := drs_qofs state; drs_r := drs_r state; drs_rofs := drs_rofs state;
    drs_entry_rows := drs_entry_rows state; drs_entry_columns := drs_entry_columns state;
    drs_entry_rows_read := drs_entry_rows_read state; drs_entry_columns_read := drs_entry_columns_read state;
    drs_temps := PTree.set column (Vint (Int.repr (j+1))) (drs_temps state); drs_memory := middle |}.
  - rewrite PTree.gso by congruence; apply drs_iterator.
  - rewrite PTree.gso by congruence; apply drs_rows.
  - rewrite PTree.gso by congruence; apply drs_columns.
  - eapply mint32_load_survives_apart_store;
      [exact (@loaded_rectangle_storev d VALID block i j (drs_memory state) middle INDEX STORE)|apply drs_rows_read|exact AQ].
  - eapply mint32_load_survives_apart_store;
      [exact (@loaded_rectangle_storev d VALID block i j (drs_memory state) middle INDEX STORE)|apply drs_columns_read|exact AM].
  - intros b ofs [ACCESS END]; apply (drs_permissions_back state); split; [|exact END].
    eapply Mem.store_valid_access_2; [exact STORE|exact ACCESS].
Defined.

Definition dual_rect_state_increment d row rows columns i entry (state : dual_rect_state d row rows columns i entry)
  (RN : row <> rows) (RM : row <> columns) : dual_rect_state d row rows columns (i+1) entry.
Proof.
  refine {| drs_rows_range := drs_rows_range state; drs_columns_range := drs_columns_range state;
    drs_q := drs_q state; drs_qofs := drs_qofs state; drs_r := drs_r state; drs_rofs := drs_rofs state;
    drs_entry_rows := drs_entry_rows state; drs_entry_columns := drs_entry_columns state;
    drs_entry_rows_read := drs_entry_rows_read state; drs_entry_columns_read := drs_entry_columns_read state;
    drs_temps := PTree.set row (Vint (Int.repr (i+1))) (drs_temps state); drs_memory := drs_memory state;
    drs_rows_read := drs_rows_read state; drs_columns_read := drs_columns_read state;
    drs_permissions_back := drs_permissions_back state |}.
  - apply PTree.gss.
  - rewrite PTree.gso by congruence; apply drs_rows.
  - rewrite PTree.gso by congruence; apply drs_columns.
Defined.

Print Assumptions dual_rect_state_store.
