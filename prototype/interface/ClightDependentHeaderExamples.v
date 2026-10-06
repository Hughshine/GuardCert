From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightSameAddress ClightPureExpr CompCertMemoryActions.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightDependentBoundSyntax ClightDependentHeaderObservations
  ClightWordAddressSeparation ClightWordChunkSeparation ClightReadonlyLoadedTreeSynthesis ClightSignedExpressionProgress.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Concrete CompCert memory: an eight-byte pointer at offset 0 refers to
    the signed bound at offset 16. The write at offset 4 overlaps only the
    second half of the pointer cell. These are Rocq execution fixtures. *)
Definition dh_allocated := fst (Mem.alloc Mem.empty 0 32).
Lemma dh_allocated_access chunk offset :
  0 <= offset -> offset+size_chunk chunk <= 32 -> (align_chunk chunk | offset) ->
  Mem.valid_access dh_allocated chunk 1%positive offset Writable.
Proof.
  intros LOW HIGH ALIGN; eapply Mem.valid_access_implies with (p1:=Freeable); [|constructor].
  eapply Mem.valid_access_alloc_same with (m1:=Mem.empty) (lo:=0) (hi:=32);
    [reflexivity|exact LOW|exact HIGH|exact ALIGN].
Qed.
Definition dh_pointer_memory_state :
  {memory | Mem.store Mptr dh_allocated 1%positive 0 (Vptr 1%positive (Ptrofs.repr 16)) = Some memory}.
Proof.
  apply Mem.valid_access_store,dh_allocated_access;
    [lia|change (0+8 <= 32); lia|change (8 | 0); exists 0; reflexivity].
Defined.
Definition dh_pointer_memory := proj1_sig dh_pointer_memory_state.
Lemma concrete_pointer_store :
  Mem.store Mptr dh_allocated 1%positive 0 (Vptr 1%positive (Ptrofs.repr 16)) = Some dh_pointer_memory.
Proof. exact (proj2_sig dh_pointer_memory_state). Qed.
Definition dh_memory_state :
  {memory | Mem.store Mint32 dh_pointer_memory 1%positive 16 (Vint (Int.repr 3)) = Some memory}.
Proof.
  apply Mem.valid_access_store; eapply Mem.store_valid_access_1; [exact concrete_pointer_store|].
  apply dh_allocated_access; [lia|change (16+4 <= 32); lia|exists 4; reflexivity].
Defined.
Definition dh_memory := proj1_sig dh_memory_state.
Lemma concrete_bound_store :
  Mem.store Mint32 dh_pointer_memory 1%positive 16 (Vint (Int.repr 3)) = Some dh_memory.
Proof. exact (proj2_sig dh_memory_state). Qed.
Definition dh_changed_memory_state : {memory | Mem.store Mint32 dh_memory 1%positive 4 (Vint Int.zero) = Some memory}.
Proof.
  apply Mem.valid_access_store; eapply Mem.store_valid_access_1; [exact concrete_bound_store|].
  eapply Mem.store_valid_access_1; [exact concrete_pointer_store|].
  apply dh_allocated_access; [lia|change (4+4 <= 32); lia|exists 1; reflexivity].
Defined.
Definition dh_changed_memory := proj1_sig dh_changed_memory_state.
Definition dh_row := 1%positive.
Definition dh_root := 2%positive.
Definition dh_write := 3%positive.
Definition dh_pointer_cache := 4%positive.
Definition dh_cache := 5%positive.
Definition dh_temps := PTree.set dh_write (Vptr 1%positive (Ptrofs.repr 4))
  (PTree.set dh_root (Vptr 1%positive Ptrofs.zero) (PTree.set dh_row (Vint Int.zero) (PTree.empty val))).

Example concrete_pointer_read :
  Mem.loadv Mptr dh_memory (Vptr 1%positive Ptrofs.zero) = Some (Vptr 1%positive (Ptrofs.repr 16)).
Proof.
  change (Mem.load Mint64 dh_memory 1%positive 0 = Some (Vptr 1%positive (Ptrofs.repr 16))).
  erewrite Mem.load_store_other; [|exact concrete_bound_store|right; left; change (0+8 <= 16); lia].
  exact (@Mem.load_store_same Mptr dh_allocated 1%positive 0 (Vptr 1%positive (Ptrofs.repr 16))
    dh_pointer_memory concrete_pointer_store).
Qed.
Example concrete_bound_read :
  Mem.loadv Mint32 dh_memory (Vptr 1%positive (Ptrofs.repr 16)) = Some (Vint (Int.repr 3)).
Proof.
  change (Mem.load Mint32 dh_memory 1%positive 16 = Some (Vint (Int.repr 3))).
  exact (@Mem.load_store_same Mint32 dh_pointer_memory 1%positive 16 (Vint (Int.repr 3)) dh_memory concrete_bound_store).
Qed.
Example concrete_upper_half_store : Mem.store Mint32 dh_memory 1%positive 4 (Vint Int.zero) = Some dh_changed_memory.
Proof. exact (proj2_sig dh_changed_memory_state). Qed.
Example concrete_upper_half_changes_pointer :
  Mem.loadv Mptr dh_changed_memory (Vptr 1%positive Ptrofs.zero) <> Some (Vptr 1%positive (Ptrofs.repr 16)).
Proof.
  intro READ; change (Mem.load Mptr dh_changed_memory 1%positive 0 = Some (Vptr 1%positive (Ptrofs.repr 16))) in READ.
  destruct (@Mem.load_pointer_store Mint32 dh_memory 1%positive 4 (Vint Int.zero) dh_changed_memory
    Mptr 1%positive 0 1%positive (Ptrofs.repr 16) concrete_upper_half_store READ) as [[VALUE REST]|APART];
    [discriminate|destruct APART as [BAD|[BAD|BAD]]; [congruence|change (0+8 <= 4) in BAD; lia|change (4+4 <= 0) in BAD; lia]].
Qed.

Lemma concrete_word_access offset : 0 <= offset -> offset+4 <= 32 -> (4 | offset) ->
  Mem.valid_access dh_memory Mint32 1%positive offset Writable.
Proof.
  intros LOW HIGH ALIGN.
  eapply Mem.store_valid_access_1; [exact concrete_bound_store|].
  eapply Mem.store_valid_access_1; [exact concrete_pointer_store|].
  eapply Mem.valid_access_implies; [|constructor].
  apply dh_allocated_access; [exact LOW|exact HIGH|exact ALIGN].
Qed.

Lemma concrete_dependent_header ge locals :
  expression_test (dependent_bound_test dh_row dh_root) (Entry ge locals dh_temps dh_memory) true.
Proof.
  change true with (Int.lt Int.zero (Int.repr 3)); eapply dependent_bound_test_eval;
    [reflexivity|reflexivity|exact concrete_pointer_read|exact concrete_bound_read].
Qed.

Theorem concrete_safe_double_capture ge locals fe :
  exists after, exec_stmt fe ge locals dh_temps dh_memory (dependent_header_capture dh_root dh_pointer_cache dh_cache)
    Events.E0 after dh_memory Out_normal /\
    dependent_cached_header dh_root dh_pointer_cache dh_cache (Entry ge locals after dh_memory).
Proof.
  eapply dependent_header_safe_capture; [discriminate|discriminate|discriminate|apply concrete_dependent_header].
Qed.

Theorem upper_half_first_equality_false ge locals :
  expression_test (word_chunk_equal (signed_pointer_temp dh_write) (dependent_pointer_cell_address dh_root))
    (Entry ge locals dh_temps dh_memory) false.
Proof.
  change false with (address_flag 1%positive (Ptrofs.repr 4) 1%positive Ptrofs.zero).
  eapply word_chunk_equality_test; [reflexivity|reflexivity|constructor; reflexivity|
    apply dependent_pointer_cell_address_eval; reflexivity| |].
  - apply valid_word_address; change (Mem.valid_access dh_memory Mint32 1%positive 4 Writable).
    apply concrete_word_access; [lia|lia|exists 1; reflexivity].
  - eapply loaded_address_valid; exact concrete_pointer_read.
Qed.

Theorem upper_half_wide_guard_refuses ge locals :
  decision_run (Entry ge locals dh_temps dh_memory)
    (word_chunk_separation (signed_pointer_temp dh_write) (dependent_pointer_cell_address dh_root) true) false.
Proof.
  unfold word_chunk_separation; eapply run_test with (b:=false); [apply upper_half_first_equality_false|].
  eapply run_test with (b:=true); [|constructor].
  change true with (address_flag 1%positive (Ptrofs.repr 4) 1%positive (Ptrofs.add Ptrofs.zero (Ptrofs.repr 4))).
  eapply word_chunk_equality_test; [reflexivity|reflexivity|constructor; reflexivity| | |].
  - apply word_chunk_second_evaluation; [reflexivity|apply dependent_pointer_cell_address_eval; reflexivity].
  - apply valid_word_address; change (Mem.valid_access dh_memory Mint32 1%positive 4 Writable).
    apply concrete_word_access; [lia|lia|exists 1; reflexivity].
  - eapply wide_second_valid; exact concrete_pointer_read.
Qed.

Theorem upper_half_refusal_skips_tail ge locals tail :
  decision_run (Entry ge locals dh_temps dh_memory)
    (decision_bind (word_chunk_separation (signed_pointer_temp dh_write) (dependent_pointer_cell_address dh_root) true)
      tail (Decision false)) false.
Proof. eapply decision_bind_run; [apply upper_half_wide_guard_refuses|constructor]. Qed.

Example wide_cell_aligned_word_at_8_is_disjoint :
  location_disjoint (MemoryLocation Mint32 1%positive 8) (MemoryLocation Mptr 1%positive 0).
Proof. right; right; change (8 <= 8); lia. Qed.
Example word_at_4_is_not_disjoint :
  ~ location_disjoint (MemoryLocation Mint32 1%positive 4) (MemoryLocation Mptr 1%positive 0).
Proof. change (~ (1%positive <> 1%positive \/ 4+4 <= 0 \/ 0+8 <= 4)); intros [BAD|[BAD|BAD]]; [congruence|lia|lia]. Qed.

Example dependent_header_progress_selected :
  signed_expression_region_progress_supported (dependent_bound_loop dh_row dh_root Sskip) = true.
Proof. vm_compute; reflexivity. Qed.
Example changing_pointer_cell_does_not_require_static_stability :
  signed_expression_region_progress_supported (dependent_bound_loop dh_row dh_root
    (Sassign (dependent_pointer_load dh_root) (signed_pointer_temp dh_pointer_cache))) = true.
Proof. vm_compute; reflexivity. Qed.
Example resetting_source_iterator_refused :
  signed_expression_region_progress_supported (dependent_bound_loop dh_row dh_root
    (Sset dh_row (Econst_int Int.zero type_int32s))) = false.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions concrete_pointer_read.
Print Assumptions concrete_bound_read.
Print Assumptions concrete_upper_half_changes_pointer.
Print Assumptions concrete_dependent_header.
Print Assumptions concrete_safe_double_capture.
Print Assumptions upper_half_first_equality_false.
Print Assumptions upper_half_wide_guard_refuses.
Print Assumptions upper_half_refusal_skips_tail.
Print Assumptions wide_cell_aligned_word_at_8_is_disjoint.
Print Assumptions word_at_4_is_not_disjoint.
Print Assumptions dependent_header_progress_selected.
Print Assumptions changing_pointer_cell_does_not_require_static_stability.
Print Assumptions resetting_source_iterator_refused.
