(** Real allocated memory, complete original loops and the complete guard.
    The second RHS reads a value produced by the first actual store. *)
From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes Cop ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame ClightTempFootprint
  ClightLoopSyntax ClightCountedLoop ClightCountedProtocol ClightFrontendLoopProtocol ClightPureExpr.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightLoadedOffsetHeader
  ClightExpressionHeaderCapture ClightSignedExpressionProgress ClightStrictLoopProgress ClightDualLoadedUnitSyntax
  ClightWordStoreSequence ClightWordStoreSequenceFactory ClightWordStoreSequenceLoaded
  ClightWordStoreSequenceScan ClightWordStoreSequenceGuard ClightWordStoreSequenceExample
  ClightDirectWordObservation ClightAffineJointObservation.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition sequence_scan_rename id := if peq id 1%positive then 20%positive else id.
Definition sequence_scan_stable := [2;9;10;11]%positive.
Definition sequence_scan_live := [1;2;9;10;11]%positive.
Definition sequence_scan_public := [1;9;10;11]%positive.
Definition sequence_scan_source delta := loaded_offset_loop 1%positive 11%positive Int.zero (sequence_demo_body delta).
Definition sequence_scan_code delta := word_store_loaded_guard_code
  1%positive 2%positive 11%positive Int.zero 20%positive 21%positive 100%positive
  sequence_scan_rename (sequence_demo_sites delta).
Definition sequence_scan_rewrite delta := word_store_loaded_rewrite_code
  1%positive 2%positive 11%positive Int.zero 20%positive 21%positive 100%positive
  sequence_scan_rename (sequence_demo_sites delta) (sequence_demo_body delta).
Definition sequence_scan_result delta entry := word_store_loaded_guard_result
  1%positive 2%positive 20%positive sequence_scan_rename (sequence_demo_sites delta) 11%positive entry.
Definition sequence_scan_checked delta : checked_word_store_body (sequence_demo_body delta).
Proof.
  refine (@CheckedWordStoreBody (sequence_demo_body delta) (sequence_demo_sites delta)
    eq_refl (sequence_demo_words delta) eq_refl eq_refl _).
  constructor; constructor.
Defined.

Lemma sequence_scan_first_test ge locals temps memory raw counter :
  temps!1%positive = Some (Vint counter) -> temps!11%positive = Some (Vptr 1%positive Ptrofs.zero) ->
  Mem.loadv Mint32 memory (Vptr 1%positive Ptrofs.zero) = Some (Vint raw) ->
  expression_test (signed_expression_test 1%positive (signed_load_offset 11%positive Int.zero))
    (Entry ge locals temps memory) (Int.lt counter raw).
Proof.
  intros ROW POINTER LOAD; rewrite <- (Int.add_zero raw) at 1.
  eapply signed_expression_test_eval; [reflexivity|exact ROW|].
  eapply signed_load_offset_eval; eassumption.
Qed.

Theorem sequence_scan_original_accepting_loop fe ge locals :
  exec_stmt fe ge locals (sequence_demo_temps 8) sequence_demo_memory
    (sequence_scan_source (Int.repr 3)) E0
    (PTree.set 1%positive (Vint Int.one) (sequence_demo_temps 8)) sequence_demo_final Out_normal.
Proof.
  unfold sequence_scan_source,loaded_offset_loop;
    eapply strict_iteration_encode with (body_temps:=sequence_demo_temps 8) (body_memory:=sequence_demo_final).
  - change true with (Int.lt Int.zero Int.one); apply sequence_scan_first_test; [reflexivity|reflexivity|].
    apply sequence_demo_loadv; [cbn; tauto|apply sequence_demo_memory_header].
  - exists Int.zero; split; [reflexivity|change (0 < 2147483647); lia].
  - apply sequence_demo_actual_source.
  - change (exec_stmt fe ge locals (PTree.set 1%positive (Vint Int.one) (sequence_demo_temps 8)) sequence_demo_final
      (strict_frontend_loop 1%positive (signed_expression_test 1%positive (signed_load_offset 11%positive Int.zero))
        (sequence_demo_body (Int.repr 3))) E0
      (PTree.set 1%positive (Vint Int.one) (sequence_demo_temps 8)) sequence_demo_final Out_normal).
    apply strict_zero_trip_encode; change false with (Int.lt Int.one Int.one).
    apply sequence_scan_first_test; [apply PTree.gss|reflexivity|].
    apply sequence_demo_loadv; [cbn; tauto|exact (proj1 sequence_demo_header_and_arrays)].
Qed.

Theorem sequence_scan_original_alias_loop fe ge locals :
  exec_stmt fe ge locals (sequence_demo_temps 0) sequence_demo_alias_memory
    (sequence_scan_source (Int.repr (-2))) E0
    (PTree.set 1%positive (Vint Int.one) (sequence_demo_temps 0)) sequence_demo_alias_final Out_normal.
Proof.
  unfold sequence_scan_source,loaded_offset_loop;
    eapply strict_iteration_encode with (body_temps:=sequence_demo_temps 0) (body_memory:=sequence_demo_alias_final).
  - change true with (Int.lt Int.zero (Int.repr 2)); apply sequence_scan_first_test; [reflexivity|reflexivity|].
    apply sequence_demo_loadv; [cbn; tauto|apply sequence_demo_alias_memory_header].
  - exists Int.zero; split; [reflexivity|change (0 < 2147483647); lia].
  - apply sequence_demo_alias_actual_source.
  - change (exec_stmt fe ge locals (PTree.set 1%positive (Vint Int.one) (sequence_demo_temps 0)) sequence_demo_alias_final
      (strict_frontend_loop 1%positive (signed_expression_test 1%positive (signed_load_offset 11%positive Int.zero))
        (sequence_demo_body (Int.repr (-2)))) E0
      (PTree.set 1%positive (Vint Int.one) (sequence_demo_temps 0)) sequence_demo_alias_final Out_normal).
    apply strict_zero_trip_encode; change false with (Int.lt Int.one (Int.repr (-2))).
    apply sequence_scan_first_test; [apply PTree.gss|reflexivity|].
    apply sequence_demo_loadv; [cbn; tauto|exact (proj2 sequence_demo_alias_changes_loaded_header)].
Qed.

Lemma sequence_scan_instance fe ge locals temps memory source_after final delta :
  exec_stmt fe ge locals temps memory (sequence_scan_source delta) E0 source_after final Out_normal ->
  exists upper prepared_after after,
    let captured := Entry ge locals (PTree.set 2%positive (Vint upper) temps) memory in
    exec_stmt fe ge locals (entry_temps captured) memory (sequence_scan_source delta) E0 prepared_after final Out_normal /\
    loaded_offset_cached_header 11%positive Int.zero 2%positive captured /\
    temp_agree sequence_scan_public source_after prepared_after /\
    exec_stmt fe ge locals temps memory (sequence_scan_code delta) E0 after memory Out_normal /\
    temp_agree sequence_scan_live (entry_temps captured) after /\
    temp_agree sequence_scan_public temps after /\
    after!100%positive = Some (memory_boolean_word (sequence_scan_result delta captured)) /\
    (sequence_scan_result delta captured = true -> exists cached_after,
      exec_stmt fe ge locals after memory (frontend_counted_loop 1%positive 2%positive (sequence_demo_body delta))
        E0 cached_after final Out_normal /\ temp_agree sequence_scan_public source_after cached_after).
Proof.
  intro SOURCE; eapply (@word_store_loaded_guard_execution fe 1%positive 2%positive 11%positive
    20%positive 21%positive 100%positive Int.zero (sequence_demo_body delta) (sequence_scan_checked delta)
    sequence_scan_stable sequence_scan_live sequence_scan_public sequence_scan_rename).
  all: try exact SOURCE; try reflexivity.
  all: cbn [sequence_scan_stable sequence_scan_live sequence_scan_public sequence_scan_rename
    sequence_scan_checked wsbody_sites sequence_demo_sites sequence_demo_body hd tl word_store_site_code
    wss_index wss_pointer direct_word_store direct_word_address sequence_demo_zero
    sequence_demo_rhs loaded_offset_loop strict_frontend_loop signed_expression_test signed_load_offset
    signed_load signed_pointer_temp frontend_counted_loop counter_condition counter_increment
    statement_scope expression_scope statement_temps expression_temps incl List.In].
  all: try (intros id [<-|[<-|[<-|[<-|BAD]]]]; [reflexivity|reflexivity|reflexivity|reflexivity|contradiction]).
  all: try (intros site [<-|[<-|BAD]]; [cbn; tauto|cbn; tauto|contradiction]).
  all: try (intros site [<-|[<-|BAD]];
    [unfold expression_scope,incl; cbn; tauto|unfold expression_scope,incl; cbn; tauto|contradiction]).
  all: unfold incl,statement_scope,expression_scope,sequence_scan_stable,sequence_scan_live,sequence_scan_public;
    cbn [frontend_counted_loop counter_condition counter_increment statement_temps expression_temps
      sequence_demo_body sequence_demo_sites hd tl word_store_site_code direct_word_store direct_word_address
      sequence_demo_rhs sequence_demo_zero wss_pointer wss_index wss_rhs List.In]; try (intuition congruence).
  all: unfold incl; cbn; intuition congruence.
Qed.

Lemma sequence_scan_snapshot_unique ge locals temps memory upper raw :
  temps!11%positive = Some (Vptr 1%positive Ptrofs.zero) ->
  Mem.loadv Mint32 memory (Vptr 1%positive Ptrofs.zero) = Some (Vint raw) ->
  loaded_offset_cached_header 11%positive Int.zero 2%positive
    (Entry ge locals (PTree.set 2%positive (Vint upper) temps) memory) -> upper = raw.
Proof.
  intros POINTER READ [block [offset [loaded [PTR [LOAD CACHE]]]]].
  cbn [entry_temps entry_memory] in PTR,LOAD,CACHE; rewrite PTree.gso in PTR by discriminate.
  rewrite POINTER in PTR; inversion PTR; subst block offset.
  rewrite READ in LOAD; inversion LOAD; subst loaded.
  rewrite PTree.gss,Int.add_zero in CACHE; congruence.
Qed.

Lemma sequence_scan_accept_result ge locals :
  sequence_scan_result (Int.repr 3)
    (Entry ge locals (PTree.set 2%positive (Vint Int.one) (sequence_demo_temps 8)) sequence_demo_memory) = true.
Proof.
  unfold sequence_scan_result,word_store_loaded_guard_result,word_store_loaded_scan_result,
    word_store_loaded_point_result,word_store_loaded_observers.
  change ((if true then memory_boolean_scan_result
    (fun index=>word_store_sequence_flag sequence_scan_rename (sequence_demo_sites (Int.repr 3))
      (match Mem.loadv Mint32 sequence_demo_memory (Vptr 1%positive Ptrofs.zero) with
       | Some value=>[ClightWordObserver (signed_pointer_temp 11%positive) 1%positive Ptrofs.zero value]
       | None=>[] end)
      (word_store_loaded_entry 20%positive index
        (Entry ge locals (PTree.set 2%positive (Vint Int.one) (sequence_demo_temps 8)) sequence_demo_memory))) 0 1
    else false) = true).
  assert (HEADER : Mem.loadv Mint32 sequence_demo_memory (Vptr 1%positive Ptrofs.zero) = Some (Vint Int.one)).
  { apply sequence_demo_loadv; [cbn; tauto|apply sequence_demo_memory_header]. }
  rewrite HEADER; reflexivity.
Qed.
Lemma sequence_scan_alias_result ge locals :
  sequence_scan_result (Int.repr (-2))
    (Entry ge locals (PTree.set 2%positive (Vint (Int.repr 2)) (sequence_demo_temps 0)) sequence_demo_alias_memory) = false.
Proof.
  unfold sequence_scan_result,word_store_loaded_guard_result,word_store_loaded_scan_result,
    word_store_loaded_point_result,word_store_loaded_observers.
  change ((if true then memory_boolean_scan_result
    (fun index=>word_store_sequence_flag sequence_scan_rename (sequence_demo_sites (Int.repr (-2)))
      (match Mem.loadv Mint32 sequence_demo_alias_memory (Vptr 1%positive Ptrofs.zero) with
       | Some value=>[ClightWordObserver (signed_pointer_temp 11%positive) 1%positive Ptrofs.zero value]
       | None=>[] end)
      (word_store_loaded_entry 20%positive index
        (Entry ge locals (PTree.set 2%positive (Vint (Int.repr 2)) (sequence_demo_temps 0)) sequence_demo_alias_memory))) 0 2
    else false) = false).
  assert (HEADER : Mem.loadv Mint32 sequence_demo_alias_memory (Vptr 1%positive Ptrofs.zero) = Some (Vint (Int.repr 2))).
  { apply sequence_demo_loadv; [cbn; tauto|apply sequence_demo_alias_memory_header]. }
  rewrite HEADER; reflexivity.
Qed.

Theorem sequence_scan_complete_guard_accepts fe ge locals :
  exists after cached_after,
    exec_stmt fe ge locals (sequence_demo_temps 8) sequence_demo_memory (sequence_scan_code (Int.repr 3))
      E0 after sequence_demo_memory Out_normal /\ after!100%positive = Some (Vint Int.one) /\
    exec_stmt fe ge locals after sequence_demo_memory
      (frontend_counted_loop 1%positive 2%positive (sequence_demo_body (Int.repr 3)))
      E0 cached_after sequence_demo_final Out_normal /\
    temp_agree sequence_scan_public (PTree.set 1%positive (Vint Int.one) (sequence_demo_temps 8)) cached_after.
Proof.
  destruct (sequence_scan_instance (sequence_scan_original_accepting_loop fe ge locals))
    as [upper [prepared_after [after [PREPARED [READY [PUBLIC [GUARD [FRAME [INITIAL [FLAG CACHED]]]]]]]]]].
  assert (UPPER : upper = Int.one).
  { eapply sequence_scan_snapshot_unique with (temps:=sequence_demo_temps 8); [reflexivity| |exact READY].
    apply sequence_demo_loadv; [cbn; tauto|apply sequence_demo_memory_header]. }
  subst upper; rewrite sequence_scan_accept_result in FLAG,CACHED.
  destruct (CACHED eq_refl) as [cached_after [RUN SAME]].
  exists after,cached_after; repeat split; assumption.
Qed.
Theorem sequence_scan_complete_guard_refuses fe ge locals :
  exists after,
    exec_stmt fe ge locals (sequence_demo_temps 0) sequence_demo_alias_memory
      (sequence_scan_code (Int.repr (-2))) E0 after sequence_demo_alias_memory Out_normal /\
    after!100%positive = Some (Vint Int.zero) /\
    temp_agree sequence_scan_public (sequence_demo_temps 0) after.
Proof.
  destruct (sequence_scan_instance (sequence_scan_original_alias_loop fe ge locals))
    as [upper [prepared_after [after [PREPARED [READY [PUBLIC [GUARD [FRAME [INITIAL [FLAG CACHED]]]]]]]]]].
  assert (UPPER : upper = Int.repr 2).
  { eapply sequence_scan_snapshot_unique with (temps:=sequence_demo_temps 0); [reflexivity| |exact READY].
    apply sequence_demo_loadv; [cbn; tauto|apply sequence_demo_alias_memory_header]. }
  subst upper; rewrite sequence_scan_alias_result in FLAG.
  exists after; repeat split; assumption.
Qed.

Theorem sequence_scan_rewrite_instance fe ge locals temps memory source_after final delta :
  exec_stmt fe ge locals temps memory (sequence_scan_source delta) E0 source_after final Out_normal ->
  exists after, exec_stmt fe ge locals temps memory (sequence_scan_rewrite delta) E0 after final Out_normal /\
    temp_agree sequence_scan_public source_after after.
Proof.
  intro SOURCE; eapply (@word_store_loaded_rewrite_execution fe 1%positive 2%positive 11%positive
    20%positive 21%positive 100%positive Int.zero (sequence_demo_body delta) (sequence_scan_checked delta)
    sequence_scan_stable sequence_scan_live sequence_scan_public sequence_scan_rename).
  all: try exact SOURCE; try reflexivity.
  all: cbn [sequence_scan_stable sequence_scan_live sequence_scan_public sequence_scan_rename
    sequence_scan_checked wsbody_sites sequence_demo_sites sequence_demo_body hd tl word_store_site_code
    wss_index wss_pointer direct_word_store direct_word_address sequence_demo_zero
    sequence_demo_rhs loaded_offset_loop strict_frontend_loop signed_expression_test signed_load_offset
    signed_load signed_pointer_temp frontend_counted_loop counter_condition counter_increment
    statement_scope expression_scope statement_temps expression_temps incl List.In].
  all: try (intros id [<-|[<-|[<-|[<-|BAD]]]]; [reflexivity|reflexivity|reflexivity|reflexivity|contradiction]).
  all: try (intros site [<-|[<-|BAD]]; [cbn; tauto|cbn; tauto|contradiction]).
  all: try (intros site [<-|[<-|BAD]];
    [unfold expression_scope,incl; cbn; tauto|unfold expression_scope,incl; cbn; tauto|contradiction]).
  all: unfold incl,statement_scope,expression_scope,sequence_scan_stable,sequence_scan_live,sequence_scan_public;
    cbn [frontend_counted_loop counter_condition counter_increment statement_temps expression_temps
      sequence_demo_body sequence_demo_sites hd tl word_store_site_code direct_word_store direct_word_address
      sequence_demo_rhs sequence_demo_zero wss_pointer wss_index wss_rhs List.In]; try (intuition congruence).
  all: unfold incl; cbn; intuition congruence.
Qed.
Theorem sequence_scan_accepting_rewrite fe ge locals :
  exists after, exec_stmt fe ge locals (sequence_demo_temps 8) sequence_demo_memory
    (sequence_scan_rewrite (Int.repr 3)) E0 after sequence_demo_final Out_normal /\
    temp_agree sequence_scan_public (PTree.set 1%positive (Vint Int.one) (sequence_demo_temps 8)) after.
Proof. apply sequence_scan_rewrite_instance; apply sequence_scan_original_accepting_loop. Qed.
Theorem sequence_scan_alias_fallback_rewrite fe ge locals :
  exists after, exec_stmt fe ge locals (sequence_demo_temps 0) sequence_demo_alias_memory
    (sequence_scan_rewrite (Int.repr (-2))) E0 after sequence_demo_alias_final Out_normal /\
    temp_agree sequence_scan_public (PTree.set 1%positive (Vint Int.one) (sequence_demo_temps 0)) after.
Proof. apply sequence_scan_rewrite_instance; apply sequence_scan_original_alias_loop. Qed.

Definition sequence_scan_empty_memory := sequence_demo_write sequence_demo_alloc 0 Int.zero.
Definition sequence_scan_empty_temps := PTree.set 11%positive (Vptr 1%positive Ptrofs.zero)
  (PTree.set 1%positive (Vint Int.zero) (PTree.empty val)).
Lemma sequence_scan_empty_header :
  Mem.loadv Mint32 sequence_scan_empty_memory (Vptr 1%positive Ptrofs.zero) = Some (Vint Int.zero).
Proof.
  apply sequence_demo_loadv; [cbn; tauto|].
  apply sequence_demo_write_same; [apply sequence_demo_alloc_cells|cbn; tauto].
Qed.
Theorem sequence_scan_empty_original fe ge locals delta :
  exec_stmt fe ge locals sequence_scan_empty_temps sequence_scan_empty_memory (sequence_scan_source delta)
    E0 sequence_scan_empty_temps sequence_scan_empty_memory Out_normal.
Proof.
  apply strict_zero_trip_encode; change false with (Int.lt Int.zero Int.zero).
  apply sequence_scan_first_test; [reflexivity|reflexivity|exact sequence_scan_empty_header].
Qed.
Lemma sequence_scan_empty_result ge locals delta :
  sequence_scan_result delta (Entry ge locals
    (PTree.set 2%positive (Vint Int.zero) sequence_scan_empty_temps) sequence_scan_empty_memory) = true.
Proof.
  unfold sequence_scan_result,word_store_loaded_guard_result,word_store_loaded_scan_result.
  change (true = true); reflexivity.
Qed.
Theorem sequence_scan_empty_guard_accepts fe ge locals delta :
  sequence_scan_empty_temps!9%positive = None /\ sequence_scan_empty_temps!10%positive = None /\
  exists after cached_after,
    exec_stmt fe ge locals sequence_scan_empty_temps sequence_scan_empty_memory (sequence_scan_code delta)
      E0 after sequence_scan_empty_memory Out_normal /\ after!100%positive = Some (Vint Int.one) /\
    exec_stmt fe ge locals after sequence_scan_empty_memory
      (frontend_counted_loop 1%positive 2%positive (sequence_demo_body delta))
      E0 cached_after sequence_scan_empty_memory Out_normal /\
    temp_agree sequence_scan_public sequence_scan_empty_temps cached_after.
Proof.
  split; [reflexivity|split; [reflexivity|]].
  destruct (sequence_scan_instance (sequence_scan_empty_original fe ge locals delta))
    as [upper [prepared_after [after [PREPARED [READY [PUBLIC [GUARD [FRAME [INITIAL [FLAG CACHED]]]]]]]]]].
  assert (UPPER : upper = Int.zero).
  { eapply sequence_scan_snapshot_unique with (temps:=sequence_scan_empty_temps);
      [reflexivity|exact sequence_scan_empty_header|exact READY]. }
  subst upper; rewrite sequence_scan_empty_result in FLAG,CACHED.
  destruct (CACHED eq_refl) as [cached_after [RUN SAME]].
  exists after,cached_after; repeat split; assumption.
Qed.

Print Assumptions sequence_scan_checked.
Print Assumptions sequence_scan_first_test.
Print Assumptions sequence_scan_original_accepting_loop.
Print Assumptions sequence_scan_original_alias_loop.
Print Assumptions sequence_scan_instance.
Print Assumptions sequence_scan_snapshot_unique.
Print Assumptions sequence_scan_accept_result.
Print Assumptions sequence_scan_alias_result.
Print Assumptions sequence_scan_complete_guard_accepts.
Print Assumptions sequence_scan_complete_guard_refuses.
Print Assumptions sequence_scan_rewrite_instance.
Print Assumptions sequence_scan_accepting_rewrite.
Print Assumptions sequence_scan_alias_fallback_rewrite.
Print Assumptions sequence_scan_empty_header.
Print Assumptions sequence_scan_empty_original.
Print Assumptions sequence_scan_empty_result.
Print Assumptions sequence_scan_empty_guard_accepts.
