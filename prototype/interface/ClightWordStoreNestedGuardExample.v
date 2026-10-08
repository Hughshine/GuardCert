(** Full guards and rewrites in allocated memory, including an empty outer
    loop with undefined child pointer/cache and undefined array pointers. *)
From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame ClightTempFootprint
  ClightLoopSyntax ClightCountedLoop ClightCountedProtocol ClightFrontendLoopProtocol ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightLoadedOffsetHeader
  ClightExpressionHeaderCapture ClightSignedExpressionProgress ClightStrictLoopProgress ClightDualLoadedUnitSyntax
  ClightNestedExpressionCapture ClightNestedExpressionTransport ClightNestedLoadedOffset ClightDirectWordObservation
  ClightWordStoreSequence ClightWordStoreSequenceFactory ClightWordStoreSequenceGuard
  ClightWordStoreSequenceExample ClightWordStoreSequenceScanExample ClightWordStoreNestedScanExample
  ClightWordStoreNestedGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition nested_guard_demo_public := [1;3;9;10;11;12]%positive.
Definition nested_guard_demo_code delta := word_store_nested_guard_code
  1%positive 2%positive 11%positive Int.zero 3%positive 4%positive 12%positive Int.zero
  20%positive 21%positive 22%positive 23%positive 100%positive nested_scan_demo_rename(sequence_demo_sites delta).
Definition nested_guard_demo_rewrite delta := word_store_nested_rewrite_code
  1%positive 2%positive 11%positive Int.zero 3%positive 4%positive 12%positive Int.zero
  20%positive 21%positive 22%positive 23%positive 100%positive nested_scan_demo_rename(sequence_demo_sites delta)(sequence_demo_body delta).

Lemma nested_guard_demo_set_cached fe ge locals temps memory id expr word :
  temps!id=Some(Vint word) -> eval_expr ge locals temps memory expr(Vint word) ->
  exec_stmt fe ge locals temps memory(Sset id expr) E0 temps memory Out_normal.
Proof.
  intros WORD EVAL; assert(RUN : exec_stmt fe ge locals temps memory(Sset id expr)
    E0(PTree.set id(Vint word) temps) memory Out_normal) by (constructor; exact EVAL).
  rewrite PTree.gsident in RUN by exact WORD; exact RUN.
Qed.

Lemma nested_guard_demo_capture fe ge locals child_offset child_word memory :
  Mem.loadv Mint32 memory(Vptr 1%positive Ptrofs.zero)=Some(Vint Int.one) ->
  Mem.loadv Mint32 memory(Vptr 1%positive(Ptrofs.repr child_offset))=Some(Vint child_word) ->
  exec_stmt fe ge locals(nested_scan_demo_temps child_offset child_word) memory
    (nested_expression_capture 1%positive 2%positive(signed_load_offset 11%positive Int.zero)
      4%positive(signed_load_offset 12%positive Int.zero))
    E0(nested_scan_demo_temps child_offset child_word) memory Out_normal.
Proof.
  intros ROOT CHILD; unfold nested_expression_capture; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0).
  - apply nested_guard_demo_set_cached with(word:=Int.one); [reflexivity|].
    replace(Vint Int.one) with(Vint(Int.add Int.one Int.zero)) by (rewrite Int.add_zero; reflexivity).
    eapply signed_load_offset_eval; [reflexivity|exact ROOT].
  - eapply word_store_if_test_execution with(accepted:=true).
    + change true with(Int.lt Int.zero Int.one); eapply signed_expression_test_eval; [reflexivity|reflexivity|constructor; reflexivity].
    + apply nested_guard_demo_set_cached with(word:=child_word); [reflexivity|].
      replace(Vint child_word) with(Vint(Int.add child_word Int.zero)) by (rewrite Int.add_zero; reflexivity).
      eapply signed_load_offset_eval; [reflexivity|exact CHILD].
Qed.

Lemma nested_guard_demo_controls fe ge locals child_offset child_word memory delta after :
  negb(Int.lt child_word Int.zero)=true ->
  exec_stmt fe ge locals(nested_scan_demo_temps child_offset child_word) memory(nested_scan_demo_code delta)
    E0 after memory Out_normal ->
  exec_stmt fe ge locals(nested_scan_demo_temps child_offset child_word) memory
    (word_store_nested_controls 1%positive 2%positive 4%positive 20%positive 21%positive 22%positive 23%positive
      100%positive nested_scan_demo_rename(sequence_demo_sites delta) 11%positive 12%positive)
    E0 after memory Out_normal.
Proof.
  intros NONNEGATIVE SCAN; unfold word_store_nested_controls.
  eapply word_store_if_test_execution with(accepted:=true).
  - change true with(Int.eq Int.zero Int.zero); apply word_store_zero_test_execution; reflexivity.
  - eapply word_store_if_test_execution with(accepted:=true).
    + change true with(negb(Int.lt Int.one Int.zero)); apply word_store_nonnegative_test_execution; reflexivity.
    + eapply word_store_if_test_execution with(accepted:=true).
      * change true with(Int.lt Int.zero Int.one); apply word_store_positive_test_execution; reflexivity.
      * eapply word_store_if_test_execution with(accepted:=true).
        -- rewrite <-NONNEGATIVE; apply word_store_nonnegative_test_execution; reflexivity.
        -- exact SCAN.
Qed.

Theorem nested_guard_demo_actual_accepts fe ge locals :
  exists after,
    exec_stmt fe ge locals(nested_scan_demo_temps 0 Int.one) sequence_demo_memory
      (nested_guard_demo_code(Int.repr 3)) E0 after sequence_demo_memory Out_normal /\
    after!100%positive=Some(Vint Int.one).
Proof.
  assert(READ : Mem.loadv Mint32 sequence_demo_memory(Vptr 1%positive Ptrofs.zero)=Some(Vint Int.one))
    by (apply sequence_demo_loadv; [cbn; tauto|apply sequence_demo_memory_header]).
  destruct(nested_scan_demo_actual_accepts fe ge locals) as [after [cached_after [SCAN [FRAME [FLAG REST]]]]].
  exists after; split; [|exact FLAG]; unfold nested_guard_demo_code,word_store_nested_guard_code.
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [apply nested_guard_demo_capture; exact READ|].
  apply nested_guard_demo_controls; [reflexivity|exact SCAN].
Qed.

Theorem nested_guard_demo_actual_child_refuses fe ge locals :
  exists after,
    exec_stmt fe ge locals(nested_scan_demo_temps 8(Int.repr 2)) nested_scan_demo_alias_memory
      (nested_guard_demo_code(Int.repr(-2))) E0 after nested_scan_demo_alias_memory Out_normal /\
    after!100%positive=Some(Vint Int.zero).
Proof.
  assert(ROOT : Mem.loadv Mint32 nested_scan_demo_alias_memory(Vptr 1%positive Ptrofs.zero)=Some(Vint Int.one))
    by (apply sequence_demo_loadv; [cbn; tauto|apply nested_scan_demo_alias_root_before]).
  assert(CHILD : Mem.loadv Mint32 nested_scan_demo_alias_memory(Vptr 1%positive(Ptrofs.repr 8))=Some(Vint(Int.repr 2)))
    by (apply sequence_demo_loadv; [cbn; tauto|apply nested_scan_demo_alias_child_before]).
  destruct(nested_scan_demo_actual_child_refuses fe ge locals) as [after [SCAN [FRAME FLAG]]].
  exists after; split; [|exact FLAG]; unfold nested_guard_demo_code,word_store_nested_guard_code.
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [apply nested_guard_demo_capture; assumption|].
  apply nested_guard_demo_controls; [reflexivity|exact SCAN].
Qed.

Lemma nested_guard_demo_rewrite_instance fe ge locals temps memory delta source_after final :
  exec_stmt fe ge locals temps memory(nested_scan_demo_source delta) E0 source_after final Out_normal ->
  exists after, exec_stmt fe ge locals temps memory(nested_guard_demo_rewrite delta) E0 after final Out_normal /\
    temp_agree nested_guard_demo_public source_after after.
Proof.
  intro SOURCE; unfold nested_guard_demo_rewrite.
  eapply word_store_nested_rewrite_execution with(checked:=sequence_scan_checked delta)
    (stable:=nested_scan_demo_stable)(live:=nested_scan_demo_live)(public:=nested_guard_demo_public)
    (rename:=nested_scan_demo_rename)(row:=1%positive)(cache:=2%positive)(pointer:=11%positive)
    (column:=3%positive)(child_cache:=4%positive)(child_pointer:=12%positive)
    (row_cursor:=20%positive)(row_limit:=21%positive)(column_cursor:=22%positive)(column_limit:=23%positive)(flag:=100%positive)
    (ge:=ge)(locals:=locals)(temps:=temps)(memory:=memory)(source_after:=source_after)(final:=final).
  all: try exact SOURCE; try reflexivity.
  all: cbn [nested_scan_demo_stable nested_scan_demo_live nested_guard_demo_public nested_scan_demo_rename
    sequence_scan_checked wsbody_sites sequence_demo_sites sequence_demo_body hd tl word_store_site_code
    wss_index wss_pointer direct_word_store direct_word_address sequence_demo_zero sequence_demo_rhs
    nested_cached_source nested_cached_body nested_loaded_offset_source nested_expression_source nested_expression_body
    strict_frontend_loop signed_expression_test signed_load_offset signed_load signed_pointer_temp
    rectangle_reset frontend_counted_loop counter_condition counter_increment statement_scope expression_scope
    statement_temps expression_temps incl List.In List.app].
  all: try (intros id [<-|[<-|[<-|[<-|[<-|[<-|BAD]]]]]];
    [reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|contradiction]).
  all: try (intros site [<-|[<-|BAD]];
    [cbn; unfold expression_scope,incl; cbn; tauto|cbn; unfold expression_scope,incl; cbn; tauto|contradiction]).
  all: try (repeat constructor; cbn; intuition congruence).
  all: unfold statement_scope,expression_scope,incl,nested_scan_demo_stable,nested_scan_demo_live,nested_guard_demo_public;
    cbn [nested_cached_source nested_cached_body nested_loaded_offset_source nested_expression_source nested_expression_body
      strict_frontend_loop signed_expression_test signed_load_offset signed_load signed_pointer_temp rectangle_reset
      frontend_counted_loop counter_condition counter_increment statement_temps expression_temps
      sequence_demo_body sequence_demo_sites hd tl word_store_site_code direct_word_store direct_word_address
      sequence_demo_rhs sequence_demo_zero wss_index wss_pointer wss_rhs List.app List.In]; intuition congruence.
Qed.

Theorem nested_guard_demo_accepting_rewrite fe ge locals :
  exists after, exec_stmt fe ge locals(nested_scan_demo_temps 0 Int.one) sequence_demo_memory
    (nested_guard_demo_rewrite(Int.repr 3)) E0 after sequence_demo_final Out_normal /\
    temp_agree nested_guard_demo_public(nested_scan_demo_exit(nested_scan_demo_temps 0 Int.one)) after.
Proof. apply nested_guard_demo_rewrite_instance,nested_scan_demo_original_accepts. Qed.
Theorem nested_guard_demo_child_fallback_rewrite fe ge locals :
  exists after, exec_stmt fe ge locals(nested_scan_demo_temps 8(Int.repr 2)) nested_scan_demo_alias_memory
    (nested_guard_demo_rewrite(Int.repr(-2))) E0 after nested_scan_demo_alias_final Out_normal /\
    temp_agree nested_guard_demo_public(nested_scan_demo_exit(nested_scan_demo_temps 8(Int.repr 2))) after.
Proof. apply nested_guard_demo_rewrite_instance,nested_scan_demo_original_child_alias. Qed.

Definition nested_guard_demo_empty_temps := sequence_scan_empty_temps.
Theorem nested_guard_demo_empty_original fe ge locals delta :
  exec_stmt fe ge locals nested_guard_demo_empty_temps sequence_scan_empty_memory
    (nested_scan_demo_source delta) E0 nested_guard_demo_empty_temps sequence_scan_empty_memory Out_normal.
Proof.
  unfold nested_scan_demo_source,nested_loaded_offset_source,nested_expression_source; apply strict_zero_trip_encode.
  change false with(Int.lt Int.zero Int.zero); apply sequence_scan_first_test; [reflexivity|reflexivity|].
  apply sequence_demo_loadv; [cbn; tauto|apply sequence_scan_empty_header].
Qed.
Theorem nested_guard_demo_empty_guard fe ge locals delta :
  let captured := PTree.set 2%positive(Vint Int.zero) nested_guard_demo_empty_temps in
  let after := PTree.set 100%positive(Vint Int.one) captured in
  exec_stmt fe ge locals nested_guard_demo_empty_temps sequence_scan_empty_memory
    (nested_guard_demo_code delta) E0 after sequence_scan_empty_memory Out_normal /\
  after!12%positive=None /\ after!4%positive=None /\ after!9%positive=None /\ after!10%positive=None /\
  after!100%positive=Some(Vint Int.one).
Proof.
  cbn zeta; split; [|repeat split; reflexivity].
  unfold nested_guard_demo_code,word_store_nested_guard_code,nested_expression_capture.
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=PTree.set 2%positive(Vint Int.zero) nested_guard_demo_empty_temps)
    (m1:=sequence_scan_empty_memory).
  - eapply exec_Sseq_1 with(t1:=E0)(t2:=E0).
    + constructor; replace(Vint Int.zero) with(Vint(Int.add Int.zero Int.zero)) by (rewrite Int.add_zero; reflexivity).
      eapply signed_load_offset_eval; [reflexivity|].
      apply sequence_demo_loadv; [cbn; tauto|apply sequence_scan_empty_header].
    + eapply word_store_if_test_execution with(accepted:=false).
      * change false with(Int.lt Int.zero Int.zero); eapply signed_expression_test_eval; [reflexivity|reflexivity|constructor; reflexivity].
      * constructor.
  - unfold word_store_nested_controls; eapply word_store_if_test_execution with(accepted:=true).
    + change true with(Int.eq Int.zero Int.zero); apply word_store_zero_test_execution; reflexivity.
    + eapply word_store_if_test_execution with(accepted:=true).
      * change true with(negb(Int.lt Int.zero Int.zero)); apply word_store_nonnegative_test_execution; reflexivity.
      * eapply word_store_if_test_execution with(accepted:=false).
        -- change false with(Int.lt Int.zero Int.zero); apply word_store_positive_test_execution; reflexivity.
        -- constructor; constructor.
Qed.
Theorem nested_guard_demo_empty_rewrite fe ge locals delta :
  exists after, exec_stmt fe ge locals nested_guard_demo_empty_temps sequence_scan_empty_memory
    (nested_guard_demo_rewrite delta) E0 after sequence_scan_empty_memory Out_normal /\
    temp_agree nested_guard_demo_public nested_guard_demo_empty_temps after.
Proof. apply nested_guard_demo_rewrite_instance,nested_guard_demo_empty_original. Qed.

Print Assumptions nested_guard_demo_set_cached.
Print Assumptions nested_guard_demo_capture.
Print Assumptions nested_guard_demo_controls.
Print Assumptions nested_guard_demo_actual_accepts.
Print Assumptions nested_guard_demo_actual_child_refuses.
Print Assumptions nested_guard_demo_rewrite_instance.
Print Assumptions nested_guard_demo_accepting_rewrite.
Print Assumptions nested_guard_demo_child_fallback_rewrite.
Print Assumptions nested_guard_demo_empty_original.
Print Assumptions nested_guard_demo_empty_guard.
Print Assumptions nested_guard_demo_empty_rewrite.
