(** Two loaded axes in real allocated memory. Both captured addresses are
    checked; a write to only the child header refuses before a later leaf. *)
From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame ClightTempFootprint
  ClightLoopSyntax ClightCountedLoop ClightCountedProtocol ClightFrontendLoopProtocol
  ClightProjectedExecution ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightLoadedOffsetHeader
  ClightExpressionHeaderCapture ClightSignedExpressionProgress ClightDualLoadedUnitSyntax ClightNestedExpressionCapture
  ClightNestedExpressionTransport ClightNestedLoadedOffset ClightDirectWordObservation ClightAffineJointObservation
  ClightWordStoreSequence ClightWordStoreSequenceFactory ClightWordStoreSequenceLoaded
  ClightWordStoreSequenceExample ClightWordStoreSequenceScanExample
  ClightWordStoreNestedPrefix ClightWordStoreNestedScan ClightWordStoreNestedCached.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition nested_scan_demo_rename id :=
  if peq id 1%positive then 20%positive else if peq id 3%positive then 22%positive else id.
Definition nested_scan_demo_stable := [2;4;9;10;11;12]%positive.
Definition nested_scan_demo_live := [1;2;3;4;9;10;11;12]%positive.
Definition nested_scan_demo_temps child_offset child_word :=
  PTree.set 12%positive (Vptr 1%positive (Ptrofs.repr child_offset))
    (PTree.set 4%positive (Vint child_word)
      (PTree.set 2%positive (Vint Int.one) (sequence_demo_temps 8))).
Definition nested_scan_demo_source delta := nested_loaded_offset_source
  1%positive 11%positive Int.zero 3%positive 12%positive Int.zero (sequence_demo_body delta).
Definition nested_scan_demo_code delta := word_store_nested_scan_code
  2%positive 4%positive 20%positive 21%positive 22%positive 23%positive 100%positive
  nested_scan_demo_rename (sequence_demo_sites delta) 11%positive 12%positive.
Definition nested_scan_demo_result delta entry := word_store_nested_scan_result
  2%positive 4%positive 20%positive 22%positive nested_scan_demo_rename
  (sequence_demo_sites delta) 11%positive 12%positive entry.
Definition nested_scan_demo_exit temps := PTree.set 1%positive (Vint Int.one)
  (PTree.set 3%positive (Vint Int.one) temps).

Lemma nested_scan_demo_test ge locals temps memory row pointer offset raw counter :
  temps!row=Some(Vint counter) -> temps!pointer=Some(Vptr 1%positive (Ptrofs.repr offset)) ->
  Mem.loadv Mint32 memory (Vptr 1%positive (Ptrofs.repr offset))=Some(Vint raw) ->
  expression_test(signed_expression_test row(signed_load_offset pointer Int.zero))
    (Entry ge locals temps memory)(Int.lt counter raw).
Proof.
  intros ROW POINTER LOAD; rewrite <-(Int.add_zero raw) at 1.
  eapply signed_expression_test_eval; [reflexivity|exact ROW|].
  eapply signed_load_offset_eval; eassumption.
Qed.

Lemma nested_scan_demo_one_iteration fe ge locals temps memory final delta child_offset before_child after_child :
  temps!1%positive=Some(Vint Int.zero) -> temps!11%positive=Some(Vptr 1%positive Ptrofs.zero) ->
  temps!12%positive=Some(Vptr 1%positive(Ptrofs.repr child_offset)) ->
  Mem.loadv Mint32 memory(Vptr 1%positive Ptrofs.zero)=Some(Vint Int.one) ->
  Mem.loadv Mint32 final(Vptr 1%positive Ptrofs.zero)=Some(Vint Int.one) ->
  Mem.loadv Mint32 memory(Vptr 1%positive(Ptrofs.repr child_offset))=Some(Vint before_child) ->
  Mem.loadv Mint32 final(Vptr 1%positive(Ptrofs.repr child_offset))=Some(Vint after_child) ->
  Int.lt Int.zero before_child=true -> Int.lt Int.one after_child=false ->
  exec_stmt fe ge locals(PTree.set 3%positive(Vint Int.zero) temps) memory
    (sequence_demo_body delta) E0(PTree.set 3%positive(Vint Int.zero) temps) final Out_normal ->
  exec_stmt fe ge locals temps memory(nested_scan_demo_source delta) E0(nested_scan_demo_exit temps) final Out_normal.
Proof.
  intros ROW ROOT CHILD ROOT_BEFORE ROOT_AFTER CHILD_BEFORE CHILD_AFTER ACTIVE DONE BODY.
  unfold nested_scan_demo_source,nested_loaded_offset_source,nested_expression_source,nested_expression_body.
  eapply strict_iteration_encode with(body_temps:=PTree.set 3%positive(Vint Int.one) temps)(body_memory:=final).
  - change true with(Int.lt Int.zero Int.one); eapply nested_scan_demo_test; eassumption.
  - exists Int.zero; split; [rewrite PTree.gso by discriminate; exact ROW|change(0<2147483647); lia].
  - eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=PTree.set 3%positive(Vint Int.zero) temps)(m1:=memory).
    + constructor; constructor.
    + eapply strict_iteration_encode with(body_temps:=PTree.set 3%positive(Vint Int.zero) temps)(body_memory:=final).
      * rewrite <-ACTIVE; eapply nested_scan_demo_test;
          [apply PTree.gss|rewrite PTree.gso by discriminate; exact CHILD|exact CHILD_BEFORE].
      * exists Int.zero; split; [apply PTree.gss|change(0<2147483647); lia].
      * exact BODY.
      * unfold increment_temps,temp_word; rewrite PTree.gss; change(Int.add Int.zero Int.one) with Int.one.
        rewrite PTree.set2; apply strict_zero_trip_encode; rewrite <-DONE.
        eapply nested_scan_demo_test;
          [apply PTree.gss|rewrite PTree.gso by discriminate; exact CHILD|exact CHILD_AFTER].
  - unfold increment_temps,temp_word,nested_scan_demo_exit; rewrite PTree.gso by discriminate; rewrite ROW.
    change(Int.add Int.zero Int.one) with Int.one.
    apply strict_zero_trip_encode; change false with(Int.lt Int.one Int.one).
    eapply nested_scan_demo_test;
      [apply PTree.gss|repeat rewrite PTree.gso by discriminate; exact ROOT|exact ROOT_AFTER].
Qed.

Lemma nested_scan_demo_accepting_body fe ge locals temps :
  temps!9%positive=Some(Vptr 1%positive(Ptrofs.repr 4)) ->
  temps!10%positive=Some(Vptr 1%positive(Ptrofs.repr 8)) ->
  exec_stmt fe ge locals temps sequence_demo_memory(sequence_demo_body(Int.repr 3))
    E0 temps sequence_demo_final Out_normal.
Proof.
  intros A B.
  destruct(@structured_execution_temp_transport fe ge locals(sequence_demo_temps 8) sequence_demo_memory
    (sequence_demo_body(Int.repr 3)) E0(sequence_demo_temps 8) sequence_demo_final Out_normal
    (sequence_demo_actual_source fe ge locals) [9;10]%positive temps []
    (wsbody_writes(sequence_scan_checked(Int.repr 3)))
    ltac:(unfold statement_scope,incl; cbn; intuition congruence)
    ltac:(intros id [<-|[<-|BAD]]; [exact A|exact B|contradiction])) as [after [RUN FRAME]].
  rewrite(proj1(word_store_loaded_source_permissions(sequence_scan_checked(Int.repr 3)) RUN)) in RUN; exact RUN.
Qed.

Theorem nested_scan_demo_original_accepts fe ge locals :
  exec_stmt fe ge locals(nested_scan_demo_temps 0 Int.one) sequence_demo_memory
    (nested_scan_demo_source(Int.repr 3)) E0(nested_scan_demo_exit(nested_scan_demo_temps 0 Int.one))
    sequence_demo_final Out_normal.
Proof.
  eapply nested_scan_demo_one_iteration with(child_offset:=0)(before_child:=Int.one)(after_child:=Int.one);
    try reflexivity.
  - apply sequence_demo_loadv; [cbn; tauto|apply sequence_demo_memory_header].
  - apply sequence_demo_loadv; [cbn; tauto|exact(proj1 sequence_demo_header_and_arrays)].
  - apply sequence_demo_loadv; [cbn; tauto|apply sequence_demo_memory_header].
  - apply sequence_demo_loadv; [cbn; tauto|exact(proj1 sequence_demo_header_and_arrays)].
  - apply nested_scan_demo_accepting_body; reflexivity.
Qed.

Definition nested_scan_demo_alias_memory := sequence_demo_write
  (sequence_demo_write sequence_demo_alloc 0 Int.one) 8(Int.repr 2).
Definition nested_scan_demo_alias_middle := sequence_demo_write nested_scan_demo_alias_memory 4 Int.zero.
Definition nested_scan_demo_alias_final := sequence_demo_write nested_scan_demo_alias_middle 8(Int.repr(-2)).
Lemma nested_scan_demo_alias_cells : sequence_demo_cells nested_scan_demo_alias_memory.
Proof. apply sequence_demo_write_cells; [apply sequence_demo_write_cells; [apply sequence_demo_alloc_cells|cbn; tauto]|cbn; tauto]. Qed.
Lemma nested_scan_demo_alias_middle_cells : sequence_demo_cells nested_scan_demo_alias_middle.
Proof. apply sequence_demo_write_cells; [apply nested_scan_demo_alias_cells|cbn; tauto]. Qed.
Lemma nested_scan_demo_alias_root_before : Mem.load Mint32 nested_scan_demo_alias_memory 1%positive 0=Some(Vint Int.one).
Proof.
  unfold nested_scan_demo_alias_memory; rewrite sequence_demo_write_other;
    [apply sequence_demo_write_same; [apply sequence_demo_alloc_cells|cbn; tauto]| |cbn; tauto|lia].
  apply sequence_demo_write_cells; [apply sequence_demo_alloc_cells|cbn; tauto].
Qed.
Lemma nested_scan_demo_alias_root_after : Mem.load Mint32 nested_scan_demo_alias_final 1%positive 0=Some(Vint Int.one).
Proof.
  unfold nested_scan_demo_alias_final; rewrite sequence_demo_write_other;
    [|apply nested_scan_demo_alias_middle_cells|cbn; tauto|lia].
  unfold nested_scan_demo_alias_middle; rewrite sequence_demo_write_other;
    [apply nested_scan_demo_alias_root_before|apply nested_scan_demo_alias_cells|cbn; tauto|lia].
Qed.
Lemma nested_scan_demo_alias_child_before : Mem.load Mint32 nested_scan_demo_alias_memory 1%positive 8=Some(Vint(Int.repr 2)).
Proof.
  apply sequence_demo_write_same; [apply sequence_demo_write_cells; [apply sequence_demo_alloc_cells|cbn; tauto]|cbn; tauto].
Qed.
Lemma nested_scan_demo_alias_child_after : Mem.load Mint32 nested_scan_demo_alias_final 1%positive 8=Some(Vint(Int.repr(-2))).
Proof. apply sequence_demo_write_same; [apply nested_scan_demo_alias_middle_cells|cbn; tauto]. Qed.
Lemma nested_scan_demo_alias_body fe ge locals temps :
  temps!9%positive=Some(Vptr 1%positive(Ptrofs.repr 4)) ->
  temps!10%positive=Some(Vptr 1%positive(Ptrofs.repr 8)) ->
  exec_stmt fe ge locals temps nested_scan_demo_alias_memory(sequence_demo_body(Int.repr(-2)))
    E0 temps nested_scan_demo_alias_final Out_normal.
Proof.
  intros A B; unfold sequence_demo_body; cbn [sequence_demo_sites hd tl word_store_site_code].
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=temps)(m1:=nested_scan_demo_alias_middle).
  - eapply sequence_demo_store_execution with(block:=1%positive)(destination_offset:=Ptrofs.repr 4)
      (source_offset:=Ptrofs.repr 8)(raw:=Int.repr 2); [exact A|exact B| |].
    + apply sequence_demo_loadv; [cbn; tauto|apply nested_scan_demo_alias_child_before].
    + rewrite Int.add_signed; change(Mem.storev Mint32 nested_scan_demo_alias_memory(Vptr 1%positive(Ptrofs.repr 4))
        (Vint Int.zero)=Some nested_scan_demo_alias_middle).
      apply sequence_demo_storev; [apply nested_scan_demo_alias_cells|cbn; tauto].
  - eapply sequence_demo_store_execution with(block:=1%positive)(destination_offset:=Ptrofs.repr 8)
      (source_offset:=Ptrofs.repr 4)(raw:=Int.zero); [exact B|exact A| |].
    + apply sequence_demo_loadv; [cbn; tauto|apply sequence_demo_write_same; [apply nested_scan_demo_alias_cells|cbn; tauto]].
    + rewrite Int.add_zero_l; apply sequence_demo_storev; [apply nested_scan_demo_alias_middle_cells|cbn; tauto].
Qed.
Theorem nested_scan_demo_original_child_alias fe ge locals :
  exec_stmt fe ge locals(nested_scan_demo_temps 8(Int.repr 2)) nested_scan_demo_alias_memory
    (nested_scan_demo_source(Int.repr(-2))) E0(nested_scan_demo_exit(nested_scan_demo_temps 8(Int.repr 2)))
    nested_scan_demo_alias_final Out_normal.
Proof.
  eapply nested_scan_demo_one_iteration with(child_offset:=8)(before_child:=Int.repr 2)(after_child:=Int.repr(-2));
    try reflexivity.
  - apply sequence_demo_loadv; [cbn; tauto|apply nested_scan_demo_alias_root_before].
  - apply sequence_demo_loadv; [cbn; tauto|apply nested_scan_demo_alias_root_after].
  - apply sequence_demo_loadv; [cbn; tauto|apply nested_scan_demo_alias_child_before].
  - apply sequence_demo_loadv; [cbn; tauto|apply nested_scan_demo_alias_child_after].
  - apply nested_scan_demo_alias_body; reflexivity.
Qed.

Lemma nested_scan_demo_ready ge locals child_offset child_word memory :
  Mem.loadv Mint32 memory(Vptr 1%positive Ptrofs.zero)=Some(Vint Int.one) ->
  Mem.loadv Mint32 memory(Vptr 1%positive(Ptrofs.repr child_offset))=Some(Vint child_word) ->
  word_store_nested_ready 11%positive Int.zero 2%positive 12%positive Int.zero 4%positive
    (Entry ge locals(nested_scan_demo_temps child_offset child_word) memory).
Proof.
  intros ROOT CHILD; split.
  - exists 1%positive,Ptrofs.zero,Int.one; split; [reflexivity|split; [exact ROOT|rewrite Int.add_zero; reflexivity]].
  - exists 1%positive,(Ptrofs.repr child_offset),child_word; split; [reflexivity|split; [exact CHILD|rewrite Int.add_zero; reflexivity]].
Qed.

Lemma nested_scan_demo_observers ge locals child_offset child_word memory :
  Mem.loadv Mint32 memory(Vptr 1%positive Ptrofs.zero)=Some(Vint Int.one) ->
  Mem.loadv Mint32 memory(Vptr 1%positive(Ptrofs.repr child_offset))=Some(Vint child_word) ->
  word_store_nested_observers 11%positive 12%positive
    (Entry ge locals(nested_scan_demo_temps child_offset child_word) memory)=
  [ClightWordObserver(signed_pointer_temp 11%positive) 1%positive Ptrofs.zero(Vint Int.one);
   ClightWordObserver(signed_pointer_temp 12%positive) 1%positive(Ptrofs.repr child_offset)(Vint child_word)].
Proof.
  intros ROOT CHILD; unfold word_store_nested_observers,word_store_loaded_observers.
  change ((match Mem.loadv Mint32 memory(Vptr 1%positive Ptrofs.zero) with
    | Some value=>[ClightWordObserver(signed_pointer_temp 11%positive) 1%positive Ptrofs.zero value]|None=>[] end) ++
    (match Mem.loadv Mint32 memory(Vptr 1%positive(Ptrofs.repr child_offset)) with
    | Some value=>[ClightWordObserver(signed_pointer_temp 12%positive) 1%positive(Ptrofs.repr child_offset) value]|None=>[] end)=
    [ClightWordObserver(signed_pointer_temp 11%positive) 1%positive Ptrofs.zero(Vint Int.one);
     ClightWordObserver(signed_pointer_temp 12%positive) 1%positive(Ptrofs.repr child_offset)(Vint child_word)]).
  rewrite ROOT,CHILD; reflexivity.
Qed.

Lemma nested_scan_demo_accept_result ge locals :
  nested_scan_demo_result(Int.repr 3)
    (Entry ge locals(nested_scan_demo_temps 0 Int.one) sequence_demo_memory)=true.
Proof.
  unfold nested_scan_demo_result,word_store_nested_scan_result,word_store_nested_inner_scan_result.
  change(memory_boolean_scan_result(fun i=>memory_boolean_scan_result
    (fun j=>word_store_nested_point_result 20%positive 22%positive nested_scan_demo_rename
      (sequence_demo_sites(Int.repr 3)) 11%positive 12%positive i j
      (Entry ge locals(nested_scan_demo_temps 0 Int.one) sequence_demo_memory)) 0 1) 0 1=true).
  unfold word_store_nested_point_result.
  assert (READ : Mem.loadv Mint32 sequence_demo_memory(Vptr 1%positive Ptrofs.zero)=Some(Vint Int.one))
    by (apply sequence_demo_loadv; [cbn; tauto|apply sequence_demo_memory_header]).
  rewrite(@nested_scan_demo_observers ge locals 0 Int.one sequence_demo_memory READ READ); reflexivity.
Qed.

Lemma nested_scan_demo_refuse_result ge locals :
  nested_scan_demo_result(Int.repr(-2))
    (Entry ge locals(nested_scan_demo_temps 8(Int.repr 2)) nested_scan_demo_alias_memory)=false.
Proof.
  unfold nested_scan_demo_result,word_store_nested_scan_result,word_store_nested_inner_scan_result.
  change(memory_boolean_scan_result(fun i=>memory_boolean_scan_result
    (fun j=>word_store_nested_point_result 20%positive 22%positive nested_scan_demo_rename
      (sequence_demo_sites(Int.repr(-2))) 11%positive 12%positive i j
      (Entry ge locals(nested_scan_demo_temps 8(Int.repr 2)) nested_scan_demo_alias_memory)) 0 2) 0 1=false).
  unfold word_store_nested_point_result.
  assert (ROOT : Mem.loadv Mint32 nested_scan_demo_alias_memory(Vptr 1%positive Ptrofs.zero)=Some(Vint Int.one))
    by (apply sequence_demo_loadv; [cbn; tauto|apply nested_scan_demo_alias_root_before]).
  assert (CHILD : Mem.loadv Mint32 nested_scan_demo_alias_memory(Vptr 1%positive(Ptrofs.repr 8))=Some(Vint(Int.repr 2)))
    by (apply sequence_demo_loadv; [cbn; tauto|apply nested_scan_demo_alias_child_before]).
  rewrite(@nested_scan_demo_observers ge locals 8(Int.repr 2) nested_scan_demo_alias_memory ROOT CHILD); reflexivity.
Qed.

Lemma nested_scan_demo_instance fe ge locals child_offset child_word memory delta source_after final :
  word_store_nested_ready 11%positive Int.zero 2%positive 12%positive Int.zero 4%positive
    (Entry ge locals(nested_scan_demo_temps child_offset child_word) memory) ->
  0<=Int.signed child_word ->
  exec_stmt fe ge locals(nested_scan_demo_temps child_offset child_word) memory
    (nested_scan_demo_source delta) E0 source_after final Out_normal ->
  exists after,
    exec_stmt fe ge locals(nested_scan_demo_temps child_offset child_word) memory
      (nested_scan_demo_code delta) E0 after memory Out_normal /\
    temp_agree nested_scan_demo_live(nested_scan_demo_temps child_offset child_word) after /\
    after!100%positive=Some(memory_boolean_word(nested_scan_demo_result delta
      (Entry ge locals(nested_scan_demo_temps child_offset child_word) memory))) /\
    (nested_scan_demo_result delta(Entry ge locals(nested_scan_demo_temps child_offset child_word) memory)=true ->
      exists cached_after, exec_stmt fe ge locals after memory
        (nested_cached_source 1%positive 2%positive 3%positive 4%positive(sequence_demo_body delta))
        E0 cached_after final Out_normal /\ temp_agree nested_scan_demo_live source_after cached_after).
Proof.
  intros READY NONNEGATIVE SOURCE.
  unfold nested_scan_demo_code,nested_scan_demo_result.
  eapply(@word_store_nested_scan_cached_exit fe 1%positive 2%positive 11%positive
    3%positive 4%positive 12%positive 20%positive 21%positive 22%positive 23%positive 100%positive
    Int.zero Int.zero(sequence_demo_body delta)(sequence_scan_checked delta)
    nested_scan_demo_stable nested_scan_demo_live nested_scan_demo_rename)
    with(entry:=Entry ge locals(nested_scan_demo_temps child_offset child_word) memory)
      (current:=nested_scan_demo_temps child_offset child_word)(source_after:=source_after)(final:=final).
  all: try exact READY; try exact SOURCE; try reflexivity; try apply temp_agree_refl.
  all: cbn [nested_scan_demo_stable nested_scan_demo_live nested_scan_demo_rename
    sequence_scan_checked wsbody_sites sequence_demo_sites sequence_demo_body hd tl word_store_site_code
    wss_index wss_pointer direct_word_store direct_word_address sequence_demo_zero
    sequence_demo_rhs nested_cached_source nested_cached_body rectangle_reset frontend_counted_loop
    counter_condition counter_increment statement_scope expression_scope statement_temps expression_temps
    incl List.In].
  all: try (intros id [<-|[<-|[<-|[<-|[<-|[<-|BAD]]]]]];
    [reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|contradiction]).
  all: try (intros site [<-|[<-|BAD]];
    [cbn; unfold expression_scope,incl; cbn; tauto|cbn; unfold expression_scope,incl; cbn; tauto|contradiction]).
  all: try (repeat constructor; cbn; intuition congruence).
  all: unfold statement_scope,expression_scope,incl,nested_scan_demo_stable,nested_scan_demo_live;
    cbn [nested_cached_source nested_cached_body rectangle_reset frontend_counted_loop counter_condition counter_increment
      statement_temps expression_temps sequence_demo_body sequence_demo_sites hd tl word_store_site_code
      direct_word_store direct_word_address sequence_demo_rhs sequence_demo_zero wss_index wss_rhs List.In];
    try (intuition congruence).
  all: try (change(0<=Int.signed child_word); exact NONNEGATIVE).
  all: try (cbn [wss_pointer List.app List.In]; intuition congruence).
  all: change(0<=1); lia.
Qed.

Theorem nested_scan_demo_actual_accepts fe ge locals :
  exists after cached_after,
    exec_stmt fe ge locals(nested_scan_demo_temps 0 Int.one) sequence_demo_memory
      (nested_scan_demo_code(Int.repr 3)) E0 after sequence_demo_memory Out_normal /\
    temp_agree nested_scan_demo_live(nested_scan_demo_temps 0 Int.one) after /\
    after!100%positive=Some(Vint Int.one) /\
    exec_stmt fe ge locals after sequence_demo_memory
      (nested_cached_source 1%positive 2%positive 3%positive 4%positive(sequence_demo_body(Int.repr 3)))
      E0 cached_after sequence_demo_final Out_normal /\
    temp_agree nested_scan_demo_live(nested_scan_demo_exit(nested_scan_demo_temps 0 Int.one)) cached_after.
Proof.
  assert (READ : Mem.loadv Mint32 sequence_demo_memory(Vptr 1%positive Ptrofs.zero)=Some(Vint Int.one))
    by (apply sequence_demo_loadv; [cbn; tauto|apply sequence_demo_memory_header]).
  destruct(nested_scan_demo_instance (@nested_scan_demo_ready ge locals 0 Int.one sequence_demo_memory READ READ)
    ltac:(change(0<=1); lia) (nested_scan_demo_original_accepts fe ge locals))
    as [after [RUN [FRAME [FLAG CACHED]]]].
  rewrite nested_scan_demo_accept_result in FLAG,CACHED; destruct(CACHED eq_refl) as [cached_after [EXEC PUBLIC]].
  exists after,cached_after; repeat split; assumption.
Qed.

Theorem nested_scan_demo_actual_child_refuses fe ge locals :
  exists after,
    exec_stmt fe ge locals(nested_scan_demo_temps 8(Int.repr 2)) nested_scan_demo_alias_memory
      (nested_scan_demo_code(Int.repr(-2))) E0 after nested_scan_demo_alias_memory Out_normal /\
    temp_agree nested_scan_demo_live(nested_scan_demo_temps 8(Int.repr 2)) after /\
    after!100%positive=Some(Vint Int.zero).
Proof.
  assert (ROOT : Mem.loadv Mint32 nested_scan_demo_alias_memory(Vptr 1%positive Ptrofs.zero)=Some(Vint Int.one))
    by (apply sequence_demo_loadv; [cbn; tauto|apply nested_scan_demo_alias_root_before]).
  assert (CHILD : Mem.loadv Mint32 nested_scan_demo_alias_memory(Vptr 1%positive(Ptrofs.repr 8))=Some(Vint(Int.repr 2)))
    by (apply sequence_demo_loadv; [cbn; tauto|apply nested_scan_demo_alias_child_before]).
  destruct(nested_scan_demo_instance (@nested_scan_demo_ready ge locals 8(Int.repr 2) nested_scan_demo_alias_memory ROOT CHILD)
    ltac:(change(0<=2); lia) (nested_scan_demo_original_child_alias fe ge locals))
    as [after [RUN [FRAME [FLAG CACHED]]]].
  rewrite nested_scan_demo_refuse_result in FLAG; exists after; repeat split; assumption.
Qed.

Print Assumptions nested_scan_demo_one_iteration.
Print Assumptions nested_scan_demo_accepting_body.
Print Assumptions nested_scan_demo_original_accepts.
Print Assumptions nested_scan_demo_alias_cells.
Print Assumptions nested_scan_demo_alias_middle_cells.
Print Assumptions nested_scan_demo_alias_root_before.
Print Assumptions nested_scan_demo_alias_root_after.
Print Assumptions nested_scan_demo_alias_child_before.
Print Assumptions nested_scan_demo_alias_child_after.
Print Assumptions nested_scan_demo_alias_body.
Print Assumptions nested_scan_demo_original_child_alias.
Print Assumptions nested_scan_demo_ready.
Print Assumptions nested_scan_demo_observers.
Print Assumptions nested_scan_demo_accept_result.
Print Assumptions nested_scan_demo_refuse_result.
Print Assumptions nested_scan_demo_instance.
Print Assumptions nested_scan_demo_actual_accepts.
Print Assumptions nested_scan_demo_actual_child_refuses.
