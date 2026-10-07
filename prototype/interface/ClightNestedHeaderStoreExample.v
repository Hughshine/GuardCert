From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap ClightRedundantSet ClightCountedLoop
  ClightCountedProtocol ClightLoopSyntax ClightRegionProgress ClightRectangularLoops ClightSameAddress CompCertMemoryActions.
From GuardInterface Require Import ClightNestedExpressionCapture ClightNestedExpressionTransport ClightNestedExpressionPrefix
  ClightExpressionBodyPrefix ClightNestedLoadedOffset ClightLoadedOffsetHeader ClightSignedExpressionProgress
  ClightStrictLoopProgress ClightExpressionHeaderCapture ClightDualLoadedUnitSyntax ClightObservedHeaderPrefix
  ClightLoadedAffineScanAcceptExample ClightWordAddressSeparation ClightLoadedBoundSyntax ClightStorePermissions
  ClightReadonlyRewrite.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition nhs_temps := nested_expression_captured 31%positive 32%positive
  (PTree.set 20%positive (Vint Int.zero) lns_separate_temps) Int.one (Some Int.one).
Definition nhs_stable := [3%positive;11%positive;31%positive;32%positive].
Definition nhs_bound := signed_load_offset 11%positive (Int.repr(-1)).
Definition nhs_source := nested_expression_source 20%positive nhs_bound 1%positive nhs_bound (dual_unit_store 3%positive).
Definition nhs_exit := PTree.set 20%positive (Vint Int.one) (PTree.set 1%positive (Vint Int.one) nhs_temps).
Definition nhs_final_state : {memory | Mem.store Mint32 lns_initial 1%positive 4(Vint(Int.repr 2))=Some memory}.
Proof. apply Mem.valid_access_store; eapply Mem.store_valid_access_1; [exact(proj2_sig lns_initial_state)|].
  apply lns_allocated_word; [lia|lia|exists 1; reflexivity]. Defined.
Definition nhs_final := proj1_sig nhs_final_state.
Definition nhs_observations entry := nested_loaded_offset_observations 11%positive 11%positive entry.
Definition nhs_ready entry := loaded_offset_cached_header 11%positive (Int.repr(-1)) 31%positive entry /\
  loaded_offset_cached_header 11%positive (Int.repr(-1)) 32%positive entry.
Definition nhs_root_prefix fe := expression_body_prefix fe 20%positive 31%positive nhs_bound
  (nested_expression_body 1%positive nhs_bound (dual_unit_store 3%positive)) nhs_stable nhs_ready nhs_observations.

Lemma nhs_machine_upper : Int.add(Int.repr 2)(Int.repr(-1))=Int.one.
Proof. apply Int.same_if_eq; vm_compute; reflexivity. Qed.
Lemma nhs_final_bound_read : Mem.loadv Mint32 nhs_final(Vptr 1%positive Ptrofs.zero)=Some(Vint(Int.repr 2)).
Proof.
  change (Mem.load Mint32 nhs_final 1%positive 0=Some(Vint(Int.repr 2))).
  rewrite (@Mem.load_store_other Mint32 lns_initial 1%positive 4(Vint(Int.repr 2)) nhs_final
    (proj2_sig nhs_final_state) Mint32 1%positive 0 ltac:(right; left; change(0+4<=4); lia)).
  exact (proj1 same_block_bound_reads).
Qed.
Lemma nhs_snapshots ge locals : nhs_ready (Entry ge locals nhs_temps lns_initial).
Proof.
  unfold nhs_ready; split.
  - exists 1%positive,Ptrofs.zero,(Int.repr 2); split; [reflexivity|split; [exact(proj1 same_block_bound_reads)|rewrite nhs_machine_upper; reflexivity]].
  - exists 1%positive,Ptrofs.zero,(Int.repr 2); split; [reflexivity|split; [exact(proj1 same_block_bound_reads)|rewrite nhs_machine_upper; reflexivity]].
Qed.

Lemma nhs_reached_header ge locals temps memory :
  temps!11%positive=Some(Vptr 1%positive Ptrofs.zero) ->
  Mem.loadv Mint32 memory(Vptr 1%positive Ptrofs.zero)=Some(Vint(Int.repr 2)) ->
  eval_expr ge locals temps memory nhs_bound (Vint Int.one).
Proof. intros POINTER READ; rewrite <-nhs_machine_upper; eapply signed_load_offset_eval; eassumption. Qed.

Theorem nested_adjacent_original_executes fe ge locals :
  exec_stmt fe ge locals nhs_temps lns_initial nhs_source E0 nhs_exit nhs_final Out_normal.
Proof.
  unfold nhs_source,nested_expression_source,nhs_exit; eapply strict_iteration_encode with
    (body_temps:=PTree.set 1%positive(Vint Int.one) nhs_temps) (body_memory:=nhs_final).
  - change true with (Int.lt Int.zero Int.one); apply signed_expression_test_eval;
      [reflexivity|reflexivity|apply nhs_reached_header; [reflexivity|exact(proj1 same_block_bound_reads)]].
  - exists Int.zero; split; [reflexivity|change(0<2147483647); lia].
  - unfold nested_expression_body; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=nhs_temps) (m1:=lns_initial).
    + replace nhs_temps with (PTree.set 1%positive(Vint Int.zero) nhs_temps) at 2 by reflexivity; constructor; constructor.
    + eapply strict_iteration_encode with (body_temps:=nhs_temps) (body_memory:=nhs_final).
      * change true with(Int.lt Int.zero Int.one); apply signed_expression_test_eval;
          [reflexivity|reflexivity|apply nhs_reached_header; [reflexivity|exact(proj1 same_block_bound_reads)]].
      * exists Int.zero; split; [reflexivity|change(0<2147483647); lia].
      * eapply dual_unit_store_encode; [reflexivity|exact(proj2_sig nhs_final_state)].
      * change (exec_stmt fe ge locals (PTree.set 1%positive(Vint Int.one) nhs_temps) nhs_final
          (strict_frontend_loop 1%positive (signed_expression_test 1%positive nhs_bound) (dual_unit_store 3%positive))
          E0 (PTree.set 1%positive(Vint Int.one) nhs_temps) nhs_final Out_normal).
        apply signed_expression_zero_trip_execution; change false with(Int.lt Int.one Int.one).
        apply signed_expression_test_eval; [reflexivity|apply PTree.gss|apply nhs_reached_header; [reflexivity|exact nhs_final_bound_read]].
  - change (exec_stmt fe ge locals (PTree.set 20%positive(Vint Int.one)(PTree.set 1%positive(Vint Int.one) nhs_temps))
      nhs_final (strict_frontend_loop 20%positive (signed_expression_test 20%positive nhs_bound)
        (nested_expression_body 1%positive nhs_bound (dual_unit_store 3%positive))) E0
      (PTree.set 20%positive(Vint Int.one)(PTree.set 1%positive(Vint Int.one) nhs_temps)) nhs_final Out_normal).
    apply signed_expression_zero_trip_execution; change false with(Int.lt Int.one Int.one).
    apply signed_expression_test_eval; [reflexivity|apply PTree.gss|apply nhs_reached_header; [reflexivity|exact nhs_final_bound_read]].
Qed.

(** A point condition sufficient for every actual body execution in this
    example: the output word is four bytes after the shared header word. *)
Lemma nhs_point_preserves fe ge locals current memory after final :
  temp_agree nhs_stable nhs_temps current ->
  header_observations_match (nhs_observations (Entry ge locals nhs_temps lns_initial)) memory ->
  exec_stmt fe ge locals current memory (dual_unit_store 3%positive) E0 after final Out_normal ->
  header_observations_match (nhs_observations (Entry ge locals nhs_temps lns_initial)) final.
Proof.
  intros FRAME OBSERVED RUN.
  destruct (dual_unit_store_decode RUN) as [block [offset [POINTER [TEMPS STORE]]]].
  rewrite FRAME in POINTER by (left; reflexivity).
  change (Some(Vptr 1%positive(Ptrofs.repr 4))=Some(Vptr block offset)) in POINTER.
  injection POINTER as BLOCK OFFSET; subst block offset.
  change (Mem.store Mint32 memory 1%positive 4(Vint(Int.repr 2))=Some final) in STORE.
  unfold nhs_observations,nested_loaded_offset_observations,loaded_offset_observations in OBSERVED |- *.
  cbn [entry_temps entry_memory] in OBSERVED |- *; change (nhs_temps!11%positive) with(Some(Vptr 1%positive Ptrofs.zero)) in OBSERVED |- *.
  cbn -[Mem.loadv] in OBSERVED |- *; rewrite (proj1 same_block_bound_reads) in OBSERVED |- *.
  unfold header_observations_match in OBSERVED |- *; apply Forall_forall; intros observation MEMBER.
  cbn in MEMBER; destruct MEMBER as [SAME|[SAME|BAD]]; [subst observation|subst observation|contradiction].
  all: change (Mem.load Mint32 final 1%positive 0=Some(Vint(Int.repr 2))).
  all: rewrite (@Mem.load_store_other Mint32 memory 1%positive 4(Vint(Int.repr 2)) final STORE Mint32 1%positive 0
    ltac:(right; left; change(0+4<=4); lia)).
  all: rewrite Forall_forall in OBSERVED; apply (OBSERVED (MemoryLocation Mint32 1%positive 0,Vint(Int.repr 2)));
    cbn; left; reflexivity.
Qed.

Theorem nested_adjacent_cached_source_derived fe ge locals :
  exec_stmt fe ge locals nhs_temps lns_initial
    (nested_cached_source 20%positive 31%positive 1%positive 32%positive (dual_unit_store 3%positive))
    E0 nhs_exit nhs_final Out_normal /\
  header_observations_match (nhs_observations (Entry ge locals nhs_temps lns_initial)) nhs_final.
Proof.
  destruct (nhs_snapshots ge locals) as [ROOT CHILD].
  eapply nested_loaded_offset_initial_cached with (pointer:=11%positive) (child_pointer:=11%positive)
    (delta:=Int.repr(-1)) (child_delta:=Int.repr(-1)) (stable:=nhs_stable) (written:=[]);
    try exact ROOT; try exact CHILD; try exact (@nested_adjacent_original_executes fe ge locals); try reflexivity.
  - vm_compute; intuition congruence.
  - vm_compute; intuition congruence.
  - vm_compute; intuition congruence.
  - vm_compute; intuition congruence.
  - vm_compute; intuition congruence.
  - vm_compute; intuition congruence.
  - discriminate.
  - constructor.
  - cbn; tauto.
  - cbn; tauto.
  - intros id MEMBER; cbn; tauto.
  - change(0<=1); lia.
  - change(0<=1); lia.
  - intros i j current before exit last IR JR ROW COLUMN FRAME OBSERVED RUN; eapply nhs_point_preserves; eassumption.
Qed.

Lemma nhs_initial_root_prefix fe ge locals : nhs_root_prefix fe 0 (Entry ge locals nhs_temps lns_initial).
Proof.
  eapply expression_body_prefix_initial with (after:=nhs_exit) (final:=nhs_final).
  - apply nhs_snapshots.
  - exists Int.one; reflexivity.
  - change(0<=1); lia.
  - reflexivity.
  - destruct (nhs_snapshots ge locals) as [FIRST SECOND]; eapply nested_loaded_offset_observations_initial; eassumption.
  - exact (@nested_adjacent_original_executes fe ge locals).
Qed.

Theorem nested_adjacent_open_child_prefix fe ge locals :
  expression_body_prefix fe 1%positive 32%positive nhs_bound (dual_unit_store 3%positive) (20%positive::nhs_stable)
    (fun _=>nhs_ready (Entry ge locals nhs_temps lns_initial))
    (fun _=>nhs_observations (Entry ge locals nhs_temps lns_initial)) 0
    (nested_expression_inner_entry 20%positive 1%positive 0 (Entry ge locals nhs_temps lns_initial)).
Proof.
  pose proof (@nhs_initial_root_prefix fe ge locals) as ROOT.
  eapply nested_expression_prefix_open with (bound:=nhs_bound) (cache:=31%positive) (ready:=nhs_ready) (observations:=nhs_observations); [reflexivity|reflexivity| | | | | | | |exact ROOT|change(0<1); lia].
  - vm_compute; intuition congruence.
  - vm_compute; intuition congruence.
  - discriminate.
  - vm_compute; intuition congruence.
  - exists Int.one; reflexivity.
  - change(0<=1); lia.
  - intros current memory ROW FRAME OBSERVED; destruct (nhs_snapshots ge locals) as [FIRST SECOND].
    eapply nested_loaded_offset_outer_header with (cache:=31%positive) (stable:=nhs_stable)
      (entry:=Entry ge locals nhs_temps lns_initial); try eassumption; [vm_compute; intuition congruence|reflexivity].
Qed.

Theorem nested_adjacent_advance_outer_prefix fe ge locals : nhs_root_prefix fe 1 (Entry ge locals nhs_temps lns_initial).
Proof.
  change 1 with (0+1).
  eapply nested_expression_prefix_advance with (written:=[]) (child_cache:=32%positive);
    [reflexivity|reflexivity| | | | |reflexivity|reflexivity|constructor| | | | | | | | |
     exact (@nhs_initial_root_prefix fe ge locals)|change(0<1); lia].
  - vm_compute; intuition congruence.
  - vm_compute; intuition congruence.
  - discriminate.
  - vm_compute; intuition congruence.
  - cbn; tauto.
  - cbn; tauto.
  - intros id MEMBER; cbn; tauto.
  - intros entry i current memory [ROOT CHILD] RANGE ROW FRAME OBSERVED.
    assert (CACHE : (entry_temps entry)!31%positive=Some(Vint(temp_word 31%positive (entry_temps entry)))).
    { destruct ROOT as [block [offset [raw [POINTER [READ WORD]]]]]; unfold temp_word; rewrite WORD; reflexivity. }
    eapply nested_loaded_offset_outer_header with (cache:=31%positive) (stable:=nhs_stable);
      try eassumption; vm_compute; intuition congruence.
  - exists Int.one; reflexivity.
  - change(0<=1); lia.
  - intros j current memory RANGE ROW COLUMN FRAME OBSERVED; destruct (nhs_snapshots ge locals) as [ROOT CHILD].
    eapply nested_loaded_offset_child_header with (child_cache:=32%positive) (stable:=nhs_stable)
      (entry:=Entry ge locals nhs_temps lns_initial); try eassumption; [vm_compute; intuition congruence|reflexivity].
  - intros j current memory after final RANGE ROW COLUMN FRAME OBSERVED RUN; eapply nhs_point_preserves; eassumption.
Qed.

Theorem nested_adjacent_point_check_accepts ge locals :
  decision_run (Entry ge locals nhs_temps lns_initial)
    (word_address_separation (signed_pointer_temp 3%positive) 11%positive) true.
Proof.
  assert (TEST : expression_test (word_address_equal (signed_pointer_temp 3%positive) 11%positive)
    (Entry ge locals nhs_temps lns_initial) false).
  { change false with (address_flag 1%positive (Ptrofs.repr 4) 1%positive Ptrofs.zero).
    eapply word_address_equality_test; [reflexivity|constructor; reflexivity|reflexivity| |exact(proj1 same_block_bound_reads)].
    exact (@Mem.store_valid_access_3 Mint32 lns_initial 1%positive 4(Vint(Int.repr 2)) nhs_final(proj2_sig nhs_final_state)). }
  unfold word_address_separation; eapply run_test with (b:=false); [exact TEST|constructor].
Qed.

Print Assumptions nhs_final_bound_read.
Print Assumptions nhs_snapshots.
Print Assumptions nested_adjacent_original_executes.
Print Assumptions nhs_point_preserves.
Print Assumptions nested_adjacent_cached_source_derived.
Print Assumptions nested_adjacent_open_child_prefix.
Print Assumptions nested_adjacent_advance_outer_prefix.
Print Assumptions nested_adjacent_point_check_accepts.
