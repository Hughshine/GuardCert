From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap ClightCountedLoop ClightRedundantSet
  ClightTempFootprint ClightRectangularGuard CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryBooleanScan GuardMemoryWindowParameterGuard GuardMemoryIntervalGuard.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestPackageGuard
  AffineNestScanNamespace.
From GuardInterface Require Import ClightSharedGuard ClightMaterializedCheck ClightQuietDeterminacy ClightLoadedBoundSyntax
  ClightLoadedSnapshotInsertion ClightLoadedAffineFirstPath ClightAffineFirstBodyReceipt ClightLoadedBodyPrefix
  ClightLoadedAffineNumericGuard ClightLoadedAffineNumericSite ClightLoadedAffineBodyDomain ClightLoadedAffineBodyPrefix
  ClightLoadedAffineRootScan ClightLoadedAffineScanSite ClightAffineNestMaterialized
  ClightLoadedAffineScanExecution ClightLoadedOffsetHeader ClightExpressionHeaderCapture
  ClightExpressionAffineNumericSite ClightLoadedOffsetAffineBody ClightLoadedOffsetAffineRootScan
  ClightLoadedOffsetAffineScanSite.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition offset_affine_scan_flag parameters proposal pointer delta entry :=
  match (entry_temps entry)!pointer with
  | Some(Vptr block offset)=>match Mem.loadv Mint32(entry_memory entry)(Vptr block offset) with
    | Some(Vint raw)=>let prepared:=loaded_affine_scan_prepared proposal entry (Int.add raw delta) in
        affine_package_guard_flag parameters proposal prepared &&
        (loaded_affine_scan_gate_flag proposal prepared && affine_loaded_root_scan_result proposal prepared
          (MemoryLocation Mint32 block(Ptrofs.unsigned offset)))
    | _=>false end
  | _=>false end.
Definition offset_affine_scan_presumption fe parameters proposal pointer delta entry :=
  exists upper, let prepared:=loaded_affine_scan_prepared proposal entry upper in
    loaded_offset_cached_header pointer delta (affine_proposed_bound proposal) prepared /\
    affine_loaded_numeric_premise parameters proposal prepared /\
    (entry_temps prepared)!(affine_proposed_iterator proposal)=Some(Vint Int.zero) /\
    0<=Int.signed(temp_word(affine_proposed_bound proposal)(entry_temps prepared)) /\
    forall index, 0<=index<Int.signed(temp_word(affine_proposed_bound proposal)(entry_temps prepared)) ->
      offset_affine_body_preserved fe parameters proposal pointer index prepared.

Theorem offset_affine_scan_site_execution source parameters live proposal pointer delta
  (site : offset_affine_scan_site source parameters live proposal pointer delta) fe ge locals temps memory source_after final :
  exec_stmt fe ge locals temps memory source E0 source_after final Out_normal ->
  exists after,
    exec_stmt fe ge locals temps memory(offset_affine_scan_body(offset_scan_numeric site)) E0 after memory Out_normal /\
    temp_agree live temps after /\
    after!(affine_proposed_result proposal)=Some(memory_boolean_word
      (offset_affine_scan_flag parameters proposal pointer delta(Entry ge locals temps memory))) /\
    (offset_affine_scan_flag parameters proposal pointer delta(Entry ge locals temps memory)=true ->
      offset_affine_scan_presumption fe parameters proposal pointer delta(Entry ge locals temps memory)).
Proof.
  intro SOURCE.
  pose proof(expression_numeric_private(offset_scan_numeric site)) as PRIVATE.
  pose proof(expression_numeric_frameable(offset_scan_numeric site)) as FRAMEABLE.
  rewrite(expression_numeric_exact(offset_scan_numeric site)) in SOURCE,PRIVATE,FRAMEABLE.
  set(package:=expression_numeric_package(offset_scan_numeric site)).
  destruct(affine_loaded_numeric_body_properties package) as [NORMAL QUIET].
  destruct(@signed_expression_capture_receipt fe ge locals temps memory(affine_proposed_iterator proposal) (signed_load_offset pointer delta)
    (affine_proposed_body proposal)(affine_proposed_bound proposal) live source_after final eq_refl NORMAL QUIET FRAMEABLE PRIVATE SOURCE)
    as [upper [prepared_after [CAPTURE [PREPARED [SOURCE_FRAME [RECEIPT EVAL]]]]]].
  set(prepared:=PTree.set(affine_proposed_bound proposal)(Vint upper) temps).
  destruct(signed_load_offset_inv EVAL) as [block [offset [raw [POINTER [READ UPPER]]]]].
  assert(POINTER_FRESH:pointer<>affine_proposed_bound proposal).
  { intro SAME; apply PRIVATE,in_or_app; left; rewrite <-SAME; apply(signed_expression_bound_in_scope (affine_proposed_iterator proposal) (signed_load_offset pointer delta) (affine_proposed_body proposal));
    change(pointer=pointer \/ False); left; reflexivity. }
  assert(PREPARED_POINTER:prepared!pointer=Some(Vptr block offset)).
  { unfold prepared; rewrite PTree.gso by exact POINTER_FRESH; exact POINTER. }
  assert(SNAPSHOT:loaded_offset_cached_header pointer delta (affine_proposed_bound proposal)(Entry ge locals prepared memory)).
  { exists block,offset,raw; split; [exact PREPARED_POINTER|split; [exact READ|rewrite <-UPPER; apply PTree.gss]]. }
  destruct(@affine_receipted_package_guard_execution _ parameters _ proposal package fe ge locals prepared memory RECEIPT)
    as [numeric_after [NUMERIC [FRAME [RESULT MATH]]]].
  destruct(loaded_affine_scan_ports_inclusions parameters proposal live) as [PARAMETERS ROOT_LIVE].
  assert(POINTERS:incl(pointer::affine_proposed_pointers proposal)(loaded_affine_scan_ports parameters proposal live)).
  { intros identifier MEMBER; apply ROOT_LIVE; right; right; exact(offset_scan_pointer_ports site MEMBER). }
  assert(CACHE_LIVE:In(affine_proposed_bound proposal)(loaded_affine_scan_ports parameters proposal live))
    by(apply ROOT_LIVE; right; left; reflexivity).
  assert(PUBLIC:temp_agree live temps numeric_after).
  { eapply temp_agree_trans with(le1:=prepared).
    - apply temp_agree_set; intro MEMBER; apply PRIVATE,in_or_app; right; exact MEMBER.
    - eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER; apply ROOT_LIVE; right; right; exact MEMBER. }
  assert(RESULT_PRIVATE:~In(affine_proposed_result proposal) live).
  { intro MEMBER; apply(affine_scan_names_flag_private(offset_scan_namespace site)),in_or_app; right.
    apply ROOT_LIVE; right; right; exact MEMBER. }
  destruct(@shared_guard_choice_test ge locals numeric_after memory(affine_proposed_result proposal)
    (affine_package_guard_flag parameters proposal(Entry ge locals prepared memory)) RESULT)
    as [value [RESULT_EVAL RESULT_BOOL]].
  assert(FLAG:offset_affine_scan_flag parameters proposal pointer delta(Entry ge locals temps memory)=
    affine_package_guard_flag parameters proposal(Entry ge locals prepared memory) &&
      (loaded_affine_scan_gate_flag proposal(Entry ge locals prepared memory) &&
        affine_loaded_root_scan_result proposal(Entry ge locals prepared memory)(MemoryLocation Mint32 block(Ptrofs.unsigned offset)))).
  { unfold offset_affine_scan_flag; cbn [entry_temps entry_memory]; rewrite POINTER,READ,<-UPPER; reflexivity. }
  assert(NUMERIC_BODY:exec_stmt fe ge locals temps memory(expression_numeric_check_code(offset_scan_numeric site))
    E0 numeric_after memory Out_normal).
  { unfold expression_numeric_check_code.
    destruct(@describe_materialized_check_exact _ _ _ (expression_numeric_describe(offset_scan_numeric site))) as [BODY CONDITION].
    rewrite BODY; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); eassumption. }
  destruct(affine_package_guard_flag parameters proposal(Entry ge locals prepared memory)) eqn:ACCEPT_NUMERIC.
  - destruct RECEIPT as [ROW_DOMAIN [CACHE_DOMAIN RECEIPT]].
    assert(GATE_DOMAINS:Forall(fun identifier=>register_domain identifier(Entry ge locals numeric_after memory))
      [affine_proposed_iterator proposal;affine_proposed_bound proposal]).
    { constructor; [|constructor; [|constructor]].
      - destruct ROW_DOMAIN as [word WORD]; exists word; cbn [entry_temps]; rewrite FRAME; [exact WORD|apply ROOT_LIVE; left; reflexivity].
      - exists upper; cbn [entry_temps]; rewrite FRAME by exact CACHE_LIVE; apply PTree.gss. }
    assert(GATE:decision_run(Entry ge locals numeric_after memory)(loaded_affine_scan_gate proposal)
      (loaded_affine_scan_gate_flag proposal(Entry ge locals prepared memory))).
    { unfold loaded_affine_scan_gate.
      apply(proj2(@window_parameters_encoding_exact [(0,1);(0,2147483648)]
        [affine_proposed_iterator proposal;affine_proposed_bound proposal](Decision true)
        (Entry ge locals numeric_after memory) true GATE_DOMAINS
        ltac:(intro flag; split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor]) _)).
      rewrite andb_true_r; symmetry; apply loaded_affine_scan_gate_frame.
      eapply temp_agree_weaken; [|exact FRAME].
      intros identifier [SAME|[SAME|BAD]]; [subst; apply ROOT_LIVE; left; reflexivity|subst; exact CACHE_LIVE|contradiction]. }
    destruct(loaded_affine_scan_gate_flag proposal(Entry ge locals prepared memory)) eqn:ACCEPT_GATE.
    + destruct(@loaded_affine_scan_gate_sound proposal(Entry ge locals prepared memory) ROW_DOMAIN ACCEPT_GATE) as [ROW NONNEGATIVE].
      assert(NUMERIC_PREMISE:affine_loaded_numeric_premise parameters proposal(Entry ge locals prepared memory))
        by(split; [exact ACCEPT_NUMERIC|apply MATH; reflexivity]).
      pose proof(@offset_affine_body_initial_prefix _ parameters _ proposal pointer delta package fe ge locals prepared memory
        prepared_after final SNAPSHOT NUMERIC_PREMISE ROW NONNEGATIVE PREPARED) as PREFIX.
      destruct(@offset_affine_root_scan_execution _ parameters _ proposal package pointer delta(offset_scan_body_names site) fe
        (Entry ge locals prepared memory)(offset_scan_child_code site)(offset_scan_child_lower site)
        block offset PREPARED_POINTER(affine_proposal_rename proposal)(affine_proposed_result proposal)
        (loaded_affine_scan_ports parameters proposal live)(offset_scan_namespace site) numeric_after
        PREFIX PARAMETERS POINTERS CACHE_LIVE FRAME) as [after [SCAN [SCAN_FRAME [SCAN_RESULT PRESERVE]]]].
      exists after; split.
      * unfold offset_affine_scan_body,loaded_affine_scan_tail.
        eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact NUMERIC_BODY|].
        eapply exec_Sifthenelse with(b:=true); [exact RESULT_EVAL|exact RESULT_BOOL|].
        eapply decision_fragment_run; [exact GATE|exact SCAN].
      * split.
        -- eapply temp_agree_trans; [exact PUBLIC|eapply temp_agree_weaken; [|exact SCAN_FRAME]].
           intros identifier MEMBER; apply ROOT_LIVE; right; right; exact MEMBER.
        -- split; [rewrite FLAG; cbn [andb]; exact SCAN_RESULT|].
           rewrite FLAG; cbn [andb]; intro ACCEPT.
           exists upper; split; [exact SNAPSHOT|split; [exact NUMERIC_PREMISE|split; [exact ROW|split; [exact NONNEGATIVE|]]]].
           apply PRESERVE; exact ACCEPT.
    + set(after:=PTree.set(affine_proposed_result proposal)(Vint Int.zero) numeric_after).
      exists after; split.
      * unfold offset_affine_scan_body,loaded_affine_scan_tail.
        eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact NUMERIC_BODY|].
        eapply exec_Sifthenelse with(b:=true); [exact RESULT_EVAL|exact RESULT_BOOL|].
        eapply decision_fragment_run; [exact GATE|constructor; constructor].
      * split; [eapply temp_agree_trans; [exact PUBLIC|apply temp_agree_set; exact RESULT_PRIVATE]|split].
        -- rewrite FLAG; cbn [andb]; apply PTree.gss.
        -- rewrite FLAG; discriminate.
  - exists numeric_after; split.
    + unfold offset_affine_scan_body,loaded_affine_scan_tail.
      eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact NUMERIC_BODY|].
      eapply exec_Sifthenelse with(b:=false); [exact RESULT_EVAL|exact RESULT_BOOL|constructor].
    + split; [exact PUBLIC|split; [rewrite FLAG; exact RESULT|rewrite FLAG; discriminate]].
Qed.

Print Assumptions offset_affine_scan_site_execution.
