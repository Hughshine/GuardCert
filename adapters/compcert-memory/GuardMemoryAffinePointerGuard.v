From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightPureExpr ClightRedundantSet ClightNoWrap ClightRectangularGuard
  ClightCountedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryRecursiveSource
  GuardMemoryRecursiveGuard GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerProjectedCandidate
  GuardMemoryLinearPointerSyntax GuardMemoryLinearPointerPair GuardMemoryMultiPointerCells GuardMemoryPointerRangeScan
  GuardMemoryLoopGuardFrame GuardMemoryBooleanScan GuardMemoryProjectedCondition GuardMemorySequentialCondition
  GuardMemoryFootprintCapabilities.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

From GuardMemory Require Import GuardMemoryAffinePointerSyntax GuardMemoryAffinePointerPairs
  GuardMemoryAffinePointerScan GuardMemoryAffinePointerFrame.

Definition memory_affine_pointer_scan_statement source (package : memory_affine_pointer_package source) x y flag :=
  Ssequence (Sset flag (Econst_int Int.one type_int32s))
    (Ssequence (memory_affine_access_pairs_statement x y flag (affine_pointer_bound package)
      (memory_affine_access_pairs (memory_linear_pointer_accesses (multi_pointer_region_code (affine_pointer_region package)))))
      (Sifthenelse (Etempvar flag type_int32s) Sskip Sbreak)).
Definition memory_affine_pointer_guard_statement source (package : memory_affine_pointer_package source) x y flag :=
  Ssequence (tree_statement (memory_recursive_guard_tree
    (multi_pointer_region_limit (affine_pointer_region package)) []
    (multi_pointer_region_nest (affine_pointer_region package))) Sskip Sbreak)
    (memory_affine_pointer_scan_statement package x y flag).

Theorem memory_affine_pointer_guard_execution source (package : memory_affine_pointer_package source)
  fe s live x y flag :
  NoDup [x;y;flag;affine_pointer_bound package] ->
  ~ In x (memory_affine_pointer_guard_protected package live) ->
  ~ In y (memory_affine_pointer_guard_protected package live) ->
  ~ In flag (memory_affine_pointer_guard_protected package live) ->
  memory_multi_pointer_runtime_domain (affine_pointer_region package) s ->
  exists accepted checked,
    memory_projected_check_execution fe s live (memory_affine_pointer_guard_statement package x y flag) accepted checked /\
    (accepted = true -> memory_multi_pointer_runtime_presumption
      (affine_pointer_region package)
      (Entry (entry_ge s) (entry_env s) checked (entry_memory s))).
Proof.
  intros UNIQUE XFRESH YFRESH FFRESH [DOMAIN CAPABLE]; destruct s as [ge locals temps memory].
  set (region := affine_pointer_region package) in *.
  set (protected := memory_affine_pointer_guard_protected package live) in *.
  set (counts := memory_recursive_guard_accept (multi_pointer_region_limit region) [] (multi_pointer_region_nest region)
    (Entry ge locals temps memory)).
  assert (COUNT_RUN : memory_check_statement_execution fe (Entry ge locals temps memory)
    (tree_statement (memory_recursive_guard_tree (multi_pointer_region_limit region) [] (multi_pointer_region_nest region)) Sskip Sbreak) counts).
  { apply memory_decision_check_statement; apply (proj2 (@memory_recursive_guard_exact _ _ _ _ DOMAIN counts)); reflexivity. }
  destruct counts eqn:COUNT.
  - assert (COUNT_ACCEPT : memory_recursive_guard_accept (multi_pointer_region_limit region) [] (multi_pointer_region_nest region)
      (Entry ge locals temps memory) = true) by exact COUNT.
    destruct (@memory_recursive_guard_sound _ _ _ _ (proj2 (multi_pointer_region_cap (multi_pointer_region_syntax region))) DOMAIN COUNT_ACCEPT)
      as [INITIAL [RANGES ARRAYS]].
    change (Forall (fun bound => register_range bound (multi_pointer_region_limit region) (Entry ge locals temps memory))
      (memory_nest_bounds (multi_pointer_region_nest region))) in RANGES.
    unfold region in RANGES; rewrite (affine_pointer_one_bound package) in RANGES.
    inversion RANGES as [|bound rest RANGE _]; subst.
    destruct RANGE as [[word WORD] POS].
    cbn [entry_temps] in WORD; unfold temp_word in POS; cbn [entry_temps] in POS; rewrite WORD in POS.
    set (count := Int.signed word) in *.
    assert (SIGNED : signed_range count) by (unfold count,signed_range; apply Int.signed_range).
    assert (BOUND : temps ! (affine_pointer_bound package) = Some (Vint (Int.repr count)))
      by (unfold count; rewrite Int.repr_signed; exact WORD).
    specialize (CAPABLE COUNT_ACCEPT).
    set (initialized := PTree.set flag (Vint Int.one) temps).
    assert (INIT_FRAME : temp_agree protected temps initialized) by (apply temp_agree_set; exact FFRESH).
    assert (EXPAND_FRESH : forall identifier, ~ In identifier protected ->
      ~ In identifier (multi_pointer_region_pointers region++protected)).
    { intros identifier FRESH MEMBER; apply FRESH; apply in_app_or in MEMBER as [MEMBER|MEMBER]; [|exact MEMBER].
      unfold protected; apply memory_affine_pointer_protected_pointer; exact MEMBER. }
    assert (INIT_POINTERS : temp_agree (multi_pointer_region_pointers region++protected) temps initialized).
    { intros identifier MEMBER; apply INIT_FRAME; apply in_app_or in MEMBER as [MEMBER|MEMBER]; [|exact MEMBER].
      unfold protected; apply memory_affine_pointer_protected_pointer; exact MEMBER. }
    assert (INIT_BOUND : initialized ! (affine_pointer_bound package) = Some (Vint (Int.repr count))).
    { rewrite INIT_FRAME by apply memory_affine_pointer_protected_bound; exact BOUND. }
    assert (INIT_FLAG : initialized ! flag = Some (memory_boolean_word true)) by (unfold initialized; apply PTree.gss).
    assert (PAIRS : memory_affine_pointer_pairs_valid package
      (memory_affine_access_pairs (memory_linear_pointer_accesses (multi_pointer_region_code region)))).
    { apply Forall_forall; intros [first second] MEMBER; apply memory_affine_access_pair_member in MEMBER; exact MEMBER. }
    destruct (@memory_affine_access_pairs_execution source package fe ge locals temps memory count protected x y flag
      (memory_affine_access_pairs (memory_linear_pointer_accesses (multi_pointer_region_code region)))
      ltac:(lia) SIGNED BOUND UNIQUE (EXPAND_FRESH _ XFRESH) (EXPAND_FRESH _ YFRESH) (EXPAND_FRESH _ FFRESH)
      CAPABLE PAIRS initialized true INIT_POINTERS INIT_BOUND INIT_FLAG) as [checked [SCAN [FRAME FLAG]]].
    set (accepted := memory_affine_pointer_pairs_check package (memory_multi_pointer_locations temps (multi_pointer_region_window region)) count) in *.
    cbn [andb] in FLAG.
    assert (PUBLIC : temp_agree protected temps checked).
    { eapply temp_agree_trans; [exact INIT_FRAME|].
      eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER; right; apply in_or_app; right; exact MEMBER. }
    assert (FINAL_TEST : expression_test (Etempvar flag type_int32s) (Entry ge locals checked memory) accepted).
    { exists (memory_boolean_word accepted); split; [constructor; exact FLAG|destruct accepted; reflexivity]. }
    exists accepted,checked; split.
    + split.
      * unfold memory_affine_pointer_guard_statement,memory_affine_pointer_scan_statement.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact COUNT_RUN|].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor; constructor|].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact SCAN|].
        destruct FINAL_TEST as [value [EVAL BOOL]]; unfold memory_check_outcome;
          eapply exec_Sifthenelse; [exact EVAL|exact BOOL|destruct accepted; constructor].
      * eapply temp_agree_weaken; [|exact PUBLIC]; intros identifier MEMBER; unfold protected,memory_affine_pointer_guard_protected;
        repeat (apply in_or_app; right); exact MEMBER.
    + intro ACCEPT; split.
      * rewrite (@memory_recursive_guard_accept_temp_frame _ _ ge locals memory temps checked); [exact COUNT_ACCEPT|].
        eapply temp_agree_weaken; [|exact PUBLIC]; intros identifier MEMBER; unfold protected,memory_affine_pointer_guard_protected.
        apply in_app_or in MEMBER as [MEMBER|MEMBER]; [apply in_or_app; left; exact MEMBER|].
        apply in_or_app; right; apply in_or_app; left; unfold memory_multi_pointer_runtime_context; apply in_or_app; left; exact MEMBER.
      * eapply (@memory_affine_pointer_pairs_separation source package ge locals checked memory count);
          [lia|exact SIGNED| | |].
        -- rewrite PUBLIC by apply memory_affine_pointer_protected_bound; exact BOUND.
        -- eapply memory_affine_pointer_capabilities_frame; [exact BOUND|exact SIGNED|exact PUBLIC|exact CAPABLE].
        -- change (memory_affine_pointer_pairs_check package
             (memory_multi_pointer_locations checked (multi_pointer_region_window region)) count = true).
           unfold region; rewrite (@memory_affine_pointer_pairs_check_frame source package temps checked count); [exact ACCEPT|].
           eapply temp_agree_weaken; [|exact PUBLIC]; intros identifier MEMBER; unfold protected.
           apply memory_affine_pointer_protected_pointer; exact MEMBER.
  - exists false,temps; split; [split|discriminate].
    + unfold memory_affine_pointer_guard_statement; eapply exec_Sseq_2; [exact COUNT_RUN|discriminate].
    + apply temp_agree_refl.
Qed.

Print Assumptions memory_affine_pointer_guard_execution.
