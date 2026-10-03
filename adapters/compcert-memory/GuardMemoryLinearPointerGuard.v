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

Definition memory_linear_pointer_guard_protected source (package : memory_linear_pointer_pair_package source) live :=
  memory_nest_iterators (multi_pointer_region_nest (linear_pointer_region (linear_pointer_pair_region package))) ++
  memory_multi_pointer_runtime_context (linear_pointer_region (linear_pointer_pair_region package)) ++
  [linear_pointer_pair_first package;linear_pointer_pair_second package] ++ live.

Definition memory_linear_pointer_scan_statement source (package : memory_linear_pointer_pair_package source) x y flag :=
  Ssequence (Sset flag (Econst_int Int.one type_int32s))
    (Ssequence (memory_pointer_range_pair_statement x y flag
      (linear_pointer_bound (linear_pointer_pair_region package)) (linear_pointer_pair_first package) (linear_pointer_pair_second package))
      (Sifthenelse (Etempvar flag type_int32s) Sskip Sbreak)).
Definition memory_linear_pointer_guard_statement source (package : memory_linear_pointer_pair_package source) x y flag :=
  Ssequence (tree_statement (memory_recursive_guard_tree
    (multi_pointer_region_limit (linear_pointer_region (linear_pointer_pair_region package))) []
    (multi_pointer_region_nest (linear_pointer_region (linear_pointer_pair_region package)))) Sskip Sbreak)
    (memory_linear_pointer_scan_statement package x y flag).

Lemma memory_linear_pointer_protected_first source (package : memory_linear_pointer_pair_package source) live :
  In (linear_pointer_pair_first package) (memory_linear_pointer_guard_protected package live).
Proof. unfold memory_linear_pointer_guard_protected; apply in_or_app; right; apply in_or_app; right; cbn; auto. Qed.
Lemma memory_linear_pointer_protected_second source (package : memory_linear_pointer_pair_package source) live :
  In (linear_pointer_pair_second package) (memory_linear_pointer_guard_protected package live).
Proof. unfold memory_linear_pointer_guard_protected; apply in_or_app; right; apply in_or_app; right; cbn; auto. Qed.
Lemma memory_linear_pointer_protected_bound source (package : memory_linear_pointer_pair_package source) live :
  In (linear_pointer_bound (linear_pointer_pair_region package)) (memory_linear_pointer_guard_protected package live).
Proof.
  unfold memory_linear_pointer_guard_protected; apply in_or_app; right; apply in_or_app; left.
  unfold memory_multi_pointer_runtime_context; apply in_or_app; left; rewrite (linear_pointer_one_bound (linear_pointer_pair_region package)); cbn; auto.
Qed.

Lemma memory_linear_pointer_footprint_capabilities_frame source (package : memory_linear_pointer_pair_package source)
  original current memory count live :
  original ! (linear_pointer_bound (linear_pointer_pair_region package)) = Some (Vint (Int.repr count)) -> signed_range count ->
  temp_agree (memory_linear_pointer_guard_protected package live) original current ->
  Forall (memory_cell_capable (memory_multi_pointer_locations original
    (multi_pointer_region_window (linear_pointer_region (linear_pointer_pair_region package)))) memory)
    (memory_multi_pointer_runtime_footprint (linear_pointer_region (linear_pointer_pair_region package)) original) ->
  Forall (memory_cell_capable (memory_multi_pointer_locations current
    (multi_pointer_region_window (linear_pointer_region (linear_pointer_pair_region package)))) memory)
    (memory_multi_pointer_runtime_footprint (linear_pointer_region (linear_pointer_pair_region package)) current).
Proof.
  intros BOUND RANGE FRAME CELLS.
  assert (CONTEXT : temp_agree (memory_multi_pointer_runtime_context (linear_pointer_region (linear_pointer_pair_region package))) original current).
  { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER; unfold memory_linear_pointer_guard_protected;
    apply in_or_app; right; apply in_or_app; left; exact MEMBER. }
  rewrite (@memory_multi_pointer_runtime_footprint_temp_frame _ _ original current CONTEXT).
  apply Forall_forall; intros cell MEMBER.
  pose proof MEMBER as ACCESS; apply (proj1 (@memory_linear_pointer_footprint_member source
    (linear_pointer_pair_region package) original count cell BOUND RANGE)) in ACCESS as [identifier [index [ID [INDEX ->]]]].
  apply memory_linear_pointer_pair_identifier_member in ID.
  apply Forall_forall with (x := point_cell identifier index) in CELLS; [|exact MEMBER].
  destruct CELLS as [location [RESOLVE REST]]; exists location; split; [|exact REST].
  unfold memory_multi_pointer_locations in *; cbn [point_cell arr_id] in *.
  destruct ID as [SAME_FIRST | SAME_SECOND]; subst identifier; rewrite FRAME by
    (first [apply memory_linear_pointer_protected_first|apply memory_linear_pointer_protected_second]); exact RESOLVE.
Qed.

Theorem memory_linear_pointer_guard_execution source (package : memory_linear_pointer_pair_package source)
  fe s live x y flag :
  NoDup [x;y;flag;linear_pointer_bound (linear_pointer_pair_region package)] ->
  ~ In x (memory_linear_pointer_guard_protected package live) ->
  ~ In y (memory_linear_pointer_guard_protected package live) ->
  ~ In flag (memory_linear_pointer_guard_protected package live) ->
  memory_multi_pointer_runtime_domain (linear_pointer_region (linear_pointer_pair_region package)) s ->
  exists accepted checked,
    memory_projected_check_execution fe s live (memory_linear_pointer_guard_statement package x y flag) accepted checked /\
    (accepted = true -> memory_multi_pointer_runtime_presumption
      (linear_pointer_region (linear_pointer_pair_region package))
      (Entry (entry_ge s) (entry_env s) checked (entry_memory s))).
Proof.
  intros UNIQUE XFRESH YFRESH FFRESH [DOMAIN CAPABLE]; destruct s as [ge locals temps memory].
  set (region := linear_pointer_region (linear_pointer_pair_region package)) in *.
  set (protected := memory_linear_pointer_guard_protected package live) in *.
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
    unfold region in RANGES; rewrite (linear_pointer_one_bound (linear_pointer_pair_region package)) in RANGES.
    inversion RANGES as [|bound rest RANGE _]; subst.
    destruct RANGE as [[word WORD] POS].
    cbn [entry_temps] in WORD; unfold temp_word in POS; cbn [entry_temps] in POS; rewrite WORD in POS.
    set (count := Int.signed word) in *.
    assert (SIGNED : signed_range count) by (unfold count,signed_range; apply Int.signed_range).
    assert (BOUND : temps ! (linear_pointer_bound (linear_pointer_pair_region package)) = Some (Vint (Int.repr count)))
      by (unfold count; rewrite Int.repr_signed; exact WORD).
    specialize (CAPABLE COUNT_ACCEPT).
    pose proof (@memory_linear_pointer_pair_capabilities source package temps memory count BOUND SIGNED CAPABLE) as CELLS.
    set (initialized := PTree.set flag (Vint Int.one) temps).
    assert (INIT_FRAME : temp_agree protected temps initialized) by (apply temp_agree_set; exact FFRESH).
    assert (EXPAND_FRESH : forall identifier, ~ In identifier protected ->
      ~ In identifier (linear_pointer_pair_first package::linear_pointer_pair_second package::protected)).
    { intros identifier FRESH; cbn; intros [SAME|[SAME|MEMBER]]; apply FRESH;
      [subst; apply memory_linear_pointer_protected_first|subst; apply memory_linear_pointer_protected_second|exact MEMBER]. }
    assert (INIT_POINTERS : temp_agree (linear_pointer_pair_first package::linear_pointer_pair_second package::protected) temps initialized).
    { intros identifier MEMBER; apply INIT_FRAME; cbn in MEMBER; destruct MEMBER as [<-|[<-|MEMBER]];
      [apply memory_linear_pointer_protected_first|apply memory_linear_pointer_protected_second|exact MEMBER]. }
    assert (INIT_BOUND : initialized ! (linear_pointer_bound (linear_pointer_pair_region package)) = Some (Vint (Int.repr count))).
    { rewrite INIT_FRAME by apply memory_linear_pointer_protected_bound; exact BOUND. }
    assert (INIT_FLAG : initialized ! flag = Some (memory_boolean_word true)) by (unfold initialized; apply PTree.gss).
    destruct (@memory_pointer_range_pair_execution fe ge locals temps initialized memory (multi_pointer_region_window region)
      (linear_pointer_pair_first package) (linear_pointer_pair_second package) x y flag
      (linear_pointer_bound (linear_pointer_pair_region package)) protected count true
      (linear_pointer_pair_distinct package) (proj1 (proj2 (multi_pointer_region_extent (multi_pointer_region_syntax region))))
      ltac:(lia) SIGNED UNIQUE (EXPAND_FRESH _ XFRESH) (EXPAND_FRESH _ YFRESH) (EXPAND_FRESH _ FFRESH)
      INIT_POINTERS INIT_BOUND INIT_FLAG CELLS) as [checked [SCAN [FRAME FLAG]]].
    set (accepted := memory_pointer_range_pair_check (memory_multi_pointer_locations temps (multi_pointer_region_window region)) count
      (linear_pointer_pair_first package) (linear_pointer_pair_second package)) in *.
    cbn [andb] in FLAG.
    assert (PUBLIC : temp_agree protected temps checked).
    { eapply temp_agree_trans; [exact INIT_FRAME|].
      eapply temp_agree_weaken; [|exact FRAME]; cbn; auto. }
    assert (FINAL_TEST : expression_test (Etempvar flag type_int32s) (Entry ge locals checked memory) accepted).
    { exists (memory_boolean_word accepted); split; [constructor; exact FLAG|destruct accepted; reflexivity]. }
    exists accepted,checked; split.
    + split.
      * unfold memory_linear_pointer_guard_statement,memory_linear_pointer_scan_statement.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact COUNT_RUN|].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor; constructor|].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact SCAN|].
        destruct FINAL_TEST as [value [EVAL BOOL]]; unfold memory_check_outcome;
          eapply exec_Sifthenelse; [exact EVAL|exact BOOL|destruct accepted; constructor].
      * eapply temp_agree_weaken; [|exact PUBLIC]; intros identifier MEMBER; unfold protected,memory_linear_pointer_guard_protected;
        repeat (apply in_or_app; right); exact MEMBER.
    + intro ACCEPT; split.
      * rewrite (@memory_recursive_guard_accept_temp_frame _ _ ge locals memory temps checked); [exact COUNT_ACCEPT|].
        eapply temp_agree_weaken; [|exact PUBLIC]; intros identifier MEMBER; unfold protected,memory_linear_pointer_guard_protected.
        apply in_app_or in MEMBER as [MEMBER|MEMBER]; [apply in_or_app; left; exact MEMBER|].
        apply in_or_app; right; apply in_or_app; left; unfold memory_multi_pointer_runtime_context; apply in_or_app; left; exact MEMBER.
      * eapply (@memory_linear_pointer_pair_separation source package ge locals checked memory count);
          [lia|exact SIGNED| | |].
        -- rewrite PUBLIC by apply memory_linear_pointer_protected_bound; exact BOUND.
        -- eapply memory_linear_pointer_footprint_capabilities_frame; [exact BOUND|exact SIGNED|exact PUBLIC|exact CAPABLE].
        -- change (memory_pointer_range_pair_check (memory_multi_pointer_locations checked (multi_pointer_region_window region)) count
             (linear_pointer_pair_first package) (linear_pointer_pair_second package) = true).
           rewrite (@memory_pointer_range_pair_check_frame temps checked (multi_pointer_region_window region) count
            (linear_pointer_pair_first package) (linear_pointer_pair_second package)); [exact ACCEPT|].
           eapply temp_agree_weaken; [|exact PUBLIC]; intros identifier MEMBER; cbn in MEMBER;
             destruct MEMBER as [<-|[<-|[]]]; [apply memory_linear_pointer_protected_first|apply memory_linear_pointer_protected_second].
  - exists false,temps; split; [split|discriminate].
    + unfold memory_linear_pointer_guard_statement; eapply exec_Sseq_2; [exact COUNT_RUN|discriminate].
    + apply temp_agree_refl.
Qed.

Print Assumptions memory_linear_pointer_guard_execution.
