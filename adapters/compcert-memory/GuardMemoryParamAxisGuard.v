From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightPureExpr ClightNoWrap ClightRectangularGuard
  ClightCountedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryRecursiveSource
  GuardMemoryRecursiveGuard GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerProjectedCandidate
  GuardMemoryLinearPointerSyntax GuardMemoryMultiPointerCells GuardMemoryLoopGuardFrame GuardMemoryBooleanScan
  GuardMemoryProjectedCondition GuardMemorySequentialCondition GuardMemoryFootprintCapabilities GuardMemoryAffinePointerPairs.
From GuardMemory Require Import GuardMemoryAxisPointerFootprint GuardMemoryAxisPointerPairs
  GuardMemoryAxisPointerScan GuardMemoryAxisPointerFrame.
From GuardMemory Require Import GuardMemoryVectorBounds GuardMemoryVectorGuard GuardMemoryScalarPointerBody GuardMemoryRecursiveDomain.
From GuardMemory Require Import GuardMemoryParamPointerHeader GuardMemoryParamPointerSyntax GuardMemoryParamPointerProjectedCandidate GuardMemoryParamAxisFootprint GuardMemoryParamAxisPairs GuardMemoryParamAxisScan GuardMemoryParamAxisFrame GuardMemoryParamRuntimeFrame.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_param_axis_pointer_bound_values caps bounds ge locals temps memory :
  Forall2 (fun cap bound => register_range bound cap (Entry ge locals temps memory)) caps bounds ->
  exists counts,
    memory_nest_bindings bounds counts temps /\ Forall (fun count => 0 <= count /\ signed_range count) counts.
Proof.
  intro RANGES; induction RANGES as [|cap bound caps bounds [[word WORD] POS] REST IH].
  - exists []; split; constructor.
  - destruct IH as [counts [WORDS RANGES]].
    cbn [entry_temps] in WORD.
    exists (Int.signed word::counts); split.
    + constructor; [rewrite Int.repr_signed; exact WORD|exact WORDS].
    + constructor; [split|exact RANGES].
      * unfold temp_word in POS; cbn [entry_temps] in POS; rewrite WORD in POS; lia.
      * unfold signed_range; apply Int.signed_range.
Qed.

Definition memory_param_axis_pointer_scan_statement source (package : memory_param_pointer_region_package source)
  left_counters right_counters flag :=
  Ssequence (Sset flag (Econst_int Int.one type_int32s))
    (Ssequence (memory_param_axis_access_pairs_statement (memory_nest_iterators (param_pointer_region_nest package)++param_pointer_region_parameters package)
      left_counters right_counters (param_pointer_region_parameters package) flag (memory_nest_bounds (param_pointer_region_nest package))
      (memory_affine_access_pairs (memory_linear_pointer_accesses (param_pointer_region_code package))))
      (Sifthenelse (Etempvar flag type_int32s) Sskip Sbreak)).

Definition memory_param_axis_pointer_guard_statement source (package : memory_param_pointer_region_package source)
  left_counters right_counters flag :=
  Ssequence (tree_statement (memory_param_pointer_header_tree package) Sskip Sbreak)
    (memory_param_axis_pointer_scan_statement package left_counters right_counters flag).

Theorem memory_param_axis_pointer_guard_execution source (package : memory_param_pointer_region_package source)
  fe s live left_counters right_counters flag :
  length left_counters = length (memory_nest_iterators (param_pointer_region_nest package)) ->
  length right_counters = length (memory_nest_iterators (param_pointer_region_nest package)) ->
  NoDup (left_counters++right_counters) ->
  NoDup (left_counters++param_pointer_region_parameters package) ->
  NoDup (right_counters++param_pointer_region_parameters package) ->
  (forall identifier, In identifier (left_counters++right_counters) ->
    ~ In identifier (memory_param_axis_pointer_guard_protected package live) /\ identifier <> flag) ->
  ~ In flag (memory_param_axis_pointer_guard_protected package live) ->
  memory_param_pointer_runtime_domain package s ->
  exists accepted checked,
    memory_projected_check_execution fe s live
      (memory_param_axis_pointer_guard_statement package left_counters right_counters flag) accepted checked /\
    (accepted = true -> memory_param_pointer_runtime_presumption package
      (Entry (entry_ge s) (entry_env s) checked (entry_memory s))).
Proof.
  intros LEFT_LENGTH RIGHT_LENGTH UNIQUE LEFT_PARAM_UNIQUE RIGHT_PARAM_UNIQUE FRESH FLAG_FRESH [DOMAIN CAPABLE].
  destruct s as [ge locals temps memory].
  set (protected := memory_param_axis_pointer_guard_protected package live) in *.
  set (counts_ok := memory_param_pointer_header_accept package (Entry ge locals temps memory)).
  assert (COUNT_RUN : memory_check_statement_execution fe (Entry ge locals temps memory)
    (tree_statement (memory_param_pointer_header_tree package)
      Sskip Sbreak) counts_ok).
  { apply memory_decision_check_statement; apply (proj2 (@memory_param_pointer_header_exact source package _ DOMAIN counts_ok)); reflexivity. }
  destruct counts_ok eqn:COUNT.
  - assert (COUNT_ACCEPT : memory_param_pointer_header_accept package (Entry ge locals temps memory) = true) by exact COUNT.
    destruct (@memory_param_pointer_header_sound source package _ DOMAIN COUNT_ACCEPT)
      as [INITIAL [BOUND_RANGES PARAM_RANGES]].
    change (Forall2 (fun cap bound => register_range bound cap (Entry ge locals temps memory))
      (param_pointer_region_limits package) (memory_nest_bounds (param_pointer_region_nest package))) in BOUND_RANGES.
    destruct (@memory_param_axis_pointer_bound_values (param_pointer_region_limits package)
      (memory_nest_bounds (param_pointer_region_nest package)) ge locals temps memory BOUND_RANGES)
      as [counts [WORDS RANGES]].
    assert (PARAM_WORDS : memory_nest_bindings (param_pointer_region_parameters package)
      (memory_recursive_parameters (param_pointer_region_parameters package) temps) temps).
    { apply memory_scalar_register_bindings; intros identifier MEMBER.
      destruct DOMAIN as [VECTOR_DOMAIN PARAM_TYPES].
      apply andb_true_iff in COUNT_ACCEPT as [VECTOR_ACCEPT PARAM_ACCEPT].
      specialize (PARAM_TYPES VECTOR_ACCEPT); apply Forall_forall with (x := identifier) in PARAM_TYPES; [exact PARAM_TYPES|exact MEMBER]. }
    assert (SIGNED : Forall signed_range counts).
    { eapply Forall_impl; [|exact RANGES]; intros count [POS RANGE]; exact RANGE. }
    assert (DIMENSIONS : length (memory_nest_iterators (param_pointer_region_nest package)) = length counts).
    { rewrite memory_nest_lengths; unfold memory_nest_bindings in WORDS; apply Forall2_length in WORDS; exact WORDS. }
    specialize (CAPABLE COUNT_ACCEPT).
    set (initialized := PTree.set flag (Vint Int.one) temps).
    assert (INIT_FRAME : temp_agree protected temps initialized) by (apply temp_agree_set; exact FLAG_FRESH).
    assert (EXPAND : forall identifier,
      In identifier (memory_nest_bounds (param_pointer_region_nest package)++param_pointer_region_parameters package++param_pointer_region_pointers package++protected) ->
      In identifier protected).
    { intros identifier MEMBER; repeat rewrite in_app_iff in MEMBER; destruct MEMBER as [MEMBER|[MEMBER|[MEMBER|MEMBER]]].
      - unfold protected; apply memory_param_axis_pointer_protected_bound; exact MEMBER.
      - unfold protected; apply memory_param_axis_pointer_protected_parameter; exact MEMBER.
      - unfold protected; apply memory_param_axis_pointer_protected_pointer; exact MEMBER.
      - exact MEMBER. }
    assert (INIT_PUBLIC : temp_agree
      (memory_nest_bounds (param_pointer_region_nest package)++param_pointer_region_parameters package++param_pointer_region_pointers package++protected) temps initialized).
    { eapply temp_agree_weaken; [exact EXPAND|exact INIT_FRAME]. }
    assert (INIT_FLAG : initialized ! flag = Some (memory_boolean_word true)) by (unfold initialized; apply PTree.gss).
    assert (PAIRS : memory_param_axis_pointer_pairs_valid package
      (memory_affine_access_pairs (memory_linear_pointer_accesses (param_pointer_region_code package)))).
    { apply Forall_forall; intros [first second] MEMBER; apply memory_affine_access_pair_member in MEMBER; exact MEMBER. }
    destruct (@memory_param_axis_access_pairs_execution source package fe ge locals temps memory counts protected
      left_counters right_counters flag
      (memory_affine_access_pairs (memory_linear_pointer_accesses (param_pointer_region_code package)))
      RANGES WORDS ltac:(lia) ltac:(lia) UNIQUE LEFT_PARAM_UNIQUE RIGHT_PARAM_UNIQUE PARAM_WORDS
      ltac:(intros identifier MEMBER; destruct (FRESH identifier MEMBER) as [PUBLIC NOT_FLAG];
        split; [intro BAD; apply PUBLIC,EXPAND; exact BAD|exact NOT_FLAG])
      ltac:(intro BAD; apply FLAG_FRESH,EXPAND; exact BAD)
      CAPABLE PAIRS initialized true INIT_PUBLIC INIT_FLAG) as [checked [SCAN [FRAME FLAG]]].
    set (accepted := memory_param_axis_pointer_pairs_check package
      (memory_multi_pointer_locations temps (param_pointer_region_window package)) counts
      (memory_recursive_parameters (param_pointer_region_parameters package) temps)) in *.
    cbn [andb] in FLAG.
    assert (PUBLIC : temp_agree protected temps checked).
    { eapply temp_agree_trans; [exact INIT_FRAME|].
      eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER;
        apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact MEMBER. }
    assert (FINAL_TEST : expression_test (Etempvar flag type_int32s) (Entry ge locals checked memory) accepted).
    { exists (memory_boolean_word accepted); split; [constructor; exact FLAG|destruct accepted; reflexivity]. }
    exists accepted,checked; split.
    + split.
      * unfold memory_param_axis_pointer_guard_statement,memory_param_axis_pointer_scan_statement.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact COUNT_RUN|].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor; constructor|].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact SCAN|].
        destruct FINAL_TEST as [value [EVAL BOOL]]; unfold memory_check_outcome;
          eapply exec_Sifthenelse; [exact EVAL|exact BOOL|destruct accepted; constructor].
      * eapply temp_agree_weaken; [|exact PUBLIC]; intros identifier MEMBER;
        unfold protected,memory_param_axis_pointer_guard_protected; repeat (apply in_or_app; right); exact MEMBER.
    + intro ACCEPT; split.
      * change (memory_param_pointer_header_accept package (Entry ge locals checked memory) = true).
        rewrite (@memory_param_pointer_header_accept_temp_frame source package ge locals memory temps checked); [exact COUNT_ACCEPT|].
        eapply temp_agree_weaken; [|exact PUBLIC]; intros identifier MEMBER.
        repeat rewrite in_app_iff in MEMBER; destruct MEMBER as [MEMBER|[MEMBER|MEMBER]].
        -- unfold protected,memory_param_axis_pointer_guard_protected; apply in_or_app; left; exact MEMBER.
        -- unfold protected; apply memory_param_axis_pointer_protected_bound; exact MEMBER.
        -- unfold protected; apply memory_param_axis_pointer_protected_parameter; exact MEMBER.
      * eapply (@memory_param_axis_pointer_pairs_separation source package ge locals checked memory counts).
        -- exact RANGES.
        -- eapply memory_nest_bindings_frame_from; [|exact PUBLIC|exact WORDS].
           intros identifier MEMBER; unfold protected; apply memory_param_axis_pointer_protected_bound; exact MEMBER.
        -- eapply memory_param_axis_pointer_capabilities_frame; [exact WORDS|exact SIGNED|exact PUBLIC|exact CAPABLE].
        -- change (memory_param_axis_pointer_pairs_check package
             (memory_multi_pointer_locations checked (param_pointer_region_window package)) counts
             (memory_recursive_parameters (param_pointer_region_parameters package) checked) = true).
           rewrite (@memory_recursive_parameters_temp_frame (param_pointer_region_parameters package) temps checked).
           2: { eapply temp_agree_weaken; [|exact PUBLIC]; intros identifier MEMBER; unfold protected.
                apply memory_param_axis_pointer_protected_parameter; exact MEMBER. }
           rewrite (@memory_param_axis_pointer_pairs_check_frame source package temps checked counts
             (memory_recursive_parameters (param_pointer_region_parameters package) temps)); [exact ACCEPT|].
           eapply temp_agree_weaken; [|exact PUBLIC]; intros identifier MEMBER; unfold protected.
           apply memory_param_axis_pointer_protected_pointer; exact MEMBER.
  - exists false,temps; split; [split|discriminate].
    + unfold memory_param_axis_pointer_guard_statement; eapply exec_Sseq_2; [exact COUNT_RUN|discriminate].
    + apply temp_agree_refl.
Qed.
Print Assumptions memory_param_axis_pointer_guard_execution.
