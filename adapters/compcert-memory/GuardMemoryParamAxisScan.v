From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryMultiPointerCells
  GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerProjectedCandidate GuardMemoryLinearPointerSyntax
  GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryBooleanScan GuardMemoryFootprintCapabilities
  GuardMemoryRecursiveSource GuardMemoryAffinePointerPairs.
From GuardMemory Require Import GuardMemoryAxisPointerFootprint GuardMemoryAxisPointerPairs GuardMemoryAffineAxisPairScan GuardMemoryAxisPairChoice.
From GuardMemory Require Import GuardMemoryRecursiveDomain.
From GuardMemory Require Import GuardMemoryParamPointerSyntax GuardMemoryParamPointerProjectedCandidate GuardMemoryParamAxisFootprint GuardMemoryParamAxisPairs GuardMemoryParamAxisPairScan.
From GuardMemory Require Import GuardMemoryParamAxisPairChoice.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_param_axis_access_pairs_statement layout left_counters right_counters parameters flag bounds pairs :=
  match pairs with
  | [] => Sskip
  | (first,second)::rest => Ssequence
      (memory_param_affine_axis_pair_choice_statement layout left_counters right_counters parameters flag bounds
        (memory_nary_access_array first) (memory_nary_access_array second)
        (memory_nary_access_index first) (memory_nary_access_index second)
        (memory_nary_access_expression first) (memory_nary_access_expression second))
      (memory_param_axis_access_pairs_statement layout left_counters right_counters parameters flag bounds rest)
  end.
Definition memory_param_axis_pointer_pairs_valid source (package : memory_param_pointer_region_package source) pairs :=
  Forall (fun pair => In (fst pair) (memory_linear_pointer_accesses (param_pointer_region_code package)) /\
    In (snd pair) (memory_linear_pointer_accesses (param_pointer_region_code package)) /\
    memory_nary_access_array (fst pair) <> memory_nary_access_array (snd pair)) pairs.

Theorem memory_param_axis_access_pairs_execution source (package : memory_param_pointer_region_package source)
  fe ge locals original memory counts live left_counters right_counters flag pairs :
  Forall (fun count => 0 <= count /\ signed_range count) counts ->
  memory_nest_bindings (memory_nest_bounds (param_pointer_region_nest package)) counts original ->
  length left_counters = length counts -> length right_counters = length counts ->
  NoDup (left_counters++right_counters) ->
  NoDup (left_counters++param_pointer_region_parameters package) ->
  NoDup (right_counters++param_pointer_region_parameters package) ->
  memory_nest_bindings (param_pointer_region_parameters package)
    (memory_recursive_parameters (param_pointer_region_parameters package) original) original ->
  (forall identifier, In identifier (left_counters++right_counters) ->
    ~ In identifier (memory_nest_bounds (param_pointer_region_nest package)++param_pointer_region_parameters package++param_pointer_region_pointers package++live) /\ identifier <> flag) ->
  ~ In flag (memory_nest_bounds (param_pointer_region_nest package)++param_pointer_region_parameters package++param_pointer_region_pointers package++live) ->
  Forall (memory_cell_capable (memory_multi_pointer_locations original (param_pointer_region_window package)) memory)
    (memory_param_pointer_runtime_footprint package original) ->
  memory_param_axis_pointer_pairs_valid package pairs ->
  forall current accepted,
    temp_agree (memory_nest_bounds (param_pointer_region_nest package)++param_pointer_region_parameters package++param_pointer_region_pointers package++live) original current ->
    current ! flag = Some (memory_boolean_word accepted) ->
    exists after,
      exec_stmt fe ge locals current memory
        (memory_param_axis_access_pairs_statement (memory_nest_iterators (param_pointer_region_nest package)++param_pointer_region_parameters package)
          left_counters right_counters (param_pointer_region_parameters package) flag (memory_nest_bounds (param_pointer_region_nest package)) pairs)
        E0 after memory Out_normal /\
      temp_agree (memory_nest_bounds (param_pointer_region_nest package)++param_pointer_region_parameters package++param_pointer_region_pointers package++live) current after /\
      after ! flag = Some (memory_boolean_word
        (accepted && forallb (memory_param_axis_access_pair_check
          (memory_multi_pointer_locations original (param_pointer_region_window package)) counts
          (memory_recursive_parameters (param_pointer_region_parameters package) original)) pairs)).
Proof.
  intros RANGES WORDS LEFT_LENGTH RIGHT_LENGTH UNIQUE LEFT_PARAM_UNIQUE RIGHT_PARAM_UNIQUE PARAM_WORDS FRESH FLAG_FRESH CELLS VALID.
  assert (SIGNED : Forall signed_range counts).
  { eapply Forall_impl; [|exact RANGES]; intros count [POS RANGE]; exact RANGE. }
  assert (DIMENSIONS : length (memory_nest_iterators (param_pointer_region_nest package)) = length counts).
  { rewrite memory_nest_lengths; unfold memory_nest_bindings in WORDS; apply Forall2_length in WORDS; exact WORDS. }
  unfold memory_param_axis_pointer_pairs_valid in VALID.
  induction VALID as [|[first second] pairs [FIRST_MEMBER [SECOND_MEMBER DISTINCT]] REST IH];
    intros current accepted FRAME FLAG.
  - exists current; split; [constructor|split; [apply temp_agree_refl|cbn; rewrite andb_true_r; exact FLAG]].
  - pose proof (memory_param_axis_pointer_accesses_covered package) as COVER.
    assert (FIRST_ID : In (memory_nary_access_array first) (param_pointer_region_pointers package)).
    { apply Forall_forall with (x := first) in COVER; assumption. }
    assert (SECOND_ID : In (memory_nary_access_array second) (param_pointer_region_pointers package)).
    { apply Forall_forall with (x := second) in COVER; assumption. }
    assert (EXPAND : forall identifier,
      In identifier (memory_nest_bounds (param_pointer_region_nest package)++
        memory_nary_access_array first::memory_nary_access_array second::
          param_pointer_region_parameters package++param_pointer_region_pointers package++live) ->
      In identifier (memory_nest_bounds (param_pointer_region_nest package)++
        param_pointer_region_parameters package++param_pointer_region_pointers package++live)).
    { intros identifier MEMBER; apply in_app_or in MEMBER as [MEMBER|MEMBER].
      - apply in_or_app; left; exact MEMBER.
      - change (memory_nary_access_array first = identifier \/
          memory_nary_access_array second = identifier \/
          In identifier (param_pointer_region_parameters package++param_pointer_region_pointers package++live)) in MEMBER.
        destruct MEMBER as [<-|[<-|MEMBER]]; apply in_or_app; right.
        + apply in_or_app; right; apply in_or_app; left; exact FIRST_ID.
        + apply in_or_app; right; apply in_or_app; left; exact SECOND_ID.
        + exact MEMBER. }
    destruct (@memory_param_affine_axis_pair_choice_execution (memory_nary_access_expression first) (memory_nary_access_expression second)
      (memory_nary_access_index first) (memory_nary_access_index second)
      (memory_nest_iterators (param_pointer_region_nest package)++param_pointer_region_parameters package) left_counters right_counters
      (param_pointer_region_parameters package) (memory_nest_bounds (param_pointer_region_nest package)) counts
      (memory_recursive_parameters (param_pointer_region_parameters package) original)
      fe ge locals original current memory (param_pointer_region_window package)
      (memory_nary_access_array first) (memory_nary_access_array second) flag (param_pointer_region_parameters package++param_pointer_region_pointers package++live) accepted)
      as [middle [FIRST [MIDDLE_FRAME MIDDLE_FLAG]]].
    + apply memory_param_axis_pointer_accesses_encoding; exact FIRST_MEMBER.
    + apply memory_param_axis_pointer_accesses_encoding; exact SECOND_MEMBER.
    + exact (@NoDup_app_remove_r _
        (memory_nest_iterators (param_pointer_region_nest package)++param_pointer_region_parameters package)
        (param_pointer_region_scalars package) (param_pointer_region_registers (param_pointer_region_syntax package))).
    + exact UNIQUE.
    + exact LEFT_PARAM_UNIQUE.
    + exact RIGHT_PARAM_UNIQUE.
    + intros identifier MEMBER; apply in_or_app; right; cbn; right; right; apply in_or_app; left; exact MEMBER.
    + rewrite length_app,DIMENSIONS; unfold memory_recursive_parameters; rewrite length_map; reflexivity.
    + exact LEFT_LENGTH.
    + exact RIGHT_LENGTH.
    + exact DISTINCT.
    + exact (proj1 (proj2 (param_pointer_region_extent (param_pointer_region_syntax package)))).
    + exact RANGES.
    + intros identifier MEMBER; destruct (FRESH identifier MEMBER) as [PUBLIC NOT_FLAG]; split; [|exact NOT_FLAG].
      intro BAD; apply PUBLIC,EXPAND; exact BAD.
    + intro BAD; apply FLAG_FRESH,EXPAND; exact BAD.
    + exact WORDS.
    + exact PARAM_WORDS.
    + unfold memory_recursive_parameters; apply Forall_forall.
      intros value MEMBER; apply in_map_iff in MEMBER as [identifier [<- MEMBER]].
      unfold signed_range; apply Int.signed_range.
    + eapply temp_agree_weaken; [exact EXPAND|exact FRAME].
    + exact FLAG.
    + intros coordinates COORDINATES; split; eapply memory_param_axis_pointer_access_capability;
        [exact WORDS|exact SIGNED|exact CELLS|exact FIRST_MEMBER|exact COORDINATES|
         exact WORDS|exact SIGNED|exact CELLS|exact SECOND_MEMBER|exact COORDINATES].
    + assert (PUBLIC_FRAME : temp_agree
        (memory_nest_bounds (param_pointer_region_nest package)++param_pointer_region_parameters package++param_pointer_region_pointers package++live) current middle).
      { eapply temp_agree_weaken; [|exact MIDDLE_FRAME].
        intros identifier MEMBER; apply in_app_or in MEMBER as [MEMBER|MEMBER]; apply in_or_app;
          [left; exact MEMBER|right; cbn; auto]. }
      destruct (IH middle (accepted && memory_param_axis_access_pair_check
        (memory_multi_pointer_locations original (param_pointer_region_window package)) counts
        (memory_recursive_parameters (param_pointer_region_parameters package) original) (first,second)))
        as [after [LAST [AFTER_FRAME AFTER_FLAG]]].
      * eapply temp_agree_trans; eassumption.
      * exact MIDDLE_FLAG.
      * exists after; split.
        -- cbn [memory_param_axis_access_pairs_statement]; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); eassumption.
        -- split; [eapply temp_agree_trans; eassumption|cbn [forallb]; rewrite andb_assoc; exact AFTER_FLAG].
Qed.
Print Assumptions memory_param_axis_access_pairs_execution.
