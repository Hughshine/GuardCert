From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryMultiPointerCells
  GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerProjectedCandidate GuardMemoryLinearPointerSyntax
  GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryBooleanScan GuardMemoryFootprintCapabilities.
From GuardMemory Require Import GuardMemoryAffinePointerSyntax GuardMemoryAffinePointerPairs GuardMemoryAffinePairScan GuardMemoryAffinePairChoice.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_affine_access_pairs_statement x y flag bound pairs := match pairs with
  | [] => Sskip
  | (first,second)::rest => Ssequence
      (memory_affine_pair_choice_statement x y flag bound
        (memory_nary_access_array first) (memory_nary_access_array second)
        (memory_nary_access_expression first) (memory_nary_access_expression second)
        (memory_nary_access_index first) (memory_nary_access_index second))
      (memory_affine_access_pairs_statement x y flag bound rest)
  end.
Definition memory_affine_pointer_pairs_valid source (package : memory_affine_pointer_package source) pairs :=
  Forall (fun pair => In (fst pair) (memory_linear_pointer_accesses (multi_pointer_region_code (affine_pointer_region package))) /\
    In (snd pair) (memory_linear_pointer_accesses (multi_pointer_region_code (affine_pointer_region package))) /\
    memory_nary_access_array (fst pair) <> memory_nary_access_array (snd pair)) pairs.

Theorem memory_affine_access_pairs_execution source (package : memory_affine_pointer_package source)
  fe ge locals original memory count live x y flag pairs :
  0 <= count -> signed_range count ->
  original ! (affine_pointer_bound package) = Some (Vint (Int.repr count)) ->
  NoDup [x;y;flag;affine_pointer_bound package] ->
  ~ In x (multi_pointer_region_pointers (affine_pointer_region package)++live) ->
  ~ In y (multi_pointer_region_pointers (affine_pointer_region package)++live) ->
  ~ In flag (multi_pointer_region_pointers (affine_pointer_region package)++live) ->
  Forall (memory_cell_capable (memory_multi_pointer_locations original
    (multi_pointer_region_window (affine_pointer_region package))) memory)
    (memory_multi_pointer_runtime_footprint (affine_pointer_region package) original) ->
  memory_affine_pointer_pairs_valid package pairs ->
  forall current accepted,
    temp_agree (multi_pointer_region_pointers (affine_pointer_region package)++live) original current ->
    current ! (affine_pointer_bound package) = Some (Vint (Int.repr count)) ->
    current ! flag = Some (memory_boolean_word accepted) ->
    exists after,
      exec_stmt fe ge locals current memory (memory_affine_access_pairs_statement x y flag (affine_pointer_bound package) pairs)
        E0 after memory Out_normal /\
      temp_agree (affine_pointer_bound package::multi_pointer_region_pointers (affine_pointer_region package)++live) current after /\
      after ! flag = Some (memory_boolean_word
        (accepted && forallb (memory_affine_access_pair_check (memory_multi_pointer_locations original
          (multi_pointer_region_window (affine_pointer_region package))) count) pairs)).
Proof.
  intros POS RANGE BOUND UNIQUE XFRESH YFRESH FFRESH CELLS VALID.
  unfold memory_affine_pointer_pairs_valid in VALID.
  induction VALID as [|[first second] pairs [FIRST_MEMBER [SECOND_MEMBER DISTINCT]] REST IH];
    intros current accepted FRAME UPPER FLAG.
  - exists current; split; [constructor|split; [apply temp_agree_refl|cbn; rewrite andb_true_r; exact FLAG]].
  - pose proof (memory_affine_pointer_accesses_covered package) as COVER.
    assert (FIRST_ID : In (memory_nary_access_array first) (multi_pointer_region_pointers (affine_pointer_region package))).
    { apply Forall_forall with (x := first) in COVER; [exact COVER|exact FIRST_MEMBER]. }
    assert (SECOND_ID : In (memory_nary_access_array second) (multi_pointer_region_pointers (affine_pointer_region package))).
    { apply Forall_forall with (x := second) in COVER; [exact COVER|exact SECOND_MEMBER]. }
    assert (EXPAND_FRESH : forall identifier,
      ~ In identifier (multi_pointer_region_pointers (affine_pointer_region package)++live) ->
      ~ In identifier (memory_nary_access_array first::memory_nary_access_array second::multi_pointer_region_pointers (affine_pointer_region package)++live)).
    { intros identifier FRESH; cbn; intros [SAME|[SAME|MEMBER]]; apply FRESH;
      [subst; apply in_or_app; left; exact FIRST_ID|subst; apply in_or_app; left; exact SECOND_ID|exact MEMBER]. }
    assert (EXPAND_FRAME : temp_agree
      (memory_nary_access_array first::memory_nary_access_array second::multi_pointer_region_pointers (affine_pointer_region package)++live)
      original current).
    { intros identifier MEMBER; apply FRAME; cbn in MEMBER; destruct MEMBER as [<-|[<-|MEMBER]];
      [apply in_or_app; left; exact FIRST_ID|apply in_or_app; left; exact SECOND_ID|exact MEMBER]. }
    destruct (@memory_affine_pair_choice_execution (memory_nary_access_expression first) (memory_nary_access_expression second)
      (memory_nary_access_index first) (memory_nary_access_index second) (affine_pointer_iterator package)
      fe ge locals original current memory (multi_pointer_region_window (affine_pointer_region package))
      (memory_nary_access_array first) (memory_nary_access_array second) x y flag (affine_pointer_bound package)
      (multi_pointer_region_pointers (affine_pointer_region package)++live) count accepted
      (@memory_affine_pointer_accesses_encoding source package first FIRST_MEMBER)
      (@memory_affine_pointer_accesses_encoding source package second SECOND_MEMBER)
      DISTINCT (proj1 (proj2 (multi_pointer_region_extent (multi_pointer_region_syntax (affine_pointer_region package)))))
      POS RANGE UNIQUE (EXPAND_FRESH _ XFRESH) (EXPAND_FRESH _ YFRESH) (EXPAND_FRESH _ FFRESH)
      EXPAND_FRAME UPPER FLAG) as [middle [FIRST [MIDDLE_FRAME MIDDLE_FLAG]]].
    + intros index INDEX; split; eapply memory_affine_pointer_access_capability;
        [exact BOUND|exact RANGE|exact CELLS|exact FIRST_MEMBER|exact INDEX|
         exact BOUND|exact RANGE|exact CELLS|exact SECOND_MEMBER|exact INDEX].
    + destruct (IH middle (accepted && memory_affine_access_pair_check
        (memory_multi_pointer_locations original (multi_pointer_region_window (affine_pointer_region package))) count (first,second)))
        as [after [LAST [AFTER_FRAME AFTER_FLAG]]].
      * eapply temp_agree_trans; [exact FRAME|].
        eapply temp_agree_weaken; [|exact MIDDLE_FRAME]; cbn; intuition.
      * rewrite MIDDLE_FRAME by (cbn; auto); exact UPPER.
      * exact MIDDLE_FLAG.
      * exists after; split.
        -- cbn [memory_affine_access_pairs_statement]; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); eassumption.
        -- split.
           ++ eapply temp_agree_trans; [|exact AFTER_FRAME].
              eapply temp_agree_weaken; [|exact MIDDLE_FRAME]; cbn; intuition.
           ++ cbn [forallb]; rewrite andb_assoc; exact AFTER_FLAG.
Qed.
Print Assumptions memory_affine_access_pairs_execution.
