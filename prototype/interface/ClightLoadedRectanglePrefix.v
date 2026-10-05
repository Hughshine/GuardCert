From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightPureExpr ClightRedundantSet ClightCountedLoop
  ClightFrontendLoopProtocol ClightStraightLine ClightRectangularStore ClightRectangularGuard ClightRectangularLoops ClightRectangularRegion.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyConditionComposition ReadonlyBranching ReadonlyPrefixScan
  ClightReadonlyRewrite ClightConditionComposition ClightReadonlyBranching ClightReadonlyLoadedTreeSynthesis
  ClightReadonlyCellSwap ClightLoadedRectangleRow ClightLoadedRectangleMemory ClightLoadedRectangleAtoms ClightLoadedRectangleInnerScan.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition loaded_rectangle_prefix_invariant fe d array row bound (column : ident) columns (body : statement) outer_body i entry :=
  0 <= i <= rectangle_outer_limit d /\
  exists upper M block q qofs current_temps current_memory after final,
    0 < Int.signed upper <= rectangle_outer_limit d /\ 0 < M <= rectangle_stride d /\
    (entry_temps entry) ! columns = Some (Vint (Int.repr M)) /\
    rect_array_binding d (entry_ge entry) (entry_env entry) array block /\
    (entry_temps entry) ! bound = Some (Vptr q qofs) /\
    Mem.loadv Mint32 (entry_memory entry) (Vptr q qofs) = Some (Vint upper) /\
    current_temps ! row = Some (Vint (Int.repr i)) /\ current_temps ! columns = Some (Vint (Int.repr M)) /\
    current_temps ! bound = Some (Vptr q qofs) /\ Mem.loadv Mint32 current_memory (Vptr q qofs) = Some (Vint upper) /\
    (forall b ofs, writable_word current_memory b ofs -> writable_word (entry_memory entry) b ofs) /\
    exec_stmt fe (entry_ge entry) (entry_env entry) current_temps current_memory
      (loaded_rectangle_source row bound outer_body) E0 after final Out_normal.
Definition loaded_rectangle_prefix_active bound i entry := i < Int.signed (loaded_rectangle_word bound entry).
Definition loaded_rectangle_prefix_active_probe bound i :=
  Test (loaded_rectangle_active_expr bound i) (Decision true) (Decision false).
Definition loaded_rectangle_row_property d array bound columns i entry :=
  forall j, 0 <= j < Int.signed (temp_word columns (entry_temps entry)) -> loaded_rectangle_alias_flag d array bound i j entry = false.

Lemma loaded_rectangle_prefix_activity d (VALID : rectangle_layout_valid d) fe O
  (observe : fragment_observation -> O -> Prop) array row bound column columns body outer_body i :
  readonly_classifier (readonly_clight_host fe observe)
    (loaded_rectangle_prefix_invariant fe d array row bound column columns body outer_body i)
    (loaded_rectangle_prefix_active bound i) (fun entry => ~ loaded_rectangle_prefix_active bound i entry)
    (loaded_rectangle_prefix_active_probe bound i).
Proof.
  unfold loaded_rectangle_prefix_active_probe; apply readonly_expression_classifier.
  - intros entry [RANGE [upper [M [block [q [qofs [temps [memory [after [final
      [NR [MR [COLS [ARRAY [BOUND [READ REST]]]]]]]]]]]]]]]].
    exists (loaded_rectangle_active_flag bound i entry); eapply loaded_rectangle_active_test;
      [pose proof (rectangle_limits VALID); unfold signed_range in *; change Int.min_signed with (-2147483648) in *; lia|exact BOUND|exact READ].
  - intros entry [RANGE [upper [M [block [q [qofs [temps [memory [after [final
      [NR [MR [COLS [ARRAY [BOUND [READ REST]]]]]]]]]]]]]]]] TEST.
    assert (FLAG : loaded_rectangle_active_flag bound i entry = true).
    { eapply readonly_test_determinate; [eapply loaded_rectangle_active_test;
        [pose proof (rectangle_limits VALID); unfold signed_range in *; change Int.min_signed with (-2147483648) in *; lia|exact BOUND|exact READ]|exact TEST]. }
    unfold loaded_rectangle_prefix_active, loaded_rectangle_active_flag in *; apply Z.ltb_lt; exact FLAG.
  - intros entry [RANGE [upper [M [block [q [qofs [temps [memory [after [final
      [NR [MR [COLS [ARRAY [BOUND [READ REST]]]]]]]]]]]]]]]] TEST.
    assert (FLAG : loaded_rectangle_active_flag bound i entry = false).
    { eapply readonly_test_determinate; [eapply loaded_rectangle_active_test;
        [pose proof (rectangle_limits VALID); unfold signed_range in *; change Int.min_signed with (-2147483648) in *; lia|exact BOUND|exact READ]|exact TEST]. }
    unfold loaded_rectangle_prefix_active, loaded_rectangle_active_flag in *; apply Z.ltb_ge in FLAG; lia.
Defined.

Lemma loaded_rectangle_prefix_inner d (VALID : rectangle_layout_valid d) fe array row bound column columns body outer_body i entry :
  row <> bound -> row <> column -> bound <> column -> row <> columns -> column <> columns ->
  flatten_region body = [rect_store d array row column] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  loaded_rectangle_prefix_invariant fe d array row bound column columns body outer_body i entry ->
  loaded_rectangle_prefix_active bound i entry -> loaded_rectangle_inner_invariant d array bound columns i 0 entry.
Proof.
  intros RQ RC QC RM CM BODY OUTER [RANGE [upper [M [block [q [qofs [temps [memory [after [final
    [NR [MR [COLS [ARRAY [BOUND [READ [ITER [CURRENT_COLS [CURRENT_BOUND [CURRENT_READ [PERMISSIONS SOURCE]]]]]]]]]]]]]]]]]]]]] ACTIVE.
  unfold loaded_rectangle_prefix_active, loaded_rectangle_word in ACTIVE; rewrite BOUND, READ in ACTIVE.
  destruct (@loaded_rectangle_row_step d VALID fe (entry_ge entry) (entry_env entry) temps memory
    array row bound column columns body outer_body after final i upper M q qofs
    RQ RC QC RM CM BODY OUTER NR MR ltac:(lia) ITER CURRENT_BOUND CURRENT_READ CURRENT_COLS SOURCE)
    as [row_memory [POINTS TAIL]].
  split; [unfold rectangle_layout_valid in VALID; lia|split; [lia|]].
  exists M, block, q, qofs, (Vint upper); split; [exact MR|split; [exact COLS|split; [exact ARRAY|split; [exact BOUND|split; [exact READ|]]]]].
  intros j JR; apply PERMISSIONS.
  exact (@loaded_rectangle_row_words d VALID (entry_ge entry) (entry_env entry) array block i M (Z.to_nat M) 0 memory row_memory
    ARRAY ltac:(lia) MR ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) POINTS j ltac:(rewrite Z2Nat.id by lia; lia)).
Qed.

Lemma loaded_rectangle_prefix_next d (VALID : rectangle_layout_valid d) fe array row bound column columns body outer_body i entry :
  row <> bound -> row <> column -> bound <> column -> row <> columns -> column <> columns ->
  flatten_region body = [rect_store d array row column] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  loaded_rectangle_prefix_invariant fe d array row bound column columns body outer_body i entry ->
  loaded_rectangle_prefix_active bound i entry -> loaded_rectangle_row_property d array bound columns i entry ->
  loaded_rectangle_prefix_invariant fe d array row bound column columns body outer_body (i+1) entry.
Proof.
  intros RQ RC QC RM CM BODY OUTER [RANGE [upper [M [block [q [qofs [temps [memory [after [final
    [NR [MR [COLS [ARRAY [BOUND [READ [ITER [CURRENT_COLS [CURRENT_BOUND [CURRENT_READ [PERMISSIONS SOURCE]]]]]]]]]]]]]]]]]]]]] ACTIVE APART.
  unfold loaded_rectangle_prefix_active, loaded_rectangle_word in ACTIVE; rewrite BOUND, READ in ACTIVE.
  destruct (@loaded_rectangle_row_step d VALID fe (entry_ge entry) (entry_env entry) temps memory
    array row bound column columns body outer_body after final i upper M q qofs
    RQ RC QC RM CM BODY OUTER NR MR ltac:(lia) ITER CURRENT_BOUND CURRENT_READ CURRENT_COLS SOURCE)
    as [row_memory [POINTS TAIL]].
  assert (NEXT_READ : Mem.loadv Mint32 row_memory (Vptr q qofs) = Some (Vint upper)).
  { eapply (@loaded_rectangle_row_load d VALID (entry_ge entry) (entry_env entry) array block i M (Z.to_nat M) 0
      memory row_memory q qofs (Vint upper));
      [exact ARRAY|lia|exact MR|lia|rewrite Z2Nat.id by lia; lia| |exact CURRENT_READ|exact POINTS].
    intros j JR; apply (@loaded_rectangle_alias_apart d array bound i j entry block q qofs ARRAY BOUND).
    apply APART; unfold temp_word; rewrite COLS, Int.signed_repr;
      [exact JR|pose proof (rectangle_limits VALID); unfold signed_range in *; change Int.min_signed with (-2147483648) in *; lia]. }
  split; [lia|].
  exists upper, M, block, q, qofs,
    (PTree.set row (Vint (Int.repr (i+1))) (PTree.set column (Vint (Int.repr M)) temps)), row_memory, after, final.
  split; [exact NR|split; [exact MR|split; [exact COLS|split; [exact ARRAY|split; [exact BOUND|split; [exact READ|]]]]]].
  split; [apply PTree.gss|].
  split; [rewrite !PTree.gso by congruence; exact CURRENT_COLS|].
  split; [rewrite !PTree.gso by congruence; exact CURRENT_BOUND|].
  split; [exact NEXT_READ|split; [|exact TAIL]].
  intros permission_block ofs WORD; apply PERMISSIONS.
  exact (@loaded_rectangle_row_permissions d (entry_ge entry) (entry_env entry) array i (Z.to_nat M) 0
    memory row_memory POINTS permission_block ofs WORD).
Qed.

Definition loaded_rectangle_prefix_point d (VALID : rectangle_layout_valid d) fe O
  (observe : fragment_observation -> O -> Prop) array row bound column columns body outer_body i
  (RQ : row <> bound) (RC : row <> column) (QC : bound <> column) (RM : row <> columns) (CM : column <> columns)
  (BODY : flatten_region body = [rect_store d array row column])
  (OUTER : flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body]) :
  readonly_condition (readonly_clight_host fe observe)
    (fun entry => loaded_rectangle_prefix_invariant fe d array row bound column columns body outer_body i entry /\
      loaded_rectangle_prefix_active bound i entry)
    (fun entry => loaded_rectangle_row_property d array bound columns i entry /\
      loaded_rectangle_prefix_invariant fe d array row bound column columns body outer_body (i+1) entry)
    (@loaded_rectangle_inner_tree d VALID fe O observe array bound columns i).
Proof.
  eapply readonly_condition_entails.
  - eapply readonly_condition_restrict.
    + exact (@synthesized_prefix_scan_condition clight_entry (readonly_clight_host fe observe) Z
        (clight_readonly_check_algebra fe observe) (clight_readonly_branch_algebra fe observe)
        (@loaded_rectangle_inner_spec d VALID fe O observe array bound columns i) (Z.to_nat (rectangle_stride d)) 0).
    + intros entry [INV ACTIVE]; exact (@loaded_rectangle_prefix_inner d VALID fe array row bound column columns body outer_body i entry
        RQ RC QC RM CM BODY OUTER INV ACTIVE).
  - intros entry [INV ACTIVE] SCAN.
    assert (ROW_APART : loaded_rectangle_row_property d array bound columns i entry).
    { intros j JR; eapply loaded_rectangle_inner_scan_sound; [exact SCAN| |lia].
      destruct INV as [RANGE [upper [M [block [q [qofs [temps [memory [after [final [NR [MR [COLS REST]]]]]]]]]]]]].
      unfold temp_word in JR; rewrite COLS, Int.signed_repr in JR by
        (pose proof (rectangle_limits VALID); unfold signed_range in *; change Int.min_signed with (-2147483648) in *; lia).
      cbn; rewrite Z2Nat.id by (unfold rectangle_layout_valid in VALID; lia); lia. }
    split; [exact ROW_APART|exact (@loaded_rectangle_prefix_next d VALID fe array row bound column columns body outer_body i entry
      RQ RC QC RM CM BODY OUTER INV ACTIVE ROW_APART)].
Defined.

Definition loaded_rectangle_prefix_spec d (VALID : rectangle_layout_valid d) fe O
  (observe : fragment_observation -> O -> Prop) array row bound column columns body outer_body RQ RC QC RM CM BODY OUTER :
  readonly_prefix_spec (readonly_clight_host fe observe) Z :=
  @ReadonlyPrefixSpec clight_entry (readonly_clight_host fe observe) Z (fun i => i+1)
    (loaded_rectangle_prefix_active_probe bound)
    (@loaded_rectangle_inner_tree d VALID fe O observe array bound columns)
    (loaded_rectangle_prefix_invariant fe d array row bound column columns body outer_body)
    (loaded_rectangle_prefix_active bound) (loaded_rectangle_row_property d array bound columns)
    (@loaded_rectangle_prefix_activity d VALID fe O observe array row bound column columns body outer_body)
    (fun i => @loaded_rectangle_prefix_point d VALID fe O observe array row bound column columns body outer_body i RQ RC QC RM CM BODY OUTER).

Print Assumptions loaded_rectangle_prefix_activity.
Print Assumptions loaded_rectangle_prefix_inner.
Print Assumptions loaded_rectangle_prefix_next.
Print Assumptions loaded_rectangle_prefix_point.
