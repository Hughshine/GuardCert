From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCountedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRuntimeReceipts GuardMemoryRecursiveSource
  GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend GuardMemoryMultiTensorBackend
  GuardMemoryMultiTensorAffineFootprint GuardMemoryBooleanScan GuardMemoryBooleanRectangle
  GuardMemoryBooleanRectangleExecution GuardMemoryCanonicalDifference GuardMemoryCanonicalAlias
  GuardMemoryCanonicalPrepare GuardMemoryCanonicalTests.
Import ListNotations.
Set Implicit Arguments.

Definition canonical_affine_scan_statement dimensions positions limits left right bounds scalars flag accesses :=
  Ssequence (canonical_bounds_statement bounds limits)
    (memory_boolean_rectangle_statement positions limits
      (Ssequence (canonical_coordinates_statement bounds positions left right)
        (canonical_affine_tests_statement dimensions left right scalars flag accesses))).

(** Counts are mathematical witnesses only. Emitted code refers exclusively
    to checked int32 registers; all extra coordinates are private. *)
Theorem canonical_affine_scan_execution dimensions sizes original current memory
    positions limits left right bounds scalars counts values flag accesses live fe ge locals accepted :
  tensor_layout_flag sizes = true -> tensor_dimension_view dimensions sizes original ->
  NoDup positions -> NoDup limits -> NoDup (left++right) ->
  (forall id, In id positions ->
    ~ In id (limits++bounds++canonical_affine_read_ports dimensions scalars accesses++live) /\ id <> flag) ->
  (forall id, In id limits ->
    ~ In id (bounds++canonical_affine_read_ports dimensions scalars accesses++live++[flag])) ->
  (forall id, In id (left++right) ->
    ~ In id (positions++limits++bounds++canonical_affine_read_ports dimensions scalars accesses++live++[flag])) ->
  ~ In flag (bounds++canonical_affine_read_ports dimensions scalars accesses++live) ->
  length positions = length counts -> length limits = length counts ->
  length left = length counts -> length right = length counts ->
  Forall canonical_count_range counts ->
  memory_nest_bindings bounds counts original -> memory_nest_bindings scalars values original ->
  (forall point access,
    Forall2 (fun coordinate count => (0 <= coordinate < count)%Z) point counts -> In access accesses ->
    memory_cell_access (multi_tensor_locations original sizes) memory (exact_cell access (point++values)) Readable) ->
  temp_agree (bounds++canonical_affine_read_ports dimensions scalars accesses++live) original current ->
  current!flag = Some (memory_boolean_word accepted) ->
  exists after,
    exec_stmt fe ge locals current memory
      (canonical_affine_scan_statement dimensions positions limits left right bounds scalars flag accesses)
      E0 after memory Out_normal /\
    temp_agree (bounds++canonical_affine_read_ports dimensions scalars accesses++live) current after /\
    after!flag = Some (memory_boolean_word
      (accepted && canonical_alias_check (multi_tensor_locations original sizes) accesses values counts)).
Proof.
  intros LAYOUT DIMENSIONS POS_UNIQUE LIM_UNIQUE COORD_UNIQUE POS_FRESH LIM_FRESH COORD_FRESH
    FLAG_FRESH POS_LENGTH LIM_LENGTH LEFT_LENGTH RIGHT_LENGTH RANGES WORDS SCALARS RECEIPTS FRAME FLAG.
  set (ports := canonical_affine_read_ports dimensions scalars accesses).
  assert (CURRENT_WORDS : memory_nest_bindings bounds counts current).
  { eapply memory_nest_bindings_frame_from; [|exact FRAME|exact WORDS];
      intros id MEMBER; apply in_or_app; left; exact MEMBER. }
  destruct (@canonical_bounds_execution fe ge locals memory bounds limits counts
    (ports++live++[flag]) current LIM_UNIQUE LIM_FRESH LIM_LENGTH CURRENT_WORDS RANGES)
    as [initialized [PREPARE [LIMITS PREPARE_FRAME]]].
  assert (NONNEG : Forall (fun count => (0 <= count)%Z) counts).
  { eapply Forall_impl; [|exact RANGES]; intros count [NONNEG _]; exact NONNEG. }
  assert (FLAG_LIMITS : ~ In flag limits).
  { intro MEMBER; apply (LIM_FRESH flag MEMBER); repeat rewrite in_app_iff; cbn; tauto. }
  assert (FLAG_COORDS : ~ In flag (left++right)).
  { intro MEMBER; apply (COORD_FRESH flag MEMBER); repeat rewrite in_app_iff; cbn; tauto. }
  assert (FLAG_POSITIONS : ~ In flag positions).
  { intro MEMBER; destruct (POS_FRESH flag MEMBER) as [_ FALSE]; apply FALSE; reflexivity. }
  assert (PREPARE_PORTS : temp_agree (bounds++ports++live) current initialized).
  { eapply temp_agree_weaken; [|exact PREPARE_FRAME]; intros id MEMBER;
      repeat rewrite in_app_iff in *; tauto. }
  assert (INITIAL_PORTS : temp_agree (bounds++ports++live) original initialized)
    by (eapply temp_agree_trans; eassumption).
  assert (INITIAL_FLAG : initialized!flag = Some (memory_boolean_word accepted)).
  { rewrite PREPARE_FRAME by (repeat rewrite in_app_iff; cbn; tauto); exact FLAG. }
  assert (BODY : forall indices temps good,
    Forall2 (fun index limit => (0 <= index < limit)%Z) indices (canonical_difference_bounds counts) ->
    memory_nest_bindings positions indices temps ->
    temp_agree (limits++bounds++ports++live) initialized temps ->
    temps!flag = Some (memory_boolean_word good) ->
    exists after,
      exec_stmt fe ge locals temps memory
        (Ssequence (canonical_coordinates_statement bounds positions left right)
          (canonical_affine_tests_statement dimensions left right scalars flag accesses)) E0 after memory Out_normal /\
      temp_agree (positions++limits++bounds++ports++live) temps after /\
      after!flag = Some (memory_boolean_word (good &&
        multi_tensor_affine_point_check (multi_tensor_locations original sizes) accesses values
          (canonical_difference_first counts indices) (canonical_difference_second counts indices)))).
  { intros indices temps good INDICES POSITION_WORDS PUBLIC GOOD.
    assert (ORIGINAL_PORTS : temp_agree (bounds++ports++live) original temps).
    { eapply temp_agree_trans; [exact INITIAL_PORTS|]; eapply temp_agree_weaken; [|exact PUBLIC];
        intros id MEMBER; repeat rewrite in_app_iff in *; tauto. }
    assert (BOUND_WORDS : memory_nest_bindings bounds counts temps).
    { eapply memory_nest_bindings_frame_from; [|exact ORIGINAL_PORTS|exact WORDS];
        intros id MEMBER; apply in_or_app; left; exact MEMBER. }
    assert (COORDINATES_FRESH : forall id, In id (left++right) ->
      ~ In id (bounds++positions++limits++ports++live++[flag])).
    { intros id MEMBER BAD; apply (COORD_FRESH id MEMBER);
        repeat rewrite in_app_iff in *; tauto. }
    destruct (@canonical_coordinates_execution fe ge locals memory bounds positions left right counts indices
      (limits++ports++live++[flag]) temps COORD_UNIQUE COORDINATES_FRESH LEFT_LENGTH RIGHT_LENGTH
      BOUND_WORDS POSITION_WORDS RANGES INDICES) as [coordinates [COORDINATES [LEFT [RIGHT COORD_FRAME]]]].
    assert (COORD_PORTS : temp_agree ports original coordinates).
    { eapply temp_agree_trans.
      - eapply temp_agree_weaken; [|exact ORIGINAL_PORTS]; intros id MEMBER; repeat rewrite in_app_iff; tauto.
      - eapply temp_agree_weaken; [|exact COORD_FRAME]; intros id MEMBER; repeat rewrite in_app_iff; tauto. }
    assert (COORD_FLAG : coordinates!flag = Some (memory_boolean_word good)).
    { rewrite COORD_FRAME by (repeat rewrite in_app_iff; cbn; tauto); exact GOOD. }
    assert (TEST_FLAG : ~ In flag (left++right++ports++positions++limits++bounds++live)).
    { intro BAD; change (~ In flag (bounds++ports++live)) in FLAG_FRESH;
        repeat rewrite in_app_iff in BAD;
        repeat rewrite in_app_iff in FLAG_FRESH;
        repeat rewrite in_app_iff in FLAG_COORDS; tauto. }
    destruct (canonical_difference_points NONNEG INDICES) as [FIRST_POINT SECOND_POINT].
    destruct (@canonical_affine_tests_execution dimensions sizes original coordinates memory left right scalars flag
      accesses values (canonical_difference_first counts indices) (canonical_difference_second counts indices)
      (positions++limits++bounds++live) fe ge locals good LAYOUT DIMENSIONS SCALARS COORD_PORTS LEFT RIGHT
      ltac:(intros access ACCESS; apply RECEIPTS; assumption)
      ltac:(intros access ACCESS; apply RECEIPTS; assumption) TEST_FLAG COORD_FLAG)
      as [after [TESTS [TEST_FRAME RESULT]]].
    exists after; split.
    - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=coordinates) (m1:=memory);
        [exact COORDINATES|exact TESTS].
    - split; [|exact RESULT].
      eapply temp_agree_trans.
      + eapply temp_agree_weaken; [|exact COORD_FRAME]; intros id MEMBER;
          repeat rewrite in_app_iff in *; tauto.
      + eapply temp_agree_weaken; [|exact TEST_FRAME]; intros id MEMBER;
          repeat rewrite in_app_iff in *; tauto. }
  destruct (@memory_boolean_rectangle_execution fe ge locals memory flag positions limits
    (canonical_difference_bounds counts) (bounds++ports++live) initialized
    (Ssequence (canonical_coordinates_statement bounds positions left right)
      (canonical_affine_tests_statement dimensions left right scalars flag accesses))
    (fun indices => multi_tensor_affine_point_check (multi_tensor_locations original sizes) accesses values
      (canonical_difference_first counts indices) (canonical_difference_second counts indices))
    POS_UNIQUE POS_FRESH ltac:(repeat rewrite in_app_iff in *; tauto)
    (canonical_bounds_ranges RANGES) ltac:(unfold canonical_difference_bounds; rewrite length_map; exact POS_LENGTH)
    LIMITS BODY initialized accepted ltac:(apply temp_agree_refl) INITIAL_FLAG)
    as [after [SCAN [SCAN_FRAME RESULT]]].
  exists after; split.
  - unfold canonical_affine_scan_statement; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0)
      (le1:=initialized) (m1:=memory); [exact PREPARE|exact SCAN].
  - split; [|exact RESULT].
    eapply temp_agree_trans; [exact PREPARE_PORTS|]; eapply temp_agree_weaken; [|exact SCAN_FRAME];
      intros id MEMBER; repeat rewrite in_app_iff in *; tauto.
Qed.

Print Assumptions canonical_affine_scan_execution.
