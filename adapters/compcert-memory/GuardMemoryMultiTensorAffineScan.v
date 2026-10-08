From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightRectangularStore ClightCountedLoop ClightTempFrame ClightNoWrap.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRuntimeReceipts
  GuardMemoryFiniteAliasCondition GuardMemoryRecursiveSource GuardMemoryDynamicTensorLayout
  GuardMemoryDynamicTensorBackend GuardMemoryMultiTensorBackend GuardMemoryBooleanScan
  GuardMemoryBooleanTests GuardMemoryBooleanPairRectangle GuardMemoryMultiTensorAffineReceipts
  GuardMemoryMultiTensorAffineFootprint.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition multi_tensor_affine_pairs (accesses : list AccessFunction) :=
  flat_map (fun first => map (fun second => (first,second)) accesses) accesses.
Definition multi_tensor_affine_checked_test dimensions left right (pair : AccessFunction * AccessFunction) :=
  if Pos.eqb (fst (fst pair)) (fst (snd pair)) then rect_constant 1
  else multi_tensor_affine_pair_test dimensions left right (fst pair) (snd pair).
Definition multi_tensor_affine_scan_public dimensions scalars accesses live :=
  map (fun access : AccessFunction => fst access) accesses ++ tensor_dimension_registers dimensions ++ scalars ++ live.
Definition multi_tensor_affine_scan_statement dimensions left right bounds scalars flag accesses :=
  memory_boolean_pair_rectangle_statement left right bounds
    (memory_boolean_tests_statement flag
      (map (multi_tensor_affine_checked_test dimensions (left++scalars) (right++scalars))
        (multi_tensor_affine_pairs accesses))).

Lemma multi_tensor_affine_pairs_member accesses first second :
  In (first,second) (multi_tensor_affine_pairs accesses) <-> In first accesses /\ In second accesses.
Proof.
  unfold multi_tensor_affine_pairs; split.
  - intro MEMBER; apply in_flat_map in MEMBER as [left [LEFT MEMBER]].
    apply in_map_iff in MEMBER as [right [SAME RIGHT]]; inversion SAME; subst; auto.
  - intros [LEFT RIGHT]; apply in_flat_map; exists first; split; [exact LEFT|].
    apply in_map_iff; exists second; auto.
Qed.
Lemma multi_tensor_affine_forallb_map {A B} (f : A -> B) (test : B -> bool) items :
  forallb test (map f items) = forallb (fun item => test (f item)) items.
Proof. induction items; cbn; [reflexivity|rewrite IHitems; reflexivity]. Qed.
Lemma multi_tensor_affine_pairs_results locations firsts seconds a b :
  forallb (fun pair => multi_tensor_affine_access_check locations (fst pair) (snd pair) a b)
    (flat_map (fun first => map (fun second => (first,second)) seconds) firsts) =
  forallb (fun first => forallb (fun second => multi_tensor_affine_access_check locations first second a b)
    seconds) firsts.
Proof.
  induction firsts; cbn [flat_map forallb]; [reflexivity|].
  rewrite forallb_app,multi_tensor_affine_forallb_map,IHfirsts; reflexivity.
Qed.
Lemma multi_tensor_affine_checked_test_evaluation dimensions sizes original temps memory
    left right first second a b ge locals :
  tensor_layout_flag sizes = true -> tensor_dimension_view dimensions sizes temps ->
  temp_agree [fst first;fst second] original temps ->
  memory_nest_bindings left a temps -> memory_nest_bindings right b temps ->
  memory_cell_access (multi_tensor_locations original sizes) memory (exact_cell first a) Readable ->
  memory_cell_access (multi_tensor_locations original sizes) memory (exact_cell second b) Readable ->
  expression_test (multi_tensor_affine_checked_test dimensions left right (first,second))
    (Entry ge locals temps memory)
    (multi_tensor_affine_access_check (multi_tensor_locations original sizes) first second a b).
Proof.
  intros LAYOUT DIMENSIONS FRAME LEFT RIGHT FIRST SECOND.
  unfold multi_tensor_affine_checked_test,multi_tensor_affine_access_check; cbn [fst snd].
  destruct (Pos.eqb (fst first) (fst second)) eqn:IDS.
  - exists (Vint Int.one); split; [apply rect_constant_evaluation|reflexivity].
  - apply Pos.eqb_neq in IDS; eapply multi_tensor_affine_pair_test_evaluation; eassumption.
Qed.

Theorem multi_tensor_affine_scan_execution dimensions sizes original current memory
    left right bounds scalars counts values flag accesses live fe ge locals accepted :
  tensor_layout_flag sizes = true -> tensor_dimension_view dimensions sizes original ->
  NoDup (left++right) ->
  (forall identifier, In identifier (left++right) ->
    ~ In identifier (bounds++multi_tensor_affine_scan_public dimensions scalars accesses live) /\ identifier <> flag) ->
  ~ In flag (bounds++multi_tensor_affine_scan_public dimensions scalars accesses live) ->
  Forall (fun count => 0 <= count /\ signed_range count) counts ->
  length left = length counts -> length right = length counts ->
  memory_nest_bindings bounds counts original -> memory_nest_bindings scalars values original ->
  (forall point access,
    Forall2 (fun coordinate count => 0 <= coordinate < count) point counts -> In access accesses ->
    memory_cell_access (multi_tensor_locations original sizes) memory (exact_cell access (point++values)) Readable) ->
  temp_agree (bounds++multi_tensor_affine_scan_public dimensions scalars accesses live) original current ->
  current!flag = Some (memory_boolean_word accepted) ->
  exists after,
    exec_stmt fe ge locals current memory
      (multi_tensor_affine_scan_statement dimensions left right bounds scalars flag accesses) E0 after memory Out_normal /\
    temp_agree (bounds++multi_tensor_affine_scan_public dimensions scalars accesses live) current after /\
    after!flag = Some (memory_boolean_word
      (accepted && multi_tensor_affine_scan_check (multi_tensor_locations original sizes) accesses values counts)).
Proof.
  intros LAYOUT DIMENSIONS UNIQUE FRESH FLAG_FRESH RANGES LEFT_LENGTH RIGHT_LENGTH
    WORDS SCALARS RECEIPTS FRAME FLAG.
  unfold multi_tensor_affine_scan_statement,multi_tensor_affine_scan_check.
  eapply memory_boolean_pair_rectangle_execution; eauto.
  intros a b temps good A B LEFT RIGHT PUBLIC GOOD.
  assert (PRESERVED_FLAG : ~ In flag
    (left++right++bounds++multi_tensor_affine_scan_public dimensions scalars accesses live)).
  { intro BAD; repeat rewrite in_app_iff in BAD; destruct BAD as [BAD|[BAD|[BAD|BAD]]].
    - destruct (FRESH flag ltac:(apply in_or_app; left; exact BAD)) as [_ FALSE]; apply FALSE; reflexivity.
    - destruct (FRESH flag ltac:(apply in_or_app; right; exact BAD)) as [_ FALSE]; apply FALSE; reflexivity.
    - apply FLAG_FRESH; apply in_or_app; left; exact BAD.
    - apply FLAG_FRESH; apply in_or_app; right; exact BAD. }
  assert (TESTS : forall pair inside,
    In pair (multi_tensor_affine_pairs accesses) ->
    temp_agree (left++right++bounds++multi_tensor_affine_scan_public dimensions scalars accesses live) temps inside ->
    expression_test (multi_tensor_affine_checked_test dimensions (left++scalars) (right++scalars) pair)
      (Entry ge locals inside memory)
      (multi_tensor_affine_access_check (multi_tensor_locations original sizes)
        (fst pair) (snd pair) (a++values) (b++values))).
  { intros [first second] inside MEMBER INSIDE.
    apply multi_tensor_affine_pairs_member in MEMBER as [FIRST SECOND].
    assert (PUBLIC_INSIDE : temp_agree
      (bounds++multi_tensor_affine_scan_public dimensions scalars accesses live) original inside).
    { eapply temp_agree_trans; [exact PUBLIC|].
      eapply temp_agree_weaken; [|exact INSIDE]; intros id IN; repeat rewrite in_app_iff in *; tauto. }
    assert (SCALAR_INSIDE : memory_nest_bindings scalars values inside).
    { eapply memory_nest_bindings_frame_from; [|exact PUBLIC_INSIDE|exact SCALARS].
      intros id IN; unfold multi_tensor_affine_scan_public; repeat rewrite in_app_iff; tauto. }
    eapply multi_tensor_affine_checked_test_evaluation; [exact LAYOUT| | | | |exact (RECEIPTS a first A FIRST)|
      exact (RECEIPTS b second B SECOND)].
    - eapply tensor_dimension_view_frame; [|exact DIMENSIONS].
      eapply temp_agree_weaken; [|exact PUBLIC_INSIDE].
      intros id IN; unfold multi_tensor_affine_scan_public; repeat rewrite in_app_iff; tauto.
    - eapply temp_agree_weaken; [|exact PUBLIC_INSIDE]; cbn; intros id [ID|[ID|[]]]; subst id;
        unfold multi_tensor_affine_scan_public; apply in_or_app; right; apply in_or_app; left;
        apply in_map_iff; [exists first|exists second]; auto.
    - apply Forall2_app; [|exact SCALAR_INSIDE].
      eapply memory_nest_bindings_frame_from; [|exact INSIDE|exact LEFT].
      intros id IN; repeat rewrite in_app_iff; tauto.
    - apply Forall2_app; [|exact SCALAR_INSIDE].
      eapply memory_nest_bindings_frame_from; [|exact INSIDE|exact RIGHT].
      intros id IN; repeat rewrite in_app_iff; tauto. }
  destruct (@memory_boolean_tests_execution fe ge locals memory flag
    (left++right++bounds++multi_tensor_affine_scan_public dimensions scalars accesses live) temps
    (AccessFunction * AccessFunction)
    (multi_tensor_affine_checked_test dimensions (left++scalars) (right++scalars))
    (fun pair => multi_tensor_affine_access_check (multi_tensor_locations original sizes)
      (fst pair) (snd pair) (a++values) (b++values))
    (multi_tensor_affine_pairs accesses) PRESERVED_FLAG TESTS temps good ltac:(apply temp_agree_refl) GOOD)
    as [after [RUN [AFTER RESULT]]].
  exists after; split; [exact RUN|split; [exact AFTER|]].
  unfold multi_tensor_affine_pairs in RESULT; rewrite multi_tensor_affine_pairs_results in RESULT; exact RESULT.
Qed.

Print Assumptions multi_tensor_affine_pairs_member.
Print Assumptions multi_tensor_affine_forallb_map.
Print Assumptions multi_tensor_affine_pairs_results.
Print Assumptions multi_tensor_affine_checked_test_evaluation.
Print Assumptions multi_tensor_affine_scan_execution.
