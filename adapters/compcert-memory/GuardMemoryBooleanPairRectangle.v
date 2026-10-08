From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryBooleanScan
  GuardMemoryBooleanRectangle GuardMemoryBooleanRectangleExecution.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Static code; counts occur only in its execution specification. *)
Definition memory_boolean_pair_rectangle_statement left right bounds body :=
  memory_boolean_rectangle_statement left bounds
    (memory_boolean_rectangle_statement right bounds body).
Definition memory_boolean_pair_rectangle_result test counts :=
  memory_boolean_rectangle_result (fun first =>
    memory_boolean_rectangle_result (test first) counts []) counts [].

Theorem memory_boolean_pair_rectangle_member test counts :
  Forall (fun count => 0 <= count) counts ->
  memory_boolean_pair_rectangle_result test counts = true <->
  forall first second,
    Forall2 (fun coordinate count => 0 <= coordinate < count) first counts ->
    Forall2 (fun coordinate count => 0 <= coordinate < count) second counts ->
    test first second = true.
Proof.
  intro COUNTS; unfold memory_boolean_pair_rectangle_result.
  rewrite memory_boolean_rectangle_member by exact COUNTS; cbn [app].
  split.
  - intros ALL first second FIRST SECOND; specialize (ALL first FIRST).
    rewrite memory_boolean_rectangle_member in ALL by exact COUNTS.
    exact (ALL second SECOND).
  - intros ALL first FIRST; rewrite memory_boolean_rectangle_member by exact COUNTS.
    cbn [app]; intros second SECOND; apply ALL; assumption.
Qed.

Theorem memory_boolean_pair_rectangle_execution fe ge locals memory flag
    left right bounds counts live original current body test accepted :
  NoDup (left++right) ->
  (forall identifier, In identifier (left++right) ->
    ~ In identifier (bounds++live) /\ identifier <> flag) ->
  ~ In flag (bounds++live) ->
  Forall (fun count => 0 <= count /\ signed_range count) counts ->
  length left = length counts -> length right = length counts ->
  memory_nest_bindings bounds counts original ->
  (forall first second temps good,
    Forall2 (fun coordinate count => 0 <= coordinate < count) first counts ->
    Forall2 (fun coordinate count => 0 <= coordinate < count) second counts ->
    memory_nest_bindings left first temps -> memory_nest_bindings right second temps ->
    temp_agree (bounds++live) original temps ->
    temps!flag = Some (memory_boolean_word good) ->
    exists after,
      exec_stmt fe ge locals temps memory body E0 after memory Out_normal /\
      temp_agree (left++right++bounds++live) temps after /\
      after!flag = Some (memory_boolean_word (good && test first second))) ->
  temp_agree (bounds++live) original current ->
  current!flag = Some (memory_boolean_word accepted) ->
  exists after,
    exec_stmt fe ge locals current memory
      (memory_boolean_pair_rectangle_statement left right bounds body) E0 after memory Out_normal /\
    temp_agree (bounds++live) current after /\
    after!flag = Some (memory_boolean_word
      (accepted && memory_boolean_pair_rectangle_result test counts)).
Proof.
  intros UNIQUE FRESH FLAG_FRESH RANGES LEFT_LENGTH RIGHT_LENGTH WORDS BODY FRAME FLAG.
  pose proof (@NoDup_app_remove_r _ left right UNIQUE) as LEFT_UNIQUE.
  pose proof (@NoDup_app_remove_l _ left right UNIQUE) as RIGHT_UNIQUE.
  assert (DISJOINT : forall identifier, In identifier left -> ~ In identifier right).
  { intros identifier MEMBER OTHER; apply in_split in MEMBER as [prefix [suffix SAME]].
    rewrite SAME,<-app_assoc in UNIQUE; cbn in UNIQUE.
    apply NoDup_remove_2 in UNIQUE; apply UNIQUE.
    apply in_or_app; right; apply in_or_app; right; exact OTHER. }
  assert (LEFT_FRESH : forall identifier, In identifier left ->
    ~ In identifier (bounds++live) /\ identifier <> flag).
  { intros identifier MEMBER; apply FRESH; apply in_or_app; left; exact MEMBER. }
  assert (OUTER_BODY : forall first temps good,
    Forall2 (fun coordinate count => 0 <= coordinate < count) first counts ->
    memory_nest_bindings left first temps ->
    temp_agree (bounds++live) original temps ->
    temps!flag = Some (memory_boolean_word good) ->
    exists after,
      exec_stmt fe ge locals temps memory
        (memory_boolean_rectangle_statement right bounds body) E0 after memory Out_normal /\
      temp_agree (left++bounds++live) temps after /\
      after!flag = Some (memory_boolean_word
        (good && memory_boolean_rectangle_result (test first) counts []))).
  { intros first temps good FIRST FIRST_WORDS PUBLIC_FRAME GOOD.
    assert (INNER_FRESH : forall identifier, In identifier right ->
      ~ In identifier (bounds++left++live) /\ identifier <> flag).
    { intros identifier MEMBER; destruct (FRESH identifier ltac:(apply in_or_app; right; exact MEMBER)) as [PUBLIC NOT_FLAG].
      split; [|exact NOT_FLAG]; intro BAD; repeat rewrite in_app_iff in BAD.
      destruct BAD as [BAD|[BAD|BAD]].
      - apply PUBLIC; apply in_or_app; left; exact BAD.
      - exact (DISJOINT identifier BAD MEMBER).
      - apply PUBLIC; apply in_or_app; right; exact BAD. }
    assert (INNER_FLAG : ~ In flag (bounds++left++live)).
    { intro BAD; repeat rewrite in_app_iff in BAD; destruct BAD as [BAD|[BAD|BAD]].
      - apply FLAG_FRESH; apply in_or_app; left; exact BAD.
      - destruct (LEFT_FRESH flag BAD) as [_ FALSE]; apply FALSE; reflexivity.
      - apply FLAG_FRESH; apply in_or_app; right; exact BAD. }
    assert (INNER_WORDS : memory_nest_bindings bounds counts temps).
    { eapply memory_nest_bindings_frame_from; [|exact PUBLIC_FRAME|exact WORDS].
      intros identifier MEMBER; apply in_or_app; left; exact MEMBER. }
    assert (INNER_BODY : forall second inside before,
      Forall2 (fun coordinate count => 0 <= coordinate < count) second counts ->
      memory_nest_bindings right second inside ->
      temp_agree (bounds++left++live) temps inside ->
      inside!flag = Some (memory_boolean_word before) ->
      exists after,
        exec_stmt fe ge locals inside memory body E0 after memory Out_normal /\
        temp_agree (right++bounds++left++live) inside after /\
        after!flag = Some (memory_boolean_word (before && test first second))).
    { intros second inside before SECOND SECOND_WORDS INNER_FRAME BEFORE.
      destruct (BODY first second inside before FIRST SECOND) as [after [RUN [AFTER_FRAME RESULT]]].
      - eapply memory_nest_bindings_frame_from; [|exact INNER_FRAME|exact FIRST_WORDS].
        intros identifier MEMBER; repeat rewrite in_app_iff; tauto.
      - exact SECOND_WORDS.
      - eapply temp_agree_trans; [exact PUBLIC_FRAME|].
        eapply temp_agree_weaken; [|exact INNER_FRAME].
        intros identifier MEMBER; repeat rewrite in_app_iff in *; tauto.
      - exact BEFORE.
      - exists after; split; [exact RUN|split; [|exact RESULT]].
        eapply temp_agree_weaken; [|exact AFTER_FRAME].
        intros identifier MEMBER; repeat rewrite in_app_iff in *; tauto. }
    destruct (@memory_boolean_rectangle_execution fe ge locals memory flag right bounds counts
      (left++live) temps body (test first) RIGHT_UNIQUE INNER_FRESH INNER_FLAG
      RANGES RIGHT_LENGTH INNER_WORDS INNER_BODY temps good ltac:(apply temp_agree_refl) GOOD)
      as [after [RUN [AFTER_FRAME RESULT]]].
    exists after; split; [exact RUN|split; [|exact RESULT]].
    eapply temp_agree_weaken; [|exact AFTER_FRAME].
    intros identifier MEMBER; repeat rewrite in_app_iff in *; tauto. }
  exact (@memory_boolean_rectangle_execution fe ge locals memory flag left bounds counts live original
    (memory_boolean_rectangle_statement right bounds body)
    (fun first => memory_boolean_rectangle_result (test first) counts []) LEFT_UNIQUE LEFT_FRESH
    FLAG_FRESH RANGES LEFT_LENGTH WORDS OUTER_BODY current accepted FRAME FLAG).
Qed.

Print Assumptions memory_boolean_pair_rectangle_member.
Print Assumptions memory_boolean_pair_rectangle_execution.
