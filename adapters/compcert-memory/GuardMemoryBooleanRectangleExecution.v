From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryBooleanScan GuardMemoryRecursiveSource.
From GuardMemory Require Import GuardMemoryBooleanRectangle.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_boolean_rectangle_statement counters bounds body :=
  match counters,bounds with
  | [],_ => body
  | counter::rest,bound::tail =>
      Ssequence (Sset counter (Econst_int Int.zero type_int32s))
        (counted_loop counter bound (memory_boolean_rectangle_statement rest tail body))
  | _,[] => Sskip
  end.

Theorem memory_boolean_rectangle_execution fe ge locals memory flag :
  forall counters bounds counts live original body test,
  NoDup counters ->
  (forall identifier, In identifier counters -> ~ In identifier (bounds++live) /\ identifier <> flag) ->
  ~ In flag (bounds++live) ->
  Forall (fun count => 0 <= count /\ signed_range count) counts ->
  length counters = length counts ->
  memory_nest_bindings bounds counts original ->
  (forall coordinates temps accepted,
    Forall2 (fun coordinate count => 0 <= coordinate < count) coordinates counts ->
    memory_nest_bindings counters coordinates temps ->
    temp_agree (bounds++live) original temps ->
    temps ! flag = Some (memory_boolean_word accepted) ->
    exists after,
      exec_stmt fe ge locals temps memory body E0 after memory Out_normal /\
      temp_agree (counters++bounds++live) temps after /\
      after ! flag = Some (memory_boolean_word (accepted && test coordinates))) ->
  forall current accepted,
    temp_agree (bounds++live) original current ->
    current ! flag = Some (memory_boolean_word accepted) ->
    exists after,
      exec_stmt fe ge locals current memory (memory_boolean_rectangle_statement counters bounds body)
        E0 after memory Out_normal /\
      temp_agree (bounds++live) current after /\
      after ! flag = Some (memory_boolean_word
        (accepted && memory_boolean_rectangle_result test counts [])).
Proof.
  intro counters; induction counters as [|counter counters IH];
    intros bounds counts live original body test UNIQUE FRESH FLAG_FRESH RANGES LENGTH WORDS BODY
      current accepted FRAME FLAG.
  - destruct counts; [|discriminate LENGTH].
    destruct bounds; [|inversion WORDS].
    exact (BODY [] current accepted ltac:(constructor) ltac:(constructor) FRAME FLAG).
  - destruct counts as [|count counts]; [discriminate LENGTH|].
    destruct bounds as [|bound bounds]; [inversion WORDS|].
    inversion UNIQUE as [|cc cs COUNTER_FRESH UNIQUE_REST]; subst.
    inversion RANGES as [|nn ns [NONNEG RANGE] RANGES_REST]; subst.
    inversion WORDS as [|bb nn bs ns BOUND_WORD BOUND_WORDS]; subst.
    assert (REST_LENGTH : length counters = length counts) by (cbn in LENGTH; lia).
    destruct (FRESH counter ltac:(cbn; auto)) as [PUBLIC_FRESH COUNTER_FLAG].
    assert (COUNTER_BOUND : counter <> bound) by (intro SAME; apply PUBLIC_FRESH; subst; cbn; auto).
    assert (BOUND_FLAG : bound <> flag) by (intro SAME; apply FLAG_FRESH; subst; cbn; auto).
    assert (COUNTER_LIVE : ~ In counter (bounds++live)) by
      (intro MEMBER; apply PUBLIC_FRESH; cbn; auto).
    set (initialized := counter_temps counter current 0).
    set (test_coordinate := fun coordinate =>
      memory_boolean_rectangle_result test counts [coordinate]).
    assert (LOOP_BODY : forall coordinate temps good,
      signed_range coordinate -> 0 <= coordinate < count ->
      temps ! counter = Some (Vint (Int.repr coordinate)) ->
      temps ! bound = Some (Vint (Int.repr count)) ->
      temps ! flag = Some (memory_boolean_word good) ->
      temp_agree (bounds++live) original temps ->
      exists after,
        exec_stmt fe ge locals temps memory (memory_boolean_rectangle_statement counters bounds body)
          E0 after memory Out_normal /\
        temp_agree (counter::bound::bounds++live) temps after /\
        after ! flag = Some (memory_boolean_word (good && test_coordinate coordinate))).
    { intros coordinate temps good INDEX_RANGE INDEX ITER UPPER GOOD PUBLIC_FRAME.
      assert (ALL_FRAME : temp_agree ((bound::bounds)++live) original temps).
      { intros identifier MEMBER; cbn in MEMBER; destruct MEMBER as [<-|MEMBER];
          [rewrite UPPER,BOUND_WORD; reflexivity|apply PUBLIC_FRAME; exact MEMBER]. }
      assert (TAIL_WORDS : memory_nest_bindings bounds counts temps).
      { eapply memory_nest_bindings_frame_from; [|exact PUBLIC_FRAME|exact BOUND_WORDS].
        intros identifier MEMBER; apply in_or_app; left; exact MEMBER. }
      assert (INNER_FRESH : forall identifier, In identifier counters ->
        ~ In identifier (bounds++counter::bound::live) /\ identifier <> flag).
      { intros identifier MEMBER; destruct (FRESH identifier ltac:(cbn; auto)) as [PUBLIC NOT_FLAG].
        split; [|exact NOT_FLAG]; intro BAD; apply in_app_or in BAD; destruct BAD as [BAD|BAD].
        - apply PUBLIC; cbn; right; apply in_or_app; left; exact BAD.
        - cbn in BAD; destruct BAD as [SAME|[SAME|BAD]].
          + apply COUNTER_FRESH; subst; exact MEMBER.
          + apply PUBLIC; subst; cbn; auto.
          + apply PUBLIC; cbn; right; apply in_or_app; right; exact BAD. }
      assert (INNER_FLAG : ~ In flag (bounds++counter::bound::live)).
      { intro BAD; apply in_app_or in BAD; destruct BAD as [BAD|BAD].
        - apply FLAG_FRESH; cbn; right; apply in_or_app; left; exact BAD.
        - cbn in BAD; destruct BAD as [SAME|[SAME|BAD]];
            [congruence|congruence|apply FLAG_FRESH; cbn; right; apply in_or_app; right; exact BAD]. }
      assert (INNER_BODY : forall coordinates inside before,
        Forall2 (fun value limit => 0 <= value < limit) coordinates counts ->
        memory_nest_bindings counters coordinates inside ->
        temp_agree (bounds++counter::bound::live) temps inside ->
        inside ! flag = Some (memory_boolean_word before) ->
        exists after,
          exec_stmt fe ge locals inside memory body E0 after memory Out_normal /\
          temp_agree (counters++bounds++counter::bound::live) inside after /\
          after ! flag = Some (memory_boolean_word (before && test (coordinate::coordinates)))).
      { intros coordinates inside before COORDINATES COORDINATE_WORDS INNER_FRAME INNER_GOOD.
        destruct (BODY (coordinate::coordinates) inside before) as [after [RUN [AFTER_FRAME RESULT]]].
        - constructor; assumption.
        - constructor; [rewrite INNER_FRAME by (apply in_or_app; right; cbn; auto); exact ITER|exact COORDINATE_WORDS].
        - eapply temp_agree_trans; [exact ALL_FRAME|].
          eapply temp_agree_weaken; [|exact INNER_FRAME];
            intros identifier MEMBER; repeat rewrite in_app_iff in *; cbn in *;
              repeat rewrite in_app_iff in *; intuition.
        - exact INNER_GOOD.
        - exists after; split; [exact RUN|split; [|exact RESULT]].
          eapply temp_agree_weaken; [|exact AFTER_FRAME];
            intros identifier MEMBER; repeat rewrite in_app_iff in *; cbn in *;
              repeat rewrite in_app_iff in *; intuition. }
      destruct (IH bounds counts (counter::bound::live) temps body
        (fun coordinates => test (coordinate::coordinates)) UNIQUE_REST INNER_FRESH INNER_FLAG
        RANGES_REST REST_LENGTH TAIL_WORDS INNER_BODY temps good ltac:(apply temp_agree_refl) GOOD)
        as [after [RUN [AFTER_FRAME RESULT]]].
      exists after; split; [exact RUN|split].
      - eapply temp_agree_weaken; [|exact AFTER_FRAME];
          intros identifier MEMBER; repeat rewrite in_app_iff in *; cbn in *;
            repeat rewrite in_app_iff in *; intuition.
      - unfold test_coordinate; change
          (after ! flag = Some (memory_boolean_word
            (good && memory_boolean_rectangle_result (fun coordinates => test ([coordinate]++coordinates)) counts []))) in RESULT.
        rewrite memory_boolean_rectangle_prepend in RESULT; exact RESULT. }
    destruct (@memory_boolean_scan_loop fe ge locals memory counter bound flag
      (memory_boolean_rectangle_statement counters bounds body) count 0 (bounds++live) original
      test_coordinate COUNTER_BOUND COUNTER_FLAG BOUND_FLAG COUNTER_LIVE RANGE LOOP_BODY
      (Z.to_nat count) 0 initialized accepted) as [after [RUN [AFTER_FRAME [EXIT RESULT]]]].
    + rewrite Z2Nat.id by exact NONNEG; lia.
    + unfold signed_range; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia.
    + lia.
    + unfold initialized,counter_temps; apply PTree.gss.
    + unfold initialized,counter_temps; rewrite PTree.gso by congruence.
      rewrite FRAME by (cbn; auto); exact BOUND_WORD.
    + unfold initialized,counter_temps; rewrite PTree.gso by congruence; exact FLAG.
    + eapply temp_agree_trans; [|unfold initialized,counter_temps; apply temp_agree_set; exact COUNTER_LIVE].
      eapply temp_agree_weaken; [|exact FRAME]; cbn; auto.
    + exists after; split.
      * cbn [memory_boolean_rectangle_statement]; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0);
          [constructor; constructor|exact RUN].
      * split; [|exact RESULT].
        eapply temp_agree_trans; [|exact AFTER_FRAME].
        unfold initialized,counter_temps; apply temp_agree_set; exact PUBLIC_FRESH.
Qed.
Print Assumptions memory_boolean_rectangle_execution.
