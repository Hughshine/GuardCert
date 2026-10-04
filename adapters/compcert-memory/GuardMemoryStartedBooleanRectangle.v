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

From GuardMemory Require Import GuardMemoryBooleanRectangleExecution.
Definition memory_started_axis_coordinates start counts coordinates : Prop :=
  match counts,coordinates with
  | upper::rest,x::tail => start <= x < upper /\ Forall2 (fun coordinate bound => 0 <= coordinate < bound) tail rest
  | _,_ => False end.
Definition memory_boolean_started_rectangle_result test upper counts start :=
  memory_boolean_scan_result (fun x => memory_boolean_rectangle_result test counts [x]) start (Z.to_nat (upper-start)).
Definition memory_boolean_started_rectangle_statement root counters bounds body :=
  match counters,bounds with
  | counter::rest,bound::tail =>
    Ssequence (Sset counter (Etempvar root type_int32s))
      (counted_loop counter bound (memory_boolean_rectangle_statement rest tail body))
  | _,_ => Sskip end.
Theorem memory_boolean_started_rectangle_execution fe ge locals memory flag
  root counter counters bound bounds count counts start live original body test :
  NoDup (counter::counters) ->
  (forall identifier, In identifier (counter::counters) -> ~ In identifier ((bound::bounds)++root::live) /\ identifier <> flag) ->
  ~ In flag ((bound::bounds)++root::live) ->
  signed_range count -> Forall (fun count => 0 <= count /\ signed_range count) counts ->
  0 <= start <= count -> signed_range start ->
  length counters = length counts ->
  memory_nest_bindings (bound::bounds) (count::counts) original ->
  original ! root = Some (Vint (Int.repr start)) ->
  (forall coordinates temps accepted,
    memory_started_axis_coordinates start (count::counts) coordinates ->
    memory_nest_bindings (counter::counters) coordinates temps ->
    temp_agree ((bound::bounds)++root::live) original temps ->
    temps ! flag = Some (memory_boolean_word accepted) ->
    exists after,
      exec_stmt fe ge locals temps memory body E0 after memory Out_normal /\
      temp_agree ((counter::counters)++(bound::bounds)++root::live) temps after /\
      after ! flag = Some (memory_boolean_word (accepted && test coordinates))) ->
  forall current accepted,
    temp_agree ((bound::bounds)++root::live) original current ->
    current ! flag = Some (memory_boolean_word accepted) ->
    exists after,
      exec_stmt fe ge locals current memory
        (memory_boolean_started_rectangle_statement root (counter::counters) (bound::bounds) body) E0 after memory Out_normal /\
      temp_agree ((bound::bounds)++root::live) current after /\
      after ! flag = Some (memory_boolean_word
        (accepted && memory_boolean_started_rectangle_result test count counts start)).
Proof.
  intros UNIQUE FRESH FLAG_FRESH RANGE RANGES_REST START_BOUNDS START_RANGE REST_LENGTH WORDS ROOT_WORD BODY current accepted FRAME FLAG.
  set (all_live := root::live) in *.
    inversion UNIQUE as [|cc cs COUNTER_FRESH UNIQUE_REST]; subst.
    inversion WORDS as [|bb nn bs ns BOUND_WORD BOUND_WORDS]; subst.
    destruct (FRESH counter ltac:(cbn; auto)) as [PUBLIC_FRESH COUNTER_FLAG].
    assert (COUNTER_BOUND : counter <> bound) by (intro SAME; apply PUBLIC_FRESH; subst; cbn; auto).
    assert (BOUND_FLAG : bound <> flag) by (intro SAME; apply FLAG_FRESH; subst; cbn; auto).
    assert (COUNTER_LIVE : ~ In counter (bounds++all_live)) by
      (intro MEMBER; apply PUBLIC_FRESH; cbn; auto).
    set (initialized := counter_temps counter current start).
    set (test_coordinate := fun coordinate =>
      memory_boolean_rectangle_result test counts [coordinate]).
    assert (LOOP_BODY : forall coordinate temps good,
      signed_range coordinate -> start <= coordinate < count ->
      temps ! counter = Some (Vint (Int.repr coordinate)) ->
      temps ! bound = Some (Vint (Int.repr count)) ->
      temps ! flag = Some (memory_boolean_word good) ->
      temp_agree (bounds++all_live) original temps ->
      exists after,
        exec_stmt fe ge locals temps memory (memory_boolean_rectangle_statement counters bounds body)
          E0 after memory Out_normal /\
        temp_agree (counter::bound::bounds++all_live) temps after /\
        after ! flag = Some (memory_boolean_word (good && test_coordinate coordinate))).
    { intros coordinate temps good INDEX_RANGE INDEX ITER UPPER GOOD PUBLIC_FRAME.
      assert (ALL_FRAME : temp_agree ((bound::bounds)++all_live) original temps).
      { intros identifier MEMBER; cbn in MEMBER; destruct MEMBER as [<-|MEMBER];
          [rewrite UPPER,BOUND_WORD; reflexivity|apply PUBLIC_FRAME; exact MEMBER]. }
      assert (TAIL_WORDS : memory_nest_bindings bounds counts temps).
      { eapply memory_nest_bindings_frame_from; [|exact PUBLIC_FRAME|exact BOUND_WORDS].
        intros identifier MEMBER; apply in_or_app; left; exact MEMBER. }
      assert (INNER_FRESH : forall identifier, In identifier counters ->
        ~ In identifier (bounds++counter::bound::all_live) /\ identifier <> flag).
      { intros identifier MEMBER; destruct (FRESH identifier ltac:(cbn; auto)) as [PUBLIC NOT_FLAG].
        split; [|exact NOT_FLAG]; intro BAD; apply in_app_or in BAD; destruct BAD as [BAD|BAD].
        - apply PUBLIC; cbn; right; apply in_or_app; left; exact BAD.
        - cbn in BAD; destruct BAD as [SAME|[SAME|BAD]].
          + apply COUNTER_FRESH; subst; exact MEMBER.
          + apply PUBLIC; subst; cbn; auto.
          + apply PUBLIC; cbn; right; apply in_or_app; right; exact BAD. }
      assert (INNER_FLAG : ~ In flag (bounds++counter::bound::all_live)).
      { intro BAD; apply in_app_or in BAD; destruct BAD as [BAD|BAD].
        - apply FLAG_FRESH; cbn; right; apply in_or_app; left; exact BAD.
        - cbn in BAD; destruct BAD as [SAME|[SAME|BAD]];
            [congruence|congruence|apply FLAG_FRESH; cbn; right; apply in_or_app; right; exact BAD]. }
      assert (INNER_BODY : forall coordinates inside before,
        Forall2 (fun value limit => 0 <= value < limit) coordinates counts ->
        memory_nest_bindings counters coordinates inside ->
        temp_agree (bounds++counter::bound::all_live) temps inside ->
        inside ! flag = Some (memory_boolean_word before) ->
        exists after,
          exec_stmt fe ge locals inside memory body E0 after memory Out_normal /\
          temp_agree (counters++bounds++counter::bound::all_live) inside after /\
          after ! flag = Some (memory_boolean_word (before && test (coordinate::coordinates)))).
      { intros coordinates inside before COORDINATES COORDINATE_WORDS INNER_FRAME INNER_GOOD.
        destruct (BODY (coordinate::coordinates) inside before) as [after [RUN [AFTER_FRAME RESULT]]].
        - cbn [memory_started_axis_coordinates]; split; assumption.
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
      destruct (@memory_boolean_rectangle_execution fe ge locals memory flag counters bounds counts (counter::bound::all_live) temps body
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
      (memory_boolean_rectangle_statement counters bounds body) count start (bounds++all_live) original
      test_coordinate COUNTER_BOUND COUNTER_FLAG BOUND_FLAG COUNTER_LIVE RANGE LOOP_BODY
      (Z.to_nat (count-start)) start initialized accepted) as [after [RUN [AFTER_FRAME [EXIT RESULT]]]].
    + rewrite Z2Nat.id by lia; lia.
    + exact START_RANGE.
    + lia.
    + unfold initialized,counter_temps; apply PTree.gss.
    + unfold initialized,counter_temps; rewrite PTree.gso by congruence.
      rewrite FRAME by (cbn; auto); exact BOUND_WORD.
    + unfold initialized,counter_temps; rewrite PTree.gso by congruence; exact FLAG.
    + eapply temp_agree_trans; [|unfold initialized,counter_temps; apply temp_agree_set; exact COUNTER_LIVE].
      eapply temp_agree_weaken; [|exact FRAME]; cbn; auto.
    + exists after; split.
      * cbn [memory_boolean_started_rectangle_statement]; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := initialized) (m1 := memory).
        -- unfold initialized,counter_temps; apply exec_Sset; apply eval_Etempvar.
           rewrite FRAME by (apply in_or_app; right; unfold all_live; cbn; auto); exact ROOT_WORD.
        -- exact RUN.
      * split; [|exact RESULT].
        eapply temp_agree_trans; [|exact AFTER_FRAME].
        unfold initialized,counter_temps; apply temp_agree_set; exact PUBLIC_FRESH.
Qed.
Print Assumptions memory_boolean_started_rectangle_execution.
