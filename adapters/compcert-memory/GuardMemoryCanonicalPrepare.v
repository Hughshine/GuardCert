From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryCanonicalDifference GuardMemoryCanonicalWord.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition canonical_count_range count :=
  0 <= count /\ signed_range count /\ 2*count-1 <= Int.max_signed.

Lemma canonical_bounds_ranges counts :
  Forall canonical_count_range counts ->
  Forall (fun bound => 0 <= bound /\ signed_range bound) (canonical_difference_bounds counts).
Proof.
  intro COUNTS; apply Forall_map; eapply Forall_impl; [|exact COUNTS].
  intros count [NONNEG [SIGNED UPPER]]; split;
    [apply canonical_difference_bound_nonnegative|apply canonical_difference_signed; assumption].
Qed.

Fixpoint canonical_bounds_statement bounds outputs :=
  match bounds,outputs with
  | bound::rest,output::tail => Ssequence (canonical_bound_statement bound output)
      (canonical_bounds_statement rest tail)
  | _,_ => Sskip
  end.

Theorem canonical_bounds_execution fe ge locals memory :
  forall bounds outputs counts live temps,
  NoDup outputs ->
  (forall identifier, In identifier outputs -> ~ In identifier (bounds++live)) ->
  length outputs = length counts ->
  memory_nest_bindings bounds counts temps -> Forall canonical_count_range counts ->
  exists after,
    exec_stmt fe ge locals temps memory (canonical_bounds_statement bounds outputs) E0 after memory Out_normal /\
    memory_nest_bindings outputs (canonical_difference_bounds counts) after /\
    temp_agree (bounds++live) temps after.
Proof.
  intro bounds; induction bounds as [|bound bounds IH]; intros outputs counts live temps
    UNIQUE FRESH LENGTH WORDS RANGES.
  - inversion WORDS; subst counts; destruct outputs; [|discriminate LENGTH].
    exists temps; split; [constructor|split; [constructor|apply temp_agree_refl]].
  - destruct counts as [|count counts]; [inversion WORDS|].
    destruct outputs as [|output outputs]; [discriminate LENGTH|].
    inversion WORDS as [|bb nn bs ns WORD TAIL_WORDS]; subst.
    inversion RANGES as [|nn ns [NONNEG [SIGNED UPPER]] TAIL_RANGES]; subst.
    inversion UNIQUE as [|oo os HEAD_FRESH TAIL_UNIQUE]; subst.
    set (middle := PTree.set output (Vint (Int.repr (canonical_difference_bound count))) temps).
    assert (MID_FRAME : temp_agree ((bound::bounds)++live) temps middle).
    { unfold middle; apply temp_agree_set; apply FRESH; cbn; auto. }
    assert (TAIL_BINDINGS : memory_nest_bindings bounds counts middle).
    { eapply memory_nest_bindings_frame_from; [|exact MID_FRAME|exact TAIL_WORDS];
        intros identifier MEMBER; cbn; right; apply in_or_app; left; exact MEMBER. }
    assert (TAIL_FRESH : forall identifier, In identifier outputs ->
      ~ In identifier (bounds++bound::output::live)).
    { intros identifier MEMBER BAD; repeat rewrite in_app_iff in BAD; cbn in BAD.
      destruct BAD as [BAD|[BAD|[BAD|BAD]]].
      - apply (FRESH identifier ltac:(cbn; auto)); cbn; right; apply in_or_app; left; exact BAD.
      - apply (FRESH identifier ltac:(cbn; auto)); cbn; auto.
      - subst identifier; contradiction.
      - apply (FRESH identifier ltac:(cbn; auto)); cbn; right; apply in_or_app; right; exact BAD. }
    destruct (IH outputs counts (bound::output::live) middle TAIL_UNIQUE TAIL_FRESH
      ltac:(cbn in LENGTH; lia) TAIL_BINDINGS TAIL_RANGES) as [after [TAIL [OUTPUTS FRAME]]].
    exists after; split.
    + cbn [canonical_bounds_statement]; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=middle) (m1:=memory).
      * unfold middle; exact (@canonical_bound_execution fe ge locals temps memory bound output count NONNEG SIGNED WORD).
      * exact TAIL.
    + split.
      * constructor.
        -- rewrite FRAME by (apply in_or_app; right; cbn; auto); unfold middle; apply PTree.gss.
        -- exact OUTPUTS.
      * eapply temp_agree_trans; [exact MID_FRAME|].
        eapply temp_agree_weaken; [|exact FRAME]; cbn; intros identifier MEMBER;
          repeat rewrite in_app_iff in *; cbn in *; tauto.
Qed.

Lemma canonical_coordinate_private_heads (left right : ident) (lefts rights : list ident) :
  NoDup ((left::lefts)++right::rights) ->
  left <> right /\ ~ In left (lefts++rights) /\ ~ In right (lefts++rights) /\ NoDup (lefts++rights).
Proof.
  cbn; intro UNIQUE; inversion UNIQUE as [|head tail FRESH REST]; subst.
  pose proof REST as RIGHT_FRESH; apply NoDup_remove_2 in RIGHT_FRESH.
  pose proof REST as TAIL_UNIQUE; apply NoDup_remove_1 in TAIL_UNIQUE.
  repeat split; auto.
  - intro SAME; subst left; apply FRESH; apply in_or_app; right; cbn; auto.
  - intro MEMBER; apply FRESH; rewrite in_app_iff in MEMBER; destruct MEMBER as [MEMBER|MEMBER];
      [apply in_or_app; left|apply in_or_app; right; cbn; right]; exact MEMBER.
Qed.

Fixpoint canonical_coordinates_statement bounds positions lefts rights :=
  match bounds,positions,lefts,rights with
  | bound::rest,position::tail,left_id::ls,right_id::rs =>
      Ssequence (canonical_axis_statement bound position left_id right_id)
        (canonical_coordinates_statement rest tail ls rs)
  | _,_,_,_ => Sskip
  end.

Theorem canonical_coordinates_execution fe ge locals memory :
  forall bounds positions lefts rights counts indices live temps,
  NoDup (lefts++rights) ->
  (forall identifier, In identifier (lefts++rights) -> ~ In identifier (bounds++positions++live)) ->
  length lefts = length counts -> length rights = length counts ->
  memory_nest_bindings bounds counts temps -> memory_nest_bindings positions indices temps ->
  Forall canonical_count_range counts ->
  Forall2 (fun index limit => 0 <= index < limit) indices (canonical_difference_bounds counts) ->
  exists after,
    exec_stmt fe ge locals temps memory
      (canonical_coordinates_statement bounds positions lefts rights) E0 after memory Out_normal /\
    memory_nest_bindings lefts (canonical_difference_first counts indices) after /\
    memory_nest_bindings rights (canonical_difference_second counts indices) after /\
    temp_agree (bounds++positions++live) temps after.
Proof.
  intro bounds; induction bounds as [|bound bounds IH]; intros positions lefts rights counts indices live temps
    UNIQUE FRESH LEFT_LENGTH RIGHT_LENGTH WORDS POINT_WORDS RANGES POINTS.
  - inversion WORDS; subst counts; inversion POINTS; subst indices; inversion POINT_WORDS; subst positions.
    destruct lefts,rights; try discriminate LEFT_LENGTH; try discriminate RIGHT_LENGTH.
    exists temps; split; [constructor|split; [constructor|split; [constructor|apply temp_agree_refl]]].
  - destruct counts as [|count counts]; [inversion WORDS|].
    destruct lefts as [|left lefts]; [discriminate LEFT_LENGTH|].
    destruct rights as [|right rights]; [discriminate RIGHT_LENGTH|].
    inversion WORDS as [|bb nn bs ns WORD TAIL_WORDS]; subst.
    inversion RANGES as [|nn ns [NONNEG [SIGNED UPPER]] TAIL_RANGES]; subst.
    inversion POINTS as [|index limit indices' limits INDEX TAIL_POINTS]; subst.
    destruct positions as [|position positions]; [inversion POINT_WORDS|].
    inversion POINT_WORDS as [|pp ii ps is POINT_WORD TAIL_POINT_WORDS]; subst.
    destruct (canonical_coordinate_private_heads UNIQUE) as [DISTINCT [LEFT_FRESH [RIGHT_FRESH TAIL_UNIQUE]]].
    assert (HEAD_LEFT : ~ In left ((bound::bounds)++(position::positions)++live)).
    { apply FRESH; apply in_or_app; left; cbn; auto. }
    assert (HEAD_RIGHT : ~ In right ((bound::bounds)++(position::positions)++live)).
    { apply FRESH; apply in_or_app; right; cbn; auto. }
    set (middle := PTree.set right (Vint (Int.repr (canonical_difference_right count index)))
      (PTree.set left (Vint (Int.repr (canonical_difference_left count index))) temps)).
    assert (MID_FRAME : temp_agree ((bound::bounds)++(position::positions)++live) temps middle).
    { unfold middle; eapply temp_agree_trans; [apply temp_agree_set; exact HEAD_LEFT|apply temp_agree_set; exact HEAD_RIGHT]. }
    assert (TAIL_FRESH : forall identifier, In identifier (lefts++rights) ->
      ~ In identifier (bounds++positions++bound::position::left::right::live)).
    { intros identifier MEMBER.
      assert (MEMBER_ALL : In identifier ((left::lefts)++right::rights))
        by (rewrite in_app_iff in MEMBER; cbn; rewrite in_app_iff; cbn; tauto).
      pose proof (FRESH identifier MEMBER_ALL) as PROTECTED.
      intro BAD; repeat rewrite in_app_iff in BAD; cbn in BAD.
      destruct BAD as [BAD|[BAD|[BAD|[BAD|[BAD|[BAD|BAD]]]]]].
      - apply PROTECTED; cbn; repeat rewrite in_app_iff; cbn; repeat rewrite in_app_iff; tauto.
      - apply PROTECTED; cbn; repeat rewrite in_app_iff; cbn; repeat rewrite in_app_iff; tauto.
      - apply PROTECTED; cbn; auto.
      - apply PROTECTED; cbn; repeat rewrite in_app_iff; cbn; repeat rewrite in_app_iff; tauto.
      - subst identifier; contradiction.
      - subst identifier; contradiction.
      - apply PROTECTED; cbn; repeat rewrite in_app_iff; cbn; repeat rewrite in_app_iff; tauto. }
    assert (MID_BOUNDS : memory_nest_bindings bounds counts middle).
    { eapply memory_nest_bindings_frame_from; [|exact MID_FRAME|exact TAIL_WORDS];
        intros identifier MEMBER; cbn; right; apply in_or_app; left; exact MEMBER. }
    assert (MID_POINTS : memory_nest_bindings positions indices' middle).
    { eapply memory_nest_bindings_frame_from; [|exact MID_FRAME|exact TAIL_POINT_WORDS];
        intros identifier MEMBER; cbn; repeat rewrite in_app_iff; cbn; repeat rewrite in_app_iff; tauto. }
    destruct (IH positions lefts rights counts indices' (bound::position::left::right::live) middle
      TAIL_UNIQUE TAIL_FRESH ltac:(cbn in LEFT_LENGTH; lia) ltac:(cbn in RIGHT_LENGTH; lia)
      MID_BOUNDS MID_POINTS TAIL_RANGES TAIL_POINTS) as [after [TAIL [LEFTS [RIGHTS FRAME]]]].
    exists after; split.
    + cbn [canonical_coordinates_statement]; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=middle) (m1:=memory).
      * unfold middle; exact (@canonical_axis_execution fe ge locals temps memory bound position left right count index
          ltac:(intro SAME; apply HEAD_LEFT; subst left; cbn; auto)
          ltac:(intro SAME; apply HEAD_LEFT; subst left; cbn; repeat rewrite in_app_iff; cbn; tauto)
          NONNEG SIGNED UPPER INDEX WORD POINT_WORD).
      * exact TAIL.
    + split.
      * constructor.
        -- rewrite FRAME by (repeat rewrite in_app_iff; cbn; tauto).
           unfold middle; rewrite PTree.gso by congruence; apply PTree.gss.
        -- exact LEFTS.
      * split.
        -- constructor; [rewrite FRAME by (repeat rewrite in_app_iff; cbn; tauto); unfold middle; apply PTree.gss|exact RIGHTS].
        -- eapply temp_agree_trans; [exact MID_FRAME|].
           eapply temp_agree_weaken; [|exact FRAME]; cbn; intros identifier MEMBER;
             repeat rewrite in_app_iff in *; cbn in *; repeat rewrite in_app_iff in *; tauto.
Qed.

Print Assumptions canonical_bounds_ranges.
Print Assumptions canonical_bounds_execution.
Print Assumptions canonical_coordinate_private_heads.
Print Assumptions canonical_coordinates_execution.
