From Stdlib Require Import Bool List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightRegionProgress ClightLoopSyntax.
From GuardMemory Require Import GuardMemoryLongControl GuardMemoryDoubleLocations
  GuardMemoryLongRangeCapture.
From GuardInterface Require Import ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record long_capture_slot := LongCaptureSlot { capture_header : ident; capture_cache : ident }.
Definition long_capture_caches slots := map capture_cache slots.
Definition long_capture_cache_positive cache :=
  Ebinop Olt (Econst_int Int.zero memory_signed_int_type)
    (Etempvar cache memory_signed_int_type) memory_signed_int_type.

Lemma long_capture_flag_test ge locals temps memory flag (accepted : bool) :
  temps ! flag = Some (Vint (if accepted then Int.one else Int.zero)) ->
  expression_test (Etempvar flag memory_signed_int_type) (Entry ge locals temps memory) accepted.
Proof.
  intro VALUE; exists (Vint (if accepted then Int.one else Int.zero)); split.
  - constructor; exact VALUE.
  - destruct accepted; reflexivity.
Qed.
Lemma long_capture_positive_test ge locals temps memory cache word :
  temps ! cache = Some (Vint word) ->
  expression_test (long_capture_cache_positive cache) (Entry ge locals temps memory)
    (0 <? Int.signed word).
Proof.
  intro VALUE; exists (Val.of_bool (0 <? Int.signed word)); split.
  - eapply eval_Ebinop; [constructor|constructor; exact VALUE|].
    change (Some (Val.of_bool (Int.lt Int.zero word)) = Some (Val.of_bool (0 <? Int.signed word))).
    unfold Int.lt; rewrite Int.signed_zero.
    destruct (zlt 0 (Int.signed word));
      [rewrite (proj2 (Z.ltb_lt 0 (Int.signed word)) ltac:(lia))|
       rewrite (proj2 (Z.ltb_ge 0 (Int.signed word)) ltac:(lia))]; reflexivity.
  - destruct (0 <? Int.signed word); reflexivity.
Qed.

Fixpoint long_capture_clear slots :=
  match slots with
  | [] => Sskip
  | slot :: rest => Ssequence (Sset (capture_cache slot) (Econst_int Int.zero memory_signed_int_type))
      (long_capture_clear rest)
  end.
Fixpoint long_capture_cleared slots (temps : temp_env) :=
  match slots with
  | [] => temps
  | slot :: rest => long_capture_cleared rest (PTree.set (capture_cache slot) (Vint Int.zero) temps)
  end.
Fixpoint long_capture_path slots flag limit :=
  match slots with
  | [] => memory_capture_flag flag true
  | slot :: rest => Ssequence
      (memory_long_range_capture (capture_header slot) (capture_cache slot) flag limit)
      (Sifthenelse (Etempvar flag memory_signed_int_type)
        (Sifthenelse (long_capture_cache_positive (capture_cache slot))
          (long_capture_path rest flag limit)
          (Ssequence (long_capture_clear rest) (memory_capture_flag flag true))) Sskip)
  end.

(** Safe invocation is derived from reached source headers, without numeric
    range premises.  Only an active parent licenses the next load. *)
Fixpoint long_capture_path_license ge locals memory slots : Prop :=
  match slots with
  | [] => True
  | slot :: rest => exists block word,
      double_global_binding ge locals (capture_header slot) block /\
      Mem.load Mint64 memory block 0 = Some (Vlong word) /\
      (0 < Int64.signed word -> long_capture_path_license ge locals memory rest)
  end.
Fixpoint long_capture_entry_values ge locals memory slots values : Prop :=
  match slots, values with
  | [], [] => True
  | slot :: rest, value :: remaining => exists block,
      double_global_binding ge locals (capture_header slot) block /\
      Mem.load Mint64 memory block 0 = Some (Vlong (Int64.repr value)) /\
      (0 < value -> long_capture_entry_values ge locals memory rest remaining)
  | _, _ => False
  end.
Definition long_capture_acceptance ge locals memory slots limit (temps : temp_env) :=
  exists values,
    Forall2 (fun slot value => temps ! (capture_cache slot) = Some (Vint (Int.repr value))) slots values /\
    Forall (fun value => 0 <= value <= limit) values /\
    long_capture_entry_values ge locals memory slots values.

Lemma long_capture_clear_execution fe ge locals memory slots temps :
  exec_stmt fe ge locals temps memory (long_capture_clear slots) E0
    (long_capture_cleared slots temps) memory Out_normal.
Proof.
  revert temps; induction slots; intro temps; cbn [long_capture_clear long_capture_cleared]; [constructor|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [constructor; constructor|apply IHslots].
Qed.
Lemma long_capture_cleared_frame slots temps key : ~ In key (long_capture_caches slots) ->
  (long_capture_cleared slots temps) ! key = temps ! key.
Proof.
  revert temps; induction slots as [|slot rest IH]; intros temps PRIVATE; [reflexivity|].
  cbn [long_capture_cleared].
  change (~ In key (capture_cache slot :: long_capture_caches rest)) in PRIVATE.
  rewrite IH by (intro MEMBER; apply PRIVATE; right; exact MEMBER).
  rewrite PTree.gso by (intro SAME; apply PRIVATE; left; congruence); reflexivity.
Qed.
Lemma long_capture_cleared_lookup slots temps key : In key (long_capture_caches slots) ->
  (long_capture_cleared slots temps) ! key = Some (Vint Int.zero).
Proof.
  revert temps; induction slots; intros temps MEMBER; [contradiction|].
  cbn [long_capture_cleared]; cbn [long_capture_caches] in MEMBER.
  destruct (in_dec peq key (long_capture_caches slots)) as [IN|OUT].
  - apply IHslots; exact IN.
  - rewrite long_capture_cleared_frame by exact OUT.
    destruct MEMBER as [SAME|IN]; [subst key; apply PTree.gss|contradiction].
Qed.
Lemma long_capture_clear_writes slots : writes_only (long_capture_caches slots) (long_capture_clear slots).
Proof.
  induction slots; cbn [long_capture_clear long_capture_caches]; [constructor|constructor].
  - apply writes_set; cbn; auto.
  - eapply writes_only_weaken; [|exact IHslots]; cbn; auto.
Qed.
Lemma long_capture_path_writes slots flag limit :
  writes_only (flag :: long_capture_caches slots) (long_capture_path slots flag limit).
Proof.
  induction slots; cbn [long_capture_path long_capture_caches].
  - apply writes_set; cbn; auto.
  - apply writes_sequence.
    + eapply writes_only_weaken; [|apply memory_long_range_capture_writes]; cbn; tauto.
    + apply writes_if; [apply writes_if|constructor].
      * eapply writes_only_weaken; [|exact IHslots]; cbn; tauto.
      * apply writes_sequence.
        -- eapply writes_only_weaken; [|apply long_capture_clear_writes]; cbn; tauto.
        -- apply writes_set; cbn; auto.
Qed.
Lemma long_capture_path_quiet slots flag limit : quiet_statement (long_capture_path slots flag limit)=true.
Proof.
  induction slots; cbn [long_capture_path]; [reflexivity|].
  assert (CLEAR : quiet_statement (long_capture_clear slots)=true).
  { clear IHslots; induction slots; cbn [long_capture_clear quiet_statement]; auto. }
  cbn [memory_long_range_capture memory_long_range_tree tree_statement memory_capture_flag quiet_statement];
    rewrite IHslots, CLEAR; reflexivity.
Qed.

Lemma long_capture_zero_values slots temps :
  (forall slot, In slot slots -> temps ! (capture_cache slot)=Some (Vint Int.zero)) ->
  Forall2 (fun slot value => temps ! (capture_cache slot)=Some (Vint (Int.repr value)))
    slots (repeat 0 (List.length slots)).
Proof.
  induction slots; intro ALL; [constructor|constructor].
  - apply ALL; cbn; auto.
  - apply IHslots; intros slot MEMBER; apply ALL; cbn; auto.
Qed.

Theorem long_capture_path_execution fe ge locals memory slots flag limit temps :
  0 <= limit <= Int.max_signed -> NoDup (long_capture_caches slots) ->
  ~ In flag (long_capture_caches slots) -> long_capture_path_license ge locals memory slots ->
  exists (accepted : bool) after,
    exec_stmt fe ge locals temps memory (long_capture_path slots flag limit) E0 after memory Out_normal /\
    after ! flag = Some (Vint (if accepted then Int.one else Int.zero)) /\
    (accepted=true -> long_capture_acceptance ge locals memory slots limit after).
Proof.
  revert temps; induction slots as [|slot rest IH]; intros temps LIMIT DISTINCT PRIVATE LICENSE.
  - exists true, (PTree.set flag (Vint Int.one) temps); split.
    + apply memory_capture_flag_execution.
    + split; [apply PTree.gss|intro; exists []; repeat split; constructor].
  - cbn [long_capture_caches] in DISTINCT.
    change (~ In flag (capture_cache slot :: long_capture_caches rest)) in PRIVATE.
    assert (CACHE_FLAG : capture_cache slot <> flag)
      by (intro SAME; apply PRIVATE; left; exact SAME).
    assert (TAIL_FLAG : ~ In flag (long_capture_caches rest))
      by (intro MEMBER; apply PRIVATE; right; exact MEMBER).
    inversion DISTINCT as [|cache caches CACHE_PRIVATE REST_DISTINCT]; subst.
    destruct LICENSE as [block [word [BIND [LOAD CHILD]]]].
    pose (prepared := memory_long_range_captured temps (capture_cache slot) flag word limit).
    pose proof (@memory_long_range_capture_execution fe ge locals temps memory (capture_header slot)
      block (capture_cache slot) flag word limit BIND LOAD LIMIT) as CAPTURE.
    fold prepared in CAPTURE.
    assert (FLAG : prepared ! flag = Some (Vint
      (if memory_long_range_accept word limit then Int.one else Int.zero))) by apply PTree.gss.
    cbn [long_capture_path].
    destruct (memory_long_range_accept word limit) eqn:ACCEPT.
    + pose proof (proj1 (memory_long_range_accept_spec word limit) ACCEPT) as RANGE.
      destruct (@memory_long_accepted_int_exact word limit LIMIT ACCEPT) as [CAST SIGNED].
      assert (CACHE : prepared ! (capture_cache slot)=Some (Vint (Int64.loword word))).
      { unfold prepared, memory_long_range_captured; rewrite ACCEPT.
        rewrite PTree.gso by exact CACHE_FLAG; apply PTree.gss. }
      pose proof (@long_capture_positive_test ge locals prepared memory (capture_cache slot)
        (Int64.loword word) CACHE) as POSITIVE.
      rewrite SIGNED in POSITIVE.
      destruct (0 <? Int64.signed word) eqn:ACTIVE.
      * apply Z.ltb_lt in ACTIVE.
        destruct (IH prepared LIMIT REST_DISTINCT TAIL_FLAG (CHILD ACTIVE))
          as [accepted [after [RUN [RESULT FACTS]]]].
        exists accepted, after; split.
        -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact CAPTURE|].
           destruct (@long_capture_flag_test ge locals prepared memory flag true FLAG) as [v [EVAL BOOL]].
           eapply exec_Sifthenelse with (b:=true); [exact EVAL|exact BOOL|].
           destruct POSITIVE as [v' [EVAL' BOOL']].
           eapply exec_Sifthenelse with (b:=true); [exact EVAL'|exact BOOL'|exact RUN].
        -- split; [exact RESULT|intro TRUE].
           destruct (FACTS TRUE) as [values [CACHES [BOUNDS ENTRY]]].
           exists (Int64.signed word :: values); split.
           ++ constructor; [|exact CACHES].
              rewrite (@writes_only_frame fe ge locals prepared memory _ E0 after memory Out_normal RUN
                (flag :: long_capture_caches rest) (long_capture_path_writes rest flag limit)
                (capture_cache slot) ltac:(intro MEMBER; destruct MEMBER as [SAME|IN];
                  [apply CACHE_FLAG; congruence|exact (CACHE_PRIVATE IN)])).
              rewrite CACHE, CAST; reflexivity.
           ++ split; [constructor; assumption|].
              exists block; split; [exact BIND|split; [rewrite Int64.repr_signed; exact LOAD|auto]].
      * apply Z.ltb_ge in ACTIVE.
        assert (ZERO : Int64.signed word=0) by lia.
        assert (WORD_ZERO : Int64.repr 0=word) by (rewrite <- ZERO; apply Int64.repr_signed).
        pose (after := PTree.set flag (Vint Int.one) (long_capture_cleared rest prepared)).
        exists true, after; split.
        -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact CAPTURE|].
           destruct (@long_capture_flag_test ge locals prepared memory flag true FLAG) as [v [EVAL BOOL]].
           eapply exec_Sifthenelse with (b:=true); [exact EVAL|exact BOOL|].
           destruct POSITIVE as [v' [EVAL' BOOL']].
           eapply exec_Sifthenelse with (b:=false); [exact EVAL'|exact BOOL'|].
           eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);
             [apply long_capture_clear_execution|apply memory_capture_flag_execution].
        -- split; [apply PTree.gss|intro TRUE].
           exists (0 :: repeat 0 (List.length rest)); split.
           ++ constructor.
              ** unfold after; rewrite PTree.gso by exact CACHE_FLAG.
                 rewrite long_capture_cleared_frame by exact CACHE_PRIVATE.
                 rewrite CACHE, CAST, ZERO; reflexivity.
              ** apply long_capture_zero_values; intros next MEMBER; unfold after.
                 assert (IN : In (capture_cache next) (long_capture_caches rest))
                   by (apply in_map; exact MEMBER).
                 rewrite PTree.gso by (intro SAME; subst; tauto).
                 apply long_capture_cleared_lookup; exact IN.
           ++ split.
              ** constructor; [lia|].
                 induction (List.length rest); cbn; constructor; auto; lia.
              ** exists block; split; [exact BIND|split; [rewrite WORD_ZERO; exact LOAD|lia]].
    + exists false, prepared; split.
      * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact CAPTURE|].
        destruct (@long_capture_flag_test ge locals prepared memory flag false FLAG) as [v [EVAL BOOL]].
        eapply exec_Sifthenelse with (b:=false); [exact EVAL|exact BOOL|constructor].
      * split; [exact FLAG|discriminate].
Qed.

Theorem long_capture_path_completed fe ge locals memory slots flag limit temps trace after final outcome :
  0 <= limit <= Int.max_signed -> NoDup (long_capture_caches slots) ->
  ~ In flag (long_capture_caches slots) -> long_capture_path_license ge locals memory slots ->
  exec_stmt fe ge locals temps memory (long_capture_path slots flag limit) trace after final outcome ->
  trace=E0 /\ final=memory /\ outcome=Out_normal /\
  exists (accepted : bool), after ! flag=Some (Vint (if accepted then Int.one else Int.zero)) /\
    (accepted=true -> long_capture_acceptance ge locals memory slots limit after).
Proof.
  intros LIMIT DISTINCT PRIVATE LICENSE RUN.
  destruct (@long_capture_path_execution fe ge locals memory slots flag limit temps LIMIT DISTINCT PRIVATE LICENSE)
    as [accepted [expected [EXPECTED [RESULT FACTS]]]].
  destruct (@quiet_execution_determinate fe ge locals temps memory _ E0 expected memory Out_normal EXPECTED
    (long_capture_path_quiet slots flag limit) trace after final outcome RUN)
    as [TRACE [TEMPS [MEMORY OUTCOME]]]; subst; repeat split; auto.
  exists accepted; auto.
Qed.

Print Assumptions long_capture_clear_execution.
Print Assumptions long_capture_path_writes.
Print Assumptions long_capture_path_execution.
Print Assumptions long_capture_path_completed.
