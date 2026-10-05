From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightPureExpr ClightSameAddress ClightCountedLoop ClightCountedProtocol ClightFrontendRegion ClightFrontendLoopProtocol
  ClightRegionProgress ClightLoopExecution ClightLoopSyntax ClightStraightLine ClightTempFrame ClightTempFootprint
  ClightProjectedExecution CompCertMemoryEquivalence.
From GuardInterface Require Import ClightReadonlyRewrite ClightRegionBoundary ClightReadonlyProjectedCompiler
  ClightStrictLoopProgress ClightStrictIteration ClightActiveLoopCondition ClightStableLoopCondition
  ClightIndexedLoadBody ClightIndexedAliasGuard ClightIndexedBoundSyntax ClightIndexedBoundPrefix
  ClightIndexedBoundScan ClightIndexedBoundGuard ClightQuietDeterminacy ClightStableLoadBody ClightReadonlyLoadedTreeSynthesis.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition indexed_bound_candidate iterator bound cache body :=
  Ssequence (Sset cache (indexed_bound_value bound)) (frontend_counted_loop iterator cache body).
Definition indexed_bound_snapshot iterator out bound cache block base q qofs upper (active : bool) le memory :=
  exists word, le ! iterator = Some (Vint word) /\
    0 <= Int.signed word /\ (if active then Int.signed word < Int.signed upper else Int.signed word <= Int.signed upper) /\
    le ! out = Some (Vptr block base) /\ le ! bound = Some (Vptr q qofs) /\
    le ! cache = Some (Vint upper) /\ Mem.loadv Mint32 memory (Vptr q qofs) = Some (Vint upper).
Lemma indexed_bound_source_writes iterator bound out body :
  flatten_region body = [indexed_bound_body out iterator] -> writes_only [iterator] (indexed_bound_loop iterator bound body).
Proof.
  intro FLAT; unfold indexed_bound_loop, strict_frontend_loop, counter_increment; constructor.
  - constructor; [repeat constructor|].
    eapply writes_only_weaken with (small := []); [intros id BAD; contradiction|exact (@indexed_bound_body_writes out iterator body FLAT)].
  - repeat constructor; cbn; auto.
Qed.
Lemma indexed_bound_source_quiet iterator bound out body :
  flatten_region body = [indexed_bound_body out iterator] -> quiet_statement (indexed_bound_loop iterator bound body) = true.
Proof.
  intro FLAT; cbn [indexed_bound_loop strict_frontend_loop quiet_statement counter_increment].
  rewrite (@indexed_bound_body_quiet out iterator body FLAT); reflexivity.
Qed.

Theorem indexed_bound_loop_cached fe ge locals iterator out bound cache body block base q qofs upper
  le memory trace after final outcome :
  iterator <> out -> iterator <> bound -> cache <> iterator ->
  flatten_region body = [indexed_bound_body out iterator] ->
  (forall k, 0 <= k < Int.signed upper -> Vptr block (indexed_word_offset base (Int.repr k)) <> Vptr q qofs) ->
  indexed_bound_snapshot iterator out bound cache block base q qofs upper false le memory ->
  exec_stmt fe ge locals le memory (indexed_bound_loop iterator bound body) trace after final outcome ->
  exec_stmt fe ge locals le memory (frontend_counted_loop iterator cache body) trace after final outcome.
Proof.
  intros IO IQ CI FLAT APART INV SOURCE.
  assert (TEST : forall before mem flag,
    indexed_bound_snapshot iterator out bound cache block base q qofs upper false before mem ->
    expression_test (indexed_bound_test iterator bound) (Entry ge locals before mem) flag ->
    expression_test (counter_condition iterator cache) (Entry ge locals before mem) flag).
  { intros before mem flag [word [ITER [LOW [HIGH [OUT [BOUND [CACHE READ]]]]]]] RUN.
    pose proof (@indexed_bound_test_eval ge locals before mem iterator bound word upper q qofs ITER BOUND READ) as KNOWN.
    assert (SAME : flag = Int.lt word upper) by (eapply readonly_test_determinate; eassumption); subst flag.
    exists (Val.of_bool (Int.lt word upper)); split; [|apply bool_of_bool].
    eapply eval_Ebinop with (v1 := Vint word) (v2 := Vint upper); [constructor; exact ITER|constructor; exact CACHE|reflexivity]. }
  assert (BODY : forall before mem tr exit mem' out',
    indexed_bound_snapshot iterator out bound cache block base q qofs upper false before mem ->
    expression_test (indexed_bound_test iterator bound) (Entry ge locals before mem) true ->
    exec_stmt fe ge locals before mem body tr exit mem' out' ->
    indexed_bound_snapshot iterator out bound cache block base q qofs upper true exit mem').
  { intros before mem tr exit mem' out' [word [ITER [LOW [HIGH [OUT [BOUND [CACHE READ]]]]]]] ACTIVE RUN.
    pose proof (memory_body_temporaries_exact (@indexed_bound_body_writes out iterator body FLAT) RUN) as TEMPS; subst exit.
    pose proof (@normal_statement_execution fe ge locals body (@indexed_bound_body_normal out iterator body FLAT)
      before mem tr before mem' out' RUN) as NORMAL.
    pose proof (@quiet_execution_silent fe ge locals before mem body tr before mem' out' RUN
      (@indexed_bound_body_quiet out iterator body FLAT)) as SILENT; subst tr out'.
    pose proof (@indexed_bound_test_eval ge locals before mem iterator bound word upper q qofs ITER BOUND READ) as KNOWN.
    assert (LT : Int.lt word upper = true) by (eapply readonly_test_determinate; [exact KNOWN|exact ACTIVE]).
    assert (STRICT : Int.signed word < Int.signed upper).
    { unfold Int.lt in LT; destruct (zlt (Int.signed word) (Int.signed upper)); [assumption|discriminate]. }
    apply (flattened_singleton_execution FLAT) in RUN.
    destruct (indexed_bound_body_store ITER RUN) as [other [other_base [value [POINTER STORE]]]].
    assert (SAME : Vptr other other_base = Vptr block base) by congruence; injection SAME; intros; subst.
    exists word; split; [exact ITER|split; [exact LOW|split; [exact STRICT|split; [exact OUT|split; [exact BOUND|split; [exact CACHE|]]]]]].
    eapply mint32_load_survives_apart_store; [exact STORE|exact READ|].
    specialize (APART (Int.signed word) ltac:(lia)); rewrite Int.repr_signed in APART; exact APART. }
  assert (WEAKEN : forall before mem,
    indexed_bound_snapshot iterator out bound cache block base q qofs upper true before mem ->
    indexed_bound_snapshot iterator out bound cache block base q qofs upper false before mem).
  { intros before mem [word [ITER [LOW [HIGH REST]]]]; exists word; split; [exact ITER|split; [exact LOW|split; [lia|exact REST]]]. }
  assert (INC : forall before mem tr exit mem' out',
    indexed_bound_snapshot iterator out bound cache block base q qofs upper true before mem ->
    exec_stmt fe ge locals before mem (Ssequence Sskip (counter_increment iterator)) tr exit mem' out' ->
    indexed_bound_snapshot iterator out bound cache block base q qofs upper false exit mem').
  { intros before mem tr exit mem' out' [word [ITER [LOW [HIGH [OUT [BOUND [CACHE READ]]]]]]] RUN.
    assert (ACTIVE : strict_counter_active iterator before) by
      (exists word; split; [exact ITER|pose proof (Int.signed_range upper); lia]).
    destruct (@strict_increment_execution_exact fe ge locals iterator before mem tr exit mem' out' ACTIVE RUN)
      as [_ [TEMPS [MEMORY _]]]; subst exit mem'; unfold increment_temps; rewrite ITER.
    exists (Int.add word Int.one); split; [apply PTree.gss|].
    assert (SIGNED : Int.signed (Int.add word Int.one) = Int.signed word + 1).
    { rewrite Int.add_signed; change (Int.signed Int.one) with 1; rewrite Int.signed_repr;
        [reflexivity|pose proof (Int.signed_range upper); change Int.min_signed with (-2147483648); lia]. }
    split; [rewrite SIGNED; lia|split; [rewrite SIGNED; lia|]].
    repeat rewrite PTree.gso by congruence; repeat split; assumption. }
  exact (proj1 (@strict_active_condition_transport fe ge locals iterator (indexed_bound_test iterator bound)
    (counter_condition iterator cache) body
    (indexed_bound_snapshot iterator out bound cache block base q qofs upper false)
    (indexed_bound_snapshot iterator out bound cache block base q qofs upper true)
    TEST BODY WEAKEN INC le memory trace after final outcome SOURCE INV)).
Qed.

Theorem indexed_bound_forward fe live iterator out bound cache body cap entry observed :
  iterator <> out -> iterator <> bound -> cache <> iterator -> cache <> bound -> cache <> out -> ~ In cache live ->
  flatten_region body = [indexed_bound_body out iterator] -> indexed_bound_domain iterator bound body entry ->
  indexed_bound_guard_property iterator out bound cap tt entry ->
  clight_fragment_run fe (indexed_bound_loop iterator bound body) entry observed ->
  exists transformed, clight_fragment_run fe (indexed_bound_candidate iterator bound cache body) entry transformed /\
    boundary_observe (public_exit_ports live) observed transformed.
Proof.
  intros IO IQ CI CQ CP FRESH FLAT [[word [upper [q [qofs [ITER [BOUND READ]]]]]] COMPLETE]
    [ZERO [RANGE APART]] SOURCE.
  unfold indexed_bound_word in RANGE, APART; rewrite BOUND, READ in RANGE, APART.
  destruct entry as [ge locals le memory], observed as [trace after final outcome].
  cbn [entry_temps entry_memory] in ZERO, BOUND, READ, APART.
  assert (SILENT : trace = E0) by
    (eapply quiet_execution_silent; [exact SOURCE|exact (@indexed_bound_source_quiet iterator bound out body FLAT)]).
  assert (NORMAL : outcome = Out_normal) by
    (eapply quiet_loop_normal; [exact (@indexed_bound_source_quiet iterator bound out body FLAT)|exact SOURCE]); subst trace outcome.
  destruct (@indexed_bound_source_step fe ge locals iterator bound out body le memory after final 0 upper q qofs
    FLAT ltac:(lia) ZERO BOUND READ SOURCE) as [block [base [value [next_memory [OUT [STORE TAIL]]]]]].
  assert (BODY_SCOPE : ~ In cache (statement_temps body)).
  { rewrite <- (flatten_statement_temps body); rewrite FLAT.
    cbn [concat map statement_temps expression_temps indexed_bound_body indexed_word_lvalue indexed_word_pointer pointer_temp].
    cbn; intuition congruence. }
  assert (PRIVATE : ~ In cache (statement_temps (indexed_bound_loop iterator bound body) ++ live)).
  { rewrite in_app_iff; cbn [indexed_bound_loop strict_frontend_loop statement_temps expression_temps
      indexed_bound_test indexed_bound_value word_load pointer_temp counter_increment].
    repeat rewrite in_app_iff; cbn; intuition congruence. }
  destruct (@structured_execution_temp_transport fe ge locals le memory (indexed_bound_loop iterator bound body)
    E0 after final Out_normal SOURCE (statement_temps (indexed_bound_loop iterator bound body) ++ live)
    (PTree.set cache (Vint upper) le) [iterator] (@indexed_bound_source_writes iterator bound out body FLAT)
    ltac:(unfold statement_scope; intros id IN; apply in_or_app; left; exact IN)
    (@temp_agree_set (statement_temps (indexed_bound_loop iterator bound body) ++ live) le cache (Vint upper) PRIVATE))
    as [target_after [TRANSPORT PUBLIC]].
  assert (INV : indexed_bound_snapshot iterator out bound cache block base q qofs upper false
    (PTree.set cache (Vint upper) le) memory).
  { exists Int.zero; split; [rewrite PTree.gso by congruence; exact ZERO|].
    change (Int.signed Int.zero) with 0; split; [lia|split; [lia|]].
    repeat rewrite PTree.gso by congruence; rewrite PTree.gss; repeat split; assumption. }
  assert (APART_ADDRESSES : forall k, 0 <= k < Int.signed upper ->
    Vptr block (indexed_word_offset base (Int.repr k)) <> Vptr q qofs).
  { intros k ACTIVE; exact (@indexed_alias_apart out bound k (Entry ge locals le memory) block base q qofs
      OUT BOUND (APART k ACTIVE)). }
  pose proof (@indexed_bound_loop_cached fe ge locals iterator out bound cache body block base q qofs upper
    (PTree.set cache (Vint upper) le) memory E0 target_after final Out_normal IO IQ CI FLAT APART_ADDRESSES INV TRANSPORT) as CACHED.
  exists (FragmentObservation E0 target_after final Out_normal); split.
  - unfold clight_fragment_run, indexed_bound_candidate; cbn [entry_ge entry_env entry_temps entry_memory fragment_trace fragment_temps fragment_memory fragment_outcome].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [|exact CACHED].
    apply exec_Sset; eapply indexed_bound_value_evaluation; eassumption.
  - unfold boundary_observe; cbn; split; [reflexivity|split; [reflexivity|split]].
    + eapply temp_agree_weaken; [|apply temp_agree_sym; exact PUBLIC]; intros id IN; apply in_or_app; right; exact IN.
    + apply memory_equivalent_refl.
Qed.
Print Assumptions indexed_bound_loop_cached.
Print Assumptions indexed_bound_forward.
