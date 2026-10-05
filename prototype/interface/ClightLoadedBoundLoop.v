From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightCountedLoop ClightCountedProtocol
  ClightFrontendLoopProtocol ClightFrontendRegion ClightRegionProgress ClightLoopExecution ClightLoopSyntax
  ClightStraightLine ClightTempFrame ClightTempFootprint ClightProjectedExecution CompCertMemoryEquivalence.
From GuardInterface Require Import ClightReadonlyRewrite ClightRegionBoundary ClightReadonlyProjectedCompiler
  ClightStrictLoopProgress ClightStableLoopCondition ClightLoadedBoundSyntax ClightLoadedBoundGuard
  ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.

Definition loaded_bound_candidate iterator parameter cache body :=
  Ssequence (Sset cache (signed_load parameter)) (frontend_counted_loop iterator cache body).
Definition bound_snapshot_invariant out parameter cache block offset upper le memory :=
  le ! parameter = Some (Vptr block offset) /\ le ! out <> le ! parameter /\
  le ! cache = Some (Vint upper) /\ Mem.loadv Mint32 memory (Vptr block offset) = Some (Vint upper).

Lemma loaded_source_writes iterator parameter out body :
  flatten_region body = [loaded_bound_body out iterator] ->
  writes_only [iterator] (loaded_bound_loop iterator parameter body).
Proof.
  intro FLAT; unfold loaded_bound_loop, strict_frontend_loop, counter_increment; constructor.
  - constructor; [repeat constructor|].
    apply flatten_writes_certificate; rewrite FLAT; constructor; [constructor|constructor].
  - repeat constructor; cbn; auto.
Qed.
Lemma loaded_source_quiet iterator parameter out body :
  flatten_region body = [loaded_bound_body out iterator] ->
  quiet_statement (loaded_bound_loop iterator parameter body) = true.
Proof.
  intro FLAT; assert (BODY : quiet_statement body = true) by
    (apply flatten_quiet_certificate; rewrite FLAT; constructor; [reflexivity|constructor]).
  cbn [loaded_bound_loop strict_frontend_loop quiet_statement counter_increment]; rewrite BODY; reflexivity.
Qed.

Theorem loaded_bound_loop_cached fe ge locals iterator parameter out cache body block offset upper
  le memory trace after final outcome :
  iterator <> parameter -> iterator <> out -> cache <> iterator ->
  flatten_region body = [loaded_bound_body out iterator] ->
  bound_snapshot_invariant out parameter cache block offset upper le memory ->
  exec_stmt fe ge locals le memory (loaded_bound_loop iterator parameter body) trace after final outcome ->
  exec_stmt fe ge locals le memory (frontend_counted_loop iterator cache body) trace after final outcome.
Proof.
  intros IQ IO CI FLAT INV SOURCE.
  exact (proj1 (@strict_loop_condition_transport fe ge locals iterator
    (loaded_bound_test iterator parameter) (counter_condition iterator cache) body
    (bound_snapshot_invariant out parameter cache block offset upper)
    ltac:(intros before mem flag [Q [APART [CACHE READ]]] TEST;
      eapply loaded_bound_cached_test; eassumption)
    ltac:(intros before mem tr exit mem' out' [Q [APART [CACHE READ]]] RUN;
      assert (WRITES : writes_only [] body) by
        (apply flatten_writes_certificate; rewrite FLAT; constructor; [constructor|constructor]);
      pose proof (memory_body_temporaries_exact WRITES RUN) as TEMPS; subst exit;
      repeat split; try assumption; eapply loaded_bound_body_preserves; eassumption)
    ltac:(intros before mem tr exit mem' out' [Q [APART [CACHE READ]]] RUN;
      apply skip_prefix_exec in RUN; inversion RUN; subst;
      repeat split; try assumption;
      repeat rewrite PTree.gso by congruence; try assumption)
    le memory trace after final outcome SOURCE INV)).
Qed.

Theorem loaded_bound_forward fe live iterator parameter out cache body entry observed :
  iterator <> parameter -> iterator <> out -> cache <> iterator -> cache <> parameter -> cache <> out ->
  ~ In cache live -> flatten_region body = [loaded_bound_body out iterator] ->
  loaded_bound_domain iterator out parameter entry -> loaded_bound_property iterator out parameter tt entry ->
  clight_fragment_run fe (loaded_bound_loop iterator parameter body) entry observed ->
  exists transformed, clight_fragment_run fe (loaded_bound_candidate iterator parameter cache body) entry transformed /\
    boundary_observe (public_exit_ports live) observed transformed.
Proof.
  intros IQ IO CI CQ CP FRESH FLAT [DOMAIN ADDRESSES] [ZERO [ACTIVE APART]] SOURCE.
  destruct entry as [ge locals base memory], observed as [trace after final outcome].
  destruct DOMAIN as [x [upper [block [offset [I [Q READ]]]]]].
  cbn [entry_temps entry_memory] in Q, READ.
  change (base ! out <> base ! parameter) in APART.
  assert (BODY_SCOPE : ~ In cache (statement_temps body)).
  { rewrite <- (flatten_statement_temps body).
    rewrite FLAT; cbn [concat map statement_temps expression_temps loaded_bound_body signed_load signed_pointer_temp].
    cbn; intuition congruence. }
  assert (PRIVATE : ~ In cache (statement_temps (loaded_bound_loop iterator parameter body) ++ live)).
  { rewrite in_app_iff; cbn [loaded_bound_loop strict_frontend_loop statement_temps expression_temps
      loaded_bound_test signed_load signed_pointer_temp counter_increment].
    repeat rewrite in_app_iff; cbn; intuition congruence. }
  destruct (@structured_execution_temp_transport fe ge locals base memory
    (loaded_bound_loop iterator parameter body) trace after final outcome SOURCE
    (statement_temps (loaded_bound_loop iterator parameter body) ++ live) (PTree.set cache (Vint upper) base)
    [iterator] (@loaded_source_writes iterator parameter out body FLAT)
    ltac:(unfold statement_scope; intros id IN; apply in_or_app; left; exact IN)
    (@temp_agree_set (statement_temps (loaded_bound_loop iterator parameter body) ++ live) base cache (Vint upper) PRIVATE)) as [target_after [TRANSPORT PUBLIC]].
  assert (INV : bound_snapshot_invariant out parameter cache block offset upper
    (PTree.set cache (Vint upper) base) memory).
  { unfold bound_snapshot_invariant; repeat split; repeat rewrite PTree.gso by congruence;
      auto using PTree.gss. }
  pose proof (@loaded_bound_loop_cached fe ge locals iterator parameter out cache body block offset upper
    (PTree.set cache (Vint upper) base) memory trace target_after final outcome IQ IO CI FLAT INV TRANSPORT) as CACHED.
  exists (FragmentObservation trace target_after final outcome); split.
  - unfold clight_fragment_run, loaded_bound_candidate; cbn.
    replace trace with (E0 ** trace) by reflexivity; eapply exec_Sseq_1; [|exact CACHED].
    apply exec_Sset; apply eval_Elvalue with (loc := block) (ofs := offset) (bf := Full).
    + apply eval_Ederef, eval_Etempvar; exact Q.
    + apply deref_loc_value with (chunk := Mint32); [reflexivity|exact READ].
  - unfold boundary_observe; cbn; split; [reflexivity|split; [reflexivity|split]].
    + eapply temp_agree_weaken; [|apply temp_agree_sym; exact PUBLIC]; intros id IN; apply in_or_app; right; exact IN.
    + apply memory_equivalent_refl.
Qed.
Print Assumptions loaded_bound_loop_cached.
Print Assumptions loaded_bound_forward.
