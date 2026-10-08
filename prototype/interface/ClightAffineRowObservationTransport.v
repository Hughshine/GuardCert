From GuardInterface Require Import ClightAffineDomainFacts ClightAffineDomainRows ClightAffineDomainFootprints ClightAffineZeroSnapshotRows ClightAffineZeroSnapshotPrefix.
From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap ClightCountedLoop
  ClightLoopSyntax ClightRegionProgress ClightLoopExecution ClightRedundantSet CompCertMemoryActions
  ClightRectangularLoops ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain
  GuardMemoryParametricSourceClight
  GuardMemoryPointerSequence.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightWordReadSnapshots
  ClightAffineHeaderSnapshots ClightAffineSnapshotRows ClightAffineSnapshotSourceInputs
  ClightAffineSnapshotPrefix ClightAffineInnerPointerSourceGuard ClightAffinePreparedState ClightAffinePreparedRows
  ClightAffineSnapshotPreparation ClightAffinePointerGuard
  ClightActiveLoopTransport ClightAffineLoadedBoundTransport ClightObservedHeaderPrefix
  ClightQuietDeterminacy ClightStrictLoopProgress ClightStrictIteration
  ClightReadonlyBranching ClightReadonlyLoadedTreeSynthesis ClightAffineSnapshotTransport ClightAffineDomainFacts
  ClightAffineSnapshotRowObservation ClightAffineSnapshotSyntax.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Both separation and value-preserving services supply the same actual-row
    observation guarantee. Original execution is transported with its exact
    memory and public exits; the guard does not execute the source first. *)
Section TRANSPORT.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variables root child child_cache : ident.
Variable header : expr.
Let shape := affine_inner_pointer_shape package.
Let row := affine_inner_pointer_row shape.
Let cache := affine_inner_pointer_bound shape.
Let column := affine_inner_pointer_column shape.
Let inner_bound := affine_inner_pointer_inner_bound shape.
Let stable := affine_snapshot_stable package root child.
Let CERT := affine_inner_pointer_syntax package.
Hypothesis ROOT_FRESH : root<>row /\ root<>column /\ root<>inner_bound.
Hypothesis CHILD_FRESH : child<>row /\ child<>column /\ child<>inner_bound.
Hypothesis CHILD_CACHE_MEMBER : In child_cache stable.
Hypothesis HEADER_WORD : snapshot_word_expression header.
Hypothesis CACHED_BODY : affine_inner_pointer_outer_body shape=
  affine_snapshot_body package(snapshot_word_replace(single_snapshot_binding child child_cache)header).
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable entry : clight_entry.
Hypothesis READY : affine_zero_snapshot_ready package root child child_cache entry.
Let count := affine_prepared_count package entry.
Let observations := affine_snapshot_observations package root child child_cache entry.
Hypothesis ROW_PRESERVES : affine_snapshot_row_observation_preservation package root child child_cache header fe entry.

Definition affine_row_snapshot_execution_invariant limit current memory := exists i,
  0<=i<=limit /\ current!row=Some(Vint(Int.repr i)) /\
  temp_agree stable(entry_temps entry)current /\ header_observations_match observations memory.
Definition affine_row_snapshot_cached_source :=
  frontend_counted_loop row cache(affine_inner_pointer_outer_body shape).

Lemma affine_row_snapshot_row_private : ~In row stable.
Proof.
  intros [SAME|MEMBER]; [subst child; tauto|].
  pose proof(@affine_prepared_external_protected source package root ROOT_FRESH row MEMBER); tauto.
Qed.

Theorem affine_row_snapshot_loaded_to_cached current memory trace after final outcome :
  affine_row_snapshot_execution_invariant count current memory ->
  exec_stmt fe(entry_ge entry)(entry_env entry)current memory
    (affine_snapshot_source package root header)trace after final outcome ->
  exec_stmt fe(entry_ge entry)(entry_env entry)current memory
    affine_row_snapshot_cached_source trace after final outcome /\
  affine_row_snapshot_execution_invariant count after final.
Proof.
  intros INV SOURCE.
  assert(COUNT:0<count<=Int.max_signed).
  { pose proof(affine_domain_count_range(proj1 READY))as RANGE.
    assert(CAP:signed_range(affine_inner_pointer_row_limit package)).
    { pose proof(affine_inner_pointer_control_limits CERT)as CAPS; inversion CAPS; subst; tauto. }
    unfold count,signed_range in *; lia. }
  eapply strict_active_loop_transport with
    (invariant:=affine_row_snapshot_execution_invariant count)
    (body_invariant:=affine_row_snapshot_execution_invariant(count-1));
    [| | | |exact SOURCE|exact INV].
  - intros before mem flag [i [RANGE [ROW [FRAME READS]]]] TEST.
    unfold observations,affine_snapshot_observations,header_observations_match in READS;
      apply Forall_app in READS as [ROOT_OBS CHILD_OBS].
    destruct(@cached_signed_current_read root cache stable entry before mem
      (or_intror(or_introl eq_refl))(@affine_zero_snapshot_root_cache_member source package root child)
      (proj1(proj2 READY))FRAME ROOT_OBS)as [word [CACHE READ]].
    destruct(signed_load_inv READ)as [block [offset [POINTER LOAD]]].
    eapply loaded_bound_cached_test; [exact POINTER|exact LOAD|exact CACHE|exact TEST].
  - intros before mem tr exit mem' out [i [RANGE [ROW [FRAME READS]]]] ACTIVE RUN.
    assert(SMALL:0<=i<count).
    { pose proof(affine_zero_snapshot_actual_header ROOT_FRESH CHILD_FRESH READY RANGE ROW FRAME READS)as TEST.
      pose proof(readonly_test_determinate TEST ACTIVE)as FLAG; apply Z.ltb_lt in FLAG; lia. }
    pose proof(@quiet_execution_silent fe(entry_ge entry)(entry_env entry)before mem
      (affine_snapshot_body package header)tr exit mem' out RUN
      (@affine_setup_child_quiet column inner_bound header(affine_inner_pointer_body shape)
        (@memory_pointer_sequence_quiet _ _ (affine_inner_pointer_body_exact CERT))))as SILENT.
    pose proof(@normal_statement_execution fe(entry_ge entry)(entry_env entry)
      (affine_snapshot_body package header)
      (@affine_setup_child_normal column inner_bound header(affine_inner_pointer_body shape)
        (@memory_pointer_sequence_quiet _ _ (affine_inner_pointer_body_exact CERT)))
      before mem tr exit mem' out RUN)as NORMAL.
    subst tr out.
    destruct(@affine_zero_snapshot_actual_row_decode source package root child child_cache header
      ROOT_FRESH CHILD_FRESH CHILD_CACHE_MEMBER HEADER_WORD CACHED_BODY fe
      entry i before mem exit mem' READY SMALL ROW FRAME READS RUN)as [ITER [EXIT_ROW EXIT_FRAME]].
    change(exit!row=before!row)in EXIT_ROW.
    assert(CACHED:exec_stmt fe(entry_ge entry)(entry_env entry)before mem
      (affine_inner_pointer_outer_body shape)E0 exit mem' Out_normal).
    { assert(RECEIPTS:snapshot_word_receipts(single_snapshot_binding child child_cache)header
        (entry_ge entry)(entry_env entry)before mem).
      { unfold observations,affine_snapshot_observations,header_observations_match in READS;
          apply Forall_app in READS as [ROOT_OBS CHILD_OBS].
        exact(@single_snapshot_receipts header child child_cache stable entry before mem
          (or_introl eq_refl)CHILD_CACHE_MEMBER(proj2(proj2 READY))FRAME CHILD_OBS). }
      rewrite CACHED_BODY; unfold affine_snapshot_body,affine_setup_child in RUN|-*.
      apply(proj1(@snapshot_word_setup_execution fe(entry_ge entry)(entry_env entry)before mem
        inner_bound header
        (Ssequence(ClightRectangularLoops.rectangle_reset column)
          (frontend_counted_loop column inner_bound(affine_inner_pointer_body shape)))
        (single_snapshot_binding child child_cache)E0 exit mem' Out_normal HEADER_WORD RECEIPTS)); exact RUN. }
    assert(AFTER_READS:header_observations_match observations mem').
    { eapply ROW_PRESERVES; eassumption. }
    split; [exact CACHED|exists i; split; [lia|split; [rewrite EXIT_ROW; exact ROW|split]]].
    + eapply temp_agree_trans; [exact FRAME|exact EXIT_FRAME].
    + exact AFTER_READS.
  - intros before mem [i [RANGE REST]]; exists i; split; [lia|exact REST].
  - intros before mem tr exit mem' out [i [RANGE [ROW [FRAME READS]]]] RUN.
    destruct(@strict_increment_execution_exact fe(entry_ge entry)(entry_env entry)row
      before mem tr exit mem' out
      ltac:(exists(Int.repr i); split; [exact ROW|rewrite Int.signed_repr;
        change Int.min_signed with(-2147483648); lia])RUN)as [_ [TEMPS [MEMORY _]]].
    subst exit mem'; rewrite(@counter_increment_small row before i ROW).
    exists(i+1); split; [lia|split; [apply PTree.gss|split; [|exact READS]]].
    intros identifier MEMBER; rewrite PTree.gso by(intro SAME; subst identifier;
      exact(affine_row_snapshot_row_private MEMBER)); exact(FRAME identifier MEMBER).
Qed.

End TRANSPORT.

Theorem affine_row_snapshot_checked_cached_execution original(site:affine_snapshot_source_package original)
    fe ge locals temps memory after final :
  affine_snapshot_original_domain(snapshot_cached_package site)(snapshot_root site)(snapshot_child site)
    (snapshot_child_cache site)(snapshot_original_header site)fe(Entry ge locals temps memory) ->
  affine_domain_ready(snapshot_cached_package site)(Entry ge locals temps memory) ->
  affine_snapshot_row_observation_preservation(snapshot_cached_package site)(snapshot_root site)(snapshot_child site)
    (snapshot_child_cache site)(snapshot_original_header site)fe(Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory original E0 after final Out_normal ->
  exec_stmt fe ge locals temps memory(snapshot_cached_source site)E0 after final Out_normal.
Proof.
  intros DOMAIN READY STABLE SOURCE.
  set(entry:=Entry ge locals temps memory)in *.
  set(source:=snapshot_cached_source site).
  set(package:=snapshot_cached_package site)in *.
  set(shape:=affine_inner_pointer_shape package).
  set(row:=affine_inner_pointer_row shape).
  set(cache:=affine_inner_pointer_bound shape).
  set(root:=snapshot_root site).
  set(child:=snapshot_child site).
  set(child_cache:=snapshot_child_cache site).
  set(header:=snapshot_original_header site).
  pose proof(affine_inner_pointer_source_exact(affine_inner_pointer_syntax package))as EXACT.
  change(source=memory_affine_inner_pointer_source shape)in EXACT.
  rewrite EXACT.
  pose proof(@affine_zero_snapshot_prepared_entry source package root child child_cache header
    (snapshot_root_protected site)(snapshot_child_protected site)fe entry DOMAIN READY)as PREPARED.
  destruct(@affine_snapshot_initial_words source package root child child_cache header fe entry DOMAIN)
    as [ROW CACHE].
  assert(CAP:signed_range(affine_inner_pointer_row_limit package)).
  { pose proof(affine_inner_pointer_control_limits(affine_inner_pointer_syntax package))as CAPS;
      inversion CAPS; subst; tauto. }
  destruct(@memory_affine_inner_pointer_header_sound shape(affine_inner_pointer_row_limit package)entry
    CAP ROW CACHE(affine_domain_ready_header READY))as [ZERO REST].
  assert(INV:@affine_row_snapshot_execution_invariant source package root child child_cache entry
    (affine_prepared_count package entry)(entry_temps entry)(entry_memory entry)).
  { exists 0; split; [pose proof(affine_domain_count_range READY); lia|split; [exact ZERO|split]].
    - apply temp_agree_refl.
    - unfold affine_snapshot_observations,header_observations_match; apply Forall_app; split;
        apply cached_signed_initial_observations; [exact(proj1(proj2 PREPARED))|exact(proj2(proj2 PREPARED))]. }
  rewrite(snapshot_source_exact site)in SOURCE.
  exact(proj1(@affine_row_snapshot_loaded_to_cached source package root child child_cache header
    (snapshot_root_protected site)(snapshot_child_protected site)(snapshot_cache_member site)
    (snapshot_header_word site)(snapshot_cached_body_exact site)fe entry PREPARED STABLE
    (entry_temps entry)(entry_memory entry)E0 after final Out_normal INV SOURCE)).
Qed.

Print Assumptions affine_row_snapshot_loaded_to_cached.
Print Assumptions affine_row_snapshot_checked_cached_execution.
