From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop ClightTempFrame ClightTempFootprint.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryPointerBackend
  GuardMemoryFramedNested GuardMemoryBoundedSourceChecker GuardMemoryFootprintRestriction
  GuardMemoryWindowSingleRegistry GuardMemoryWindowCells GuardMemoryWindowBackend.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestPackageGuard
  AffineNestSourceDecode AffineNestPackageDecode AffineNestPackageRanges AffineNestSingleFootprint AffineNestShadowExit AffineNestShadowTransport.
From GuardAffineNest Require Import AffineNestMultiStaticPackage AffineNestMultiPresumption AffineNestPackageScanFootprint.
From GuardMemory Require Import GuardMemoryFiniteFootprint.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section MULTI_PREFIX.
Variable source : statement.
Variable parameters live : list ident.
Variable proposal : affine_guard_proposal.
Variable allocated : list ident.
Variable multi_package : affine_multi_static_package source parameters live allocated proposal.
Let package := affine_multi_guard multi_package.
Let nest := affine_proposal_nest proposal.
Let pointers := affine_proposed_pointers proposal.
Let lower := affine_proposed_window_lower proposal.
Let upper := affine_proposed_window_upper proposal.
Let context := affine_package_context parameters proposal.
Variable source_loop candidate : L.stmt.
Variable pool : list(ident*ident).
Variable code : statement.
Hypothesis POINTER_NAMES : forall identifier, In identifier pointers -> ~In identifier(affine_nest_mutated nest).
Hypothesis LOW : signed_range lower.
Hypothesis HIGH : signed_range(upper-1).
Hypothesis SPAN : 4*(upper-lower)<=Ptrofs.modulus.
Hypothesis LOWER : affine_package_source_loop parameters proposal=Some source_loop.
Hypothesis SCOPE : statement_scope live(affine_shadow_source nest).
Hypothesis VALIDATOR : memory_bounded_source_certificate(affine_package_validator_bounds proposal) source_loop context candidate.
Hypothesis COMPILE : compile_window_multi_pointer_buffer_loop pointers context(affine_package_encoder_bounds proposal) live pool candidate=Some code.

Theorem affine_multi_candidate_prefix fe ge locals temps target_entry memory after final :
  temp_agree(context++pointers++live) temps target_entry ->
  affine_multi_guard_flag parameters proposal(Entry ge locals temps memory)=true ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists target,
    exec_stmt fe ge locals target_entry memory code E0 target final Out_normal /\
    temp_agree live temps target.
Proof.
  intros ENTRY ACCEPT SOURCE.
  assert(NUMERIC:affine_package_guard_flag parameters proposal(Entry ge locals temps memory)=true).
  { unfold affine_multi_guard_flag in ACCEPT; apply andb_true_iff in ACCEPT; tauto. }
  pose proof(@affine_package_source_decode source parameters live proposal package source_loop fe ge locals temps memory after final
    POINTER_NAMES LOWER NUMERIC SOURCE) as LOOP.
  pose proof(@affine_package_context_typed source parameters live proposal package fe ge locals temps memory after final NUMERIC SOURCE) as SOURCE_VIEW.
  assert (VIEW:MemoryFramedNested.N.A.typed_view context(map(affine_word_valuation temps) context) target_entry).
  { eapply MemoryFramedNested.N.typed_view_frame; [|exact ENTRY|exact SOURCE_VIEW].
    intros identifier MEMBER; apply in_or_app; left; exact MEMBER. }
  set(allowed:=memory_footprint_allowed(affine_package_scan_cells parameters proposal temps)).
  set(restricted:=memory_restrict_locations allowed(window_multi_pointer_locations temps lower upper)).
  assert (NONALIAS:GuardMemoryInstr.NonAlias(RuntimeState restricted memory)).
  { exact(@affine_multi_guard_nonalias source parameters live allocated proposal multi_package
      fe ge locals temps memory after final ACCEPT SOURCE). }
  assert (COVERED:memory_loop_cells_covered allowed source_loop(map(affine_word_valuation temps) context)).
  { pose proof(memory_loop_own_footprint_covered source_loop(map(affine_word_valuation temps) context)) as COVERED.
    unfold context in COVERED.
    rewrite(affine_package_scan_footprint package temps LOWER) in COVERED; exact COVERED. }
  assert (RESTRICTED:L.loop_semantics source_loop(map(affine_word_valuation temps) context)
    (RuntimeState restricted memory)(RuntimeState restricted final)).
  { change(L.loop_semantics source_loop(map(affine_word_valuation temps) context)
      (memory_restrict_state allowed(RuntimeState(window_multi_pointer_locations temps lower upper) memory))
      (memory_restrict_state allowed(RuntimeState(window_multi_pointer_locations temps lower upper) final))).
    eapply memory_restrict_loop_execution; [exact COVERED|exact LOOP]. }
  pose proof(@VALIDATOR(map(affine_word_valuation temps) context)(RuntimeState restricted memory)(RuntimeState restricted final)
    ltac:(apply length_map)(@affine_package_validator_within source parameters live proposal package(Entry ge locals temps memory) NUMERIC)
    NONALIAS RESTRICTED) as VALIDATED.
  assert (TARGET:L.loop_semantics candidate(map(affine_word_valuation temps) context)
    (RuntimeState(window_multi_pointer_locations temps lower upper) memory)
    (RuntimeState(window_multi_pointer_locations temps lower upper) final)).
  { eapply memory_unrestrict_loop_execution; exact VALIDATED. }
  assert (POINTER_FRAME:temp_agree pointers temps target_entry).
  { eapply temp_agree_weaken; [|exact ENTRY]; intros identifier MEMBER; apply in_or_app; right; apply in_or_app; left; exact MEMBER. }
  destruct(@compile_window_multi_pointer_buffer_loop_correct temps lower upper LOW HIGH fe ge locals pointers context
    (affine_package_encoder_bounds proposal) live pool candidate code(map(affine_word_valuation temps) context) target_entry
    (RuntimeState(window_multi_pointer_locations temps lower upper) memory)
    (RuntimeState(window_multi_pointer_locations temps lower upper) final) memory
    COMPILE VIEW(@affine_package_encoder_within source parameters live proposal package(Entry ge locals temps memory) NUMERIC)
    TARGET eq_refl POINTER_FRAME) as [private [private_memory [MEMORY [POINTER_AFTER [FRAME EXEC]]]]].
  unfold window_multi_pointer_buffer_view in MEMORY; inversion MEMORY; subst private_memory.
  assert (PUBLIC:temp_agree live temps private).
  { eapply temp_agree_weaken; [|eapply temp_agree_trans; [exact ENTRY|exact FRAME]].
    intros identifier MEMBER; apply in_or_app; right; apply in_or_app; right; exact MEMBER. }
  exists private; split; assumption.
Qed.
End MULTI_PREFIX.
Print Assumptions affine_multi_candidate_prefix.
