From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryAffineSourceExpressions GuardMemoryWindowCells.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestPackageGuard
  AffineNestPackageWords AffineNestGuardParameterCheck AffineNestRealDecode AffineNestSourceDecode AffineNestValuation.
Import ListNotations.
Set Implicit Arguments.

Definition affine_package_context parameters proposal := parameters++[affine_proposed_iterator proposal].
Definition affine_package_source_loop parameters proposal := affine_checked_nest_loop(affine_proposal_nest proposal)
  parameters [](affine_proposed_operations proposal)(L.Var(length parameters)).

Theorem affine_package_source_decode source parameters live proposal
  (package:affine_guard_package source parameters live proposal) source_loop
  fe ge locals temps memory after final :
  (forall identifier, In identifier(affine_proposed_pointers proposal) -> ~In identifier(affine_nest_mutated(affine_proposal_nest proposal))) ->
  affine_package_source_loop parameters proposal=Some source_loop ->
  affine_package_guard_flag parameters proposal(Entry ge locals temps memory)=true ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  L.loop_semantics source_loop (map(affine_word_valuation temps)(affine_package_context parameters proposal))
    (RuntimeState(window_multi_pointer_locations temps(affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal)) memory)
    (RuntimeState(window_multi_pointer_locations temps(affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal)) final).
Proof.
  intros POINTERS LOWER ACCEPT SOURCE.
  pose proof(@affine_package_accepted_word_view source parameters live proposal package fe ge locals temps memory after final ACCEPT SOURCE) as WORDS.
  destruct(@affine_package_root_words source parameters live proposal package fe ge locals temps memory after final SOURCE)
    as [[iterator_word ITERATOR] [bound_word BOUND]].
  destruct(@affine_package_guard_execution source parameters live proposal package fe ge locals temps memory after final SOURCE)
    as [guarded [GUARD [FRAME [RESULT DOMAIN]]]]; specialize(DOMAIN ACCEPT).
  pose proof(affine_package_nest package) as NEST.
  pose proof(described_affine_source(affine_package_description package)) as EXACT; rewrite NEST in EXACT; rewrite EXACT in SOURCE.
  pose proof(described_affine_shapes(affine_package_description package)) as SHAPES; rewrite NEST in SHAPES.
  pose proof(@affine_nest_fresh_controls _ (described_affine_fresh(affine_package_description package))) as FRESH; rewrite NEST in FRESH.
  pose proof(described_affine_dependencies(affine_package_description package)) as DEPENDENCIES; rewrite NEST in DEPENDENCIES.
  unfold affine_package_context; rewrite map_app; cbn [map].
  pose proof(@affine_checked_nest_source_decode(affine_proposal_nest proposal)
    (affine_proposed_leaf_bounds proposal)(affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal)
    parameters [](affine_proposed_pointers proposal)(affine_proposed_operations proposal)(affine_package_leaf package)
    fe ge locals temps(affine_word_valuation temps)(affine_word_valuation temps(affine_proposed_iterator proposal))
    (L.Var(length parameters)) source_loop temps memory after final
    [affine_word_valuation temps(affine_proposed_iterator proposal)]) as DECODE.
  rewrite !app_nil_r in DECODE; eapply DECODE.
  - exact SHAPES.
  - exact FRESH.
  - exact DEPENDENCIES.
  - intros identifier MEMBER; apply in_app_or in MEMBER as [PARAMETER|POINTER].
    + exact(proj2(@check_affine_guard_parameters_sound _ _ _ _ _ (affine_package_used package) identifier PARAMETER)).
    + apply POINTERS; exact POINTER.
  - exact DOMAIN.
  - exact WORDS.
  - apply temp_agree_refl.
  - cbn [affine_nest_entry affine_proposal_nest memory_source_affine_math].
    unfold affine_word_valuation,temp_word; rewrite ITERATOR,BOUND,!Int.repr_signed; split; reflexivity.
  - exact LOWER.
  - cbn [L.eval_expr]; rewrite <-length_map with(f:=affine_word_valuation temps)(l:=parameters).
    apply nth_middle.
  - exact SOURCE.
Qed.
Print Assumptions affine_package_source_decode.
