From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Clight ClightBigstep Ctypes.
From Guard Require Import ClightGuard ClightCondition ClightNoWrap ClightCountedLoop ClightTempFrame
  ClightTempFootprint ClightProjectedExecution ClightPrivateRegion CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryBoundedSourceChecker GuardMemoryWindowBackend.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestSourceShape AffineNestSourceDecode
  AffineNestGuardPackage AffineNestPackageGuard AffineNestPackageDecode AffineNestPackageRanges
  AffineNestLeafModel AffineNestShadowExit AffineNestDomainGuard AffineNestCandidateLocal.
Import ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

From Guard Require Import StatefulGuard.
From GuardMemory Require Import GuardMemoryStatefulLanguage.
From GuardAffineNest Require Import AffineNestFlagLanguage.
Definition affine_guarded_region source parameters live proposal
  (package:affine_guard_package source parameters live proposal) code :=
  Ssequence(affine_package_guard_code package)
    (Sifthenelse(Etempvar(affine_proposed_result proposal) type_int32s)
      (affine_single_candidate_code proposal code) source).

Theorem affine_single_stateful_execution source parameters live proposal
  (package:affine_guard_package source parameters live proposal) pointer source_loop candidate pool code :
  affine_proposed_pointers proposal=[pointer] ->
  (forall identifier, In identifier(affine_proposed_pointers proposal) ->
    ~In identifier(affine_nest_mutated(affine_proposal_nest proposal))) ->
  (forall identifier, In identifier(affine_proposed_pointers proposal) -> In identifier live) ->
  signed_range(affine_proposed_window_lower proposal) -> signed_range(affine_proposed_window_upper proposal-1) ->
  4*(affine_proposed_window_upper proposal-affine_proposed_window_lower proposal)<=Ptrofs.modulus ->
  affine_package_source_loop parameters proposal=Some source_loop ->
  statement_scope live(affine_shadow_source(affine_proposal_nest proposal)) ->
  memory_bounded_source_certificate(affine_package_validator_bounds proposal) source_loop
    (affine_package_context parameters proposal) candidate ->
  compile_window_multi_pointer_buffer_loop(affine_proposed_pointers proposal)(affine_package_context parameters proposal)
    (affine_package_encoder_bounds proposal) live pool candidate=Some code ->
  forall setup p s observed, statement_scope live source ->
  stateful_command_run(affine_flag_language(adapter_entry setup)(globalenv p) live) source s observed ->
  stateful_command_run(affine_flag_language(adapter_entry setup)(globalenv p) live)
    (affine_guarded_region package code) s observed.
Proof.
  intros SINGLE POINTER_NAMES POINTER_PUBLIC LOW HIGH SPAN LOWER SHADOW_SCOPE VALIDATOR COMPILE setup p s observed SCOPE SOURCE.
  pose proof(affine_package_nest(package)) as NEST.
  pose proof(described_affine_source(affine_package_description(package))) as EXACT; rewrite NEST in EXACT.
  pose proof(described_affine_shapes(affine_package_description(package))) as SHAPES; rewrite NEST in SHAPES.
  assert(WRITES:writes_only(affine_nest_controls(affine_proposal_nest proposal)) source).
  { rewrite EXACT; apply affine_nest_source_writes; [exact SHAPES|exact(affine_leaf_writes(affine_package_leaf(package)))]. }
  set(language:=affine_flag_language(adapter_entry setup)(globalenv p) live).
  set(domain:=fun state=>exists observation, stateful_command_run language source state observation).
  set(presumption:=fun checked=>exists original,
    memory_stateful_public_frame(affine_package_context parameters proposal++affine_proposed_pointers proposal++live) original checked /\ affine_package_guard_flag parameters proposal original=true).
  assert(ENCODE_RUN:forall state, domain state -> exists accepted checked,
    stateful_test_run language (affine_package_guard_code package,Etempvar(affine_proposed_result proposal) type_int32s)
      state accepted checked /\ memory_stateful_public_frame live state checked /\ (accepted=true -> presumption checked)).
  {
    intros [globals locals temps memory] [observation [GLOBAL [source_exit [final [RUN [PUBLIC MEMORY]]]]]].
    destruct(@affine_package_guard_execution source parameters live proposal package(adapter_entry setup) globals locals temps memory
      source_exit final RUN) as[checked [GUARD [FRAME [RESULT UNUSED_DOMAIN]]]].
    destruct(@affine_probe_result_test(affine_proposed_result proposal)
      (affine_package_guard_flag parameters proposal(Entry globals locals temps memory)) globals locals checked memory RESULT)
      as[value [EVAL BOOL]].
    exists(affine_package_guard_flag parameters proposal(Entry globals locals temps memory)),(Entry globals locals checked memory).
    split; [exists checked,value; repeat split; try assumption; reflexivity|].
    assert(PUBLIC_FRAME:memory_stateful_public_frame live(Entry globals locals temps memory)(Entry globals locals checked memory))
      by(repeat split; try reflexivity; intros identifier MEMBER; apply FRAME; repeat rewrite in_app_iff; auto).
    split; [exact PUBLIC_FRAME|intro ACCEPT; exists(Entry globals locals temps memory); split; [|exact ACCEPT]].
    repeat split; try reflexivity; intros identifier MEMBER; apply FRAME.
    unfold affine_package_context in MEMBER; repeat rewrite in_app_iff in MEMBER; cbn[List.In] in MEMBER.
    repeat rewrite in_app_iff; cbn[List.In].
    destruct MEMBER as[[PARAMETER|[ITERATOR|BAD]]|[POINTER|PUBLIC_ID]];
      [tauto|tauto|contradiction|right; right; apply POINTER_PUBLIC; exact POINTER|tauto]. }
  pose(ENCODE:=@ProjectedGuardEncoding clight_entry language domain presumption(memory_stateful_public_frame live)
    (affine_package_guard_code package,Etempvar(affine_proposed_result proposal) type_int32s) ENCODE_RUN).
  eapply(@affine_flag_guard_preservation(adapter_entry setup)(globalenv p) live domain presumption source
    (affine_single_candidate_code proposal code)(affine_nest_controls(affine_proposal_nest proposal)) ENCODE);
    [exact SCOPE|exact WRITES| | |exact SOURCE].
  - intros state observation RUN; exists observation; exact RUN.
  - intros checked observation [original [FRAME ACCEPT]] [GLOBAL [after [final [RUN [PUBLIC MEMORY]]]]].
    destruct original as[globals locals temps memory],checked as[next_ge next_locals next_temps next_memory].
    destruct FRAME as[GE [ENV [MEM AGREE]]]; cbn in GE,ENV,MEM,AGREE,ACCEPT,GLOBAL,RUN,PUBLIC,MEMORY |- *;
      subst next_ge next_locals next_memory.
    assert(LIVE:temp_agree live temps next_temps).
    { intros identifier MEMBER; apply AGREE; repeat rewrite in_app_iff; auto. }
    assert(REVERSE:temp_agree live next_temps temps) by(apply temp_agree_sym; exact LIVE).
    destruct(@structured_execution_temp_transport(adapter_entry setup) globals locals next_temps memory source E0 after final
      Out_normal RUN live temps(affine_nest_controls(affine_proposal_nest proposal)) WRITES SCOPE REVERSE)
      as[source_exit [SOURCE_RUN EXIT_FRAME]].
    pose proof AGREE as ENTRY.
    destruct(@affine_single_candidate_local source parameters live proposal package pointer source_loop candidate pool code
      SINGLE POINTER_NAMES LOW HIGH SPAN LOWER SHADOW_SCOPE VALIDATOR COMPILE(adapter_entry setup) globals locals temps next_temps
      memory source_exit final ENTRY ACCEPT SOURCE_RUN) as[finish [EXEC CANDIDATE_FRAME]].
    split; [exact GLOBAL|]; exists finish,final; split; [exact EXEC|split; [|exact MEMORY]].
    eapply temp_agree_trans; [exact PUBLIC|]; eapply temp_agree_trans; eassumption.
Qed.
Print Assumptions affine_single_stateful_execution.

Theorem affine_guarded_region_sound source parameters live proposal
  (package:affine_guard_package source parameters live proposal) pointer source_loop candidate pool code :
  affine_proposed_pointers proposal=[pointer] ->
  (forall identifier, In identifier(affine_proposed_pointers proposal) ->
    ~In identifier(affine_nest_mutated(affine_proposal_nest proposal))) ->
  (forall identifier, In identifier(affine_proposed_pointers proposal) -> In identifier live) ->
  signed_range(affine_proposed_window_lower proposal) -> signed_range(affine_proposed_window_upper proposal-1) ->
  4*(affine_proposed_window_upper proposal-affine_proposed_window_lower proposal)<=Ptrofs.modulus ->
  affine_package_source_loop parameters proposal=Some source_loop ->
  statement_scope live(affine_shadow_source(affine_proposal_nest proposal)) ->
  memory_bounded_source_certificate(affine_package_validator_bounds proposal) source_loop
    (affine_package_context parameters proposal) candidate ->
  compile_window_multi_pointer_buffer_loop(affine_proposed_pointers proposal)(affine_package_context parameters proposal)
    (affine_package_encoder_bounds proposal) live pool candidate=Some code ->
  projected_region_contract live source(affine_guarded_region package code).
Proof.
  intros SINGLE POINTER_NAMES POINTER_PUBLIC LOW HIGH SPAN LOWER SHADOW_SCOPE VALIDATOR COMPILE
    setup p locals le target memory after final SCOPE AGREE SOURCE fn continuation.
  pose proof(affine_package_nest(package)) as NEST.
  pose proof(described_affine_source(affine_package_description(package))) as EXACT; rewrite NEST in EXACT.
  pose proof(described_affine_shapes(affine_package_description(package))) as SHAPES; rewrite NEST in SHAPES.
  assert(WRITES:writes_only(affine_nest_controls(affine_proposal_nest proposal)) source).
  { rewrite EXACT; apply affine_nest_source_writes; [exact SHAPES|exact(affine_leaf_writes(affine_package_leaf(package)))]. }
  destruct(@structured_execution_temp_transport(adapter_entry setup)(globalenv p) locals le memory source E0 after final
    Out_normal SOURCE live target(affine_nest_controls(affine_proposal_nest proposal)) WRITES SCOPE AGREE)
    as[source_exit [TARGET_SOURCE SOURCE_AGREE]].
  assert(OBSERVED:stateful_command_run(affine_flag_language(adapter_entry setup)(globalenv p) live) source
    (Entry(globalenv p) locals target memory)(source_exit,final)).
  { split; [reflexivity|]; exists source_exit,final; split; [exact TARGET_SOURCE|split];
      [apply temp_agree_refl|apply memory_equivalent_refl]. }
  destruct(@affine_single_stateful_execution source parameters live proposal package pointer source_loop candidate pool code
    SINGLE POINTER_NAMES POINTER_PUBLIC LOW HIGH SPAN LOWER SHADOW_SCOPE VALIDATOR COMPILE setup p
    (Entry(globalenv p) locals target memory)(source_exit,final) SCOPE OBSERVED)
    as[GLOBAL [next [result [EXEC [PUBLIC MEMORY]]]]].
  destruct(@exec_stmt_steps(adapter_entry setup) p _ _ _ _ _ _ _ _ EXEC fn continuation) as[finish [STEPS EXIT]].
  inversion EXIT; subst finish; exists next,result; split; [exact STEPS|split; [eapply temp_agree_trans; eassumption|exact MEMORY]].
Qed.
Print Assumptions affine_guarded_region_sound.
