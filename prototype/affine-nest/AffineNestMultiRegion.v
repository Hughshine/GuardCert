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
From GuardAffineNest Require Import AffineNestMultiStaticPackage AffineNestMultiPresumption AffineNestMultiGuardExecution AffineNestMultiCandidateLocal.
Import ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

From Guard Require Import StatefulGuard.
From GuardMemory Require Import GuardMemoryStatefulLanguage.
From GuardAffineNest Require Import AffineNestFlagLanguage.
Definition affine_multi_guarded_region source parameters live allocated proposal
  (package:affine_multi_static_package source parameters live allocated proposal) code :=
  Ssequence(affine_multi_guard_code package)
    (Sifthenelse(Etempvar(affine_proposed_result proposal) type_int32s)
      (affine_multi_candidate_code proposal code) source).

Theorem affine_multi_stateful_execution source parameters live allocated proposal
  (package:affine_multi_static_package source parameters live allocated proposal) source_loop candidate pool code :
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
    (affine_multi_guarded_region package code) s observed.
Proof.
  intros POINTER_NAMES POINTER_PUBLIC LOW HIGH SPAN LOWER SHADOW_SCOPE VALIDATOR COMPILE setup p s observed SCOPE SOURCE.
  pose proof(affine_package_nest(affine_multi_guard package)) as NEST.
  pose proof(described_affine_source(affine_package_description(affine_multi_guard package))) as EXACT; rewrite NEST in EXACT.
  pose proof(described_affine_shapes(affine_package_description(affine_multi_guard package))) as SHAPES; rewrite NEST in SHAPES.
  assert(WRITES:writes_only(affine_nest_controls(affine_proposal_nest proposal)) source).
  { rewrite EXACT; apply affine_nest_source_writes; [exact SHAPES|exact(affine_leaf_writes(affine_package_leaf(affine_multi_guard package)))]. }
  set(language:=affine_flag_language(adapter_entry setup)(globalenv p) live).
  set(domain:=fun state=>exists observation, stateful_command_run language source state observation).
  set(presumption:=fun checked=>exists original,
    memory_stateful_public_frame live original checked /\ affine_multi_guard_flag parameters proposal original=true).
  assert(ENCODE_RUN:forall state, domain state -> exists accepted checked,
    stateful_test_run language (affine_multi_guard_code package,Etempvar(affine_proposed_result proposal) type_int32s)
      state accepted checked /\ memory_stateful_public_frame live state checked /\ (accepted=true -> presumption checked)).
  {
    intros [globals locals temps memory] [observation [GLOBAL [source_exit [final [RUN [PUBLIC MEMORY]]]]]].
    destruct(@affine_multi_guard_execution source parameters live allocated proposal package(adapter_entry setup) globals locals temps memory
      source_exit final RUN) as[checked [GUARD [FRAME RESULT]]].
    destruct(@affine_probe_result_test(affine_proposed_result proposal)
      (affine_multi_guard_flag parameters proposal(Entry globals locals temps memory)) globals locals checked memory RESULT)
      as[value [EVAL BOOL]].
    exists(affine_multi_guard_flag parameters proposal(Entry globals locals temps memory)),(Entry globals locals checked memory).
    split; [exists checked,value; repeat split; try assumption; reflexivity|].
    assert(PUBLIC_FRAME:memory_stateful_public_frame live(Entry globals locals temps memory)(Entry globals locals checked memory))
      by(repeat split; try reflexivity; exact FRAME).
    split; [exact PUBLIC_FRAME|intro ACCEPT; exists(Entry globals locals temps memory); auto]. }
  pose(ENCODE:=@ProjectedGuardEncoding clight_entry language domain presumption(memory_stateful_public_frame live)
    (affine_multi_guard_code package,Etempvar(affine_proposed_result proposal) type_int32s) ENCODE_RUN).
  eapply(@affine_flag_guard_preservation(adapter_entry setup)(globalenv p) live domain presumption source
    (affine_multi_candidate_code proposal code)(affine_nest_controls(affine_proposal_nest proposal)) ENCODE);
    [exact SCOPE|exact WRITES| | |exact SOURCE].
  - intros state observation RUN; exists observation; exact RUN.
  - intros checked observation [original [FRAME ACCEPT]] [GLOBAL [after [final [RUN [PUBLIC MEMORY]]]]].
    destruct original as[globals locals temps memory],checked as[next_ge next_locals next_temps next_memory].
    destruct FRAME as[GE [ENV [MEM AGREE]]]; cbn in GE,ENV,MEM,AGREE,ACCEPT,GLOBAL,RUN,PUBLIC,MEMORY |- *;
      subst next_ge next_locals next_memory.
    assert(REVERSE:temp_agree live next_temps temps) by(apply temp_agree_sym; exact AGREE).
    destruct(@structured_execution_temp_transport(adapter_entry setup) globals locals next_temps memory source E0 after final
      Out_normal RUN live temps(affine_nest_controls(affine_proposal_nest proposal)) WRITES SCOPE REVERSE)
      as[source_exit [SOURCE_RUN EXIT_FRAME]].
    assert(ENTRY:temp_agree(affine_package_context parameters proposal++affine_proposed_pointers proposal++live) temps next_temps).
    { intros identifier MEMBER; apply AGREE.
      unfold affine_package_context in MEMBER; repeat rewrite in_app_iff in MEMBER; cbn[List.In] in MEMBER.
      destruct MEMBER as[[PARAMETER|[ITERATOR|BAD]]|[POINTER|PUBLIC_ID]].
      - apply(affine_multi_parameters_public package); exact PARAMETER.
      - subst identifier; exact(affine_multi_root_public package).
      - contradiction.
      - apply POINTER_PUBLIC; exact POINTER.
      - exact PUBLIC_ID. }
    destruct(@affine_multi_candidate_local source parameters live proposal allocated package source_loop candidate pool code
      POINTER_NAMES LOW HIGH LOWER SHADOW_SCOPE VALIDATOR COMPILE(adapter_entry setup) globals locals temps next_temps
      memory source_exit final ENTRY ACCEPT SOURCE_RUN) as[finish [EXEC CANDIDATE_FRAME]].
    split; [exact GLOBAL|]; exists finish,final; split; [exact EXEC|split; [|exact MEMORY]].
    eapply temp_agree_trans; [exact PUBLIC|]; eapply temp_agree_trans; eassumption.
Qed.
Print Assumptions affine_multi_stateful_execution.

Theorem affine_multi_guarded_region_sound source parameters live allocated proposal
  (package:affine_multi_static_package source parameters live allocated proposal) source_loop candidate pool code :
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
  projected_region_contract live source(affine_multi_guarded_region package code).
Proof.
  intros POINTER_NAMES POINTER_PUBLIC LOW HIGH SPAN LOWER SHADOW_SCOPE VALIDATOR COMPILE
    setup p locals le target memory after final SCOPE AGREE SOURCE fn continuation.
  pose proof(affine_package_nest(affine_multi_guard package)) as NEST.
  pose proof(described_affine_source(affine_package_description(affine_multi_guard package))) as EXACT; rewrite NEST in EXACT.
  pose proof(described_affine_shapes(affine_package_description(affine_multi_guard package))) as SHAPES; rewrite NEST in SHAPES.
  assert(WRITES:writes_only(affine_nest_controls(affine_proposal_nest proposal)) source).
  { rewrite EXACT; apply affine_nest_source_writes; [exact SHAPES|exact(affine_leaf_writes(affine_package_leaf(affine_multi_guard package)))]. }
  destruct(@structured_execution_temp_transport(adapter_entry setup)(globalenv p) locals le memory source E0 after final
    Out_normal SOURCE live target(affine_nest_controls(affine_proposal_nest proposal)) WRITES SCOPE AGREE)
    as[source_exit [TARGET_SOURCE SOURCE_AGREE]].
  assert(OBSERVED:stateful_command_run(affine_flag_language(adapter_entry setup)(globalenv p) live) source
    (Entry(globalenv p) locals target memory)(source_exit,final)).
  { split; [reflexivity|]; exists source_exit,final; split; [exact TARGET_SOURCE|split];
      [apply temp_agree_refl|apply memory_equivalent_refl]. }
  destruct(@affine_multi_stateful_execution source parameters live allocated proposal package source_loop candidate pool code
    POINTER_NAMES POINTER_PUBLIC LOW HIGH SPAN LOWER SHADOW_SCOPE VALIDATOR COMPILE setup p
    (Entry(globalenv p) locals target memory)(source_exit,final) SCOPE OBSERVED)
    as[GLOBAL [next [result [EXEC [PUBLIC MEMORY]]]]].
  destruct(@exec_stmt_steps(adapter_entry setup) p _ _ _ _ _ _ _ _ EXEC fn continuation) as[finish [STEPS EXIT]].
  inversion EXIT; subst finish; exists next,result; split; [exact STEPS|split; [eapply temp_agree_trans; eassumption|exact MEMORY]].
Qed.
Print Assumptions affine_multi_guarded_region_sound.
