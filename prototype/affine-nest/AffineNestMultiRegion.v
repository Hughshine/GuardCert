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

Definition affine_multi_guarded_region source parameters live allocated proposal
  (package:affine_multi_static_package source parameters live allocated proposal) code :=
  Ssequence(affine_multi_guard_code package)
    (Sifthenelse(Etempvar(affine_proposed_result proposal) type_int32s)
      (affine_multi_candidate_code proposal code) source).

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
    temps p locals le target memory after final SCOPE AGREE SOURCE fn continuation.
  pose proof(affine_package_nest(affine_multi_guard package)) as NEST.
  pose proof(described_affine_source(affine_package_description(affine_multi_guard package))) as EXACT; rewrite NEST in EXACT.
  pose proof(described_affine_shapes(affine_package_description(affine_multi_guard package))) as SHAPES; rewrite NEST in SHAPES.
  assert (WRITES:writes_only(affine_nest_controls(affine_proposal_nest proposal)) source).
  { rewrite EXACT; apply affine_nest_source_writes; [exact SHAPES|exact(affine_leaf_writes(affine_package_leaf(affine_multi_guard package)))]. }
  destruct(@structured_execution_temp_transport(adapter_entry temps)(globalenv p) locals le memory source E0 after final Out_normal
    SOURCE live target(affine_nest_controls(affine_proposal_nest proposal)) WRITES SCOPE AGREE)
    as [source_exit [TARGET_SOURCE SOURCE_AGREE]].
  destruct(@affine_multi_guard_execution source parameters live allocated proposal package(adapter_entry temps)(globalenv p) locals target memory
    source_exit final TARGET_SOURCE) as [guarded [GUARD [GUARD_FRAME RESULT]]].
  pose proof(@affine_probe_result_test(affine_proposed_result proposal)
    (affine_multi_guard_flag parameters proposal(Entry(globalenv p) locals target memory)) (globalenv p) locals guarded memory RESULT)
    as TEST; destruct TEST as [value [EVAL BOOL]].
  assert (SELECTED:exists finish,
    exec_stmt(adapter_entry temps)(globalenv p) locals guarded memory
      (if affine_multi_guard_flag parameters proposal(Entry(globalenv p) locals target memory)
        then affine_multi_candidate_code proposal code else source) E0 finish final Out_normal /\
    temp_agree live after finish).
  { destruct(affine_multi_guard_flag parameters proposal(Entry(globalenv p) locals target memory)) eqn:ACCEPT.
    - assert (ENTRY:temp_agree(affine_package_context parameters proposal++affine_proposed_pointers proposal++live) target guarded).
      { intros identifier MEMBER; apply GUARD_FRAME.
        unfold affine_package_context in MEMBER; repeat rewrite in_app_iff in MEMBER; cbn [List.In] in MEMBER.
        destruct MEMBER as [[PARAMETER|[ITERATOR|BAD]]|[POINTER|PUBLIC]].
        - apply(affine_multi_parameters_public package); exact PARAMETER.
        - subst identifier; exact(affine_multi_root_public package).
        - contradiction.
        - apply POINTER_PUBLIC; exact POINTER.
        - exact PUBLIC. }
      destruct(@affine_multi_candidate_local source parameters live proposal allocated package source_loop candidate pool code
         POINTER_NAMES LOW HIGH LOWER SHADOW_SCOPE VALIDATOR COMPILE(adapter_entry temps)(globalenv p) locals target guarded
        memory source_exit final ENTRY ACCEPT TARGET_SOURCE) as [finish [RUN FRAME]].
      exists finish; split; [exact RUN|eapply temp_agree_trans; eassumption].
    - assert (FRAME:temp_agree live target guarded).
      { exact GUARD_FRAME. }
      destruct(@structured_execution_temp_transport(adapter_entry temps)(globalenv p) locals target memory source E0 source_exit final Out_normal
        TARGET_SOURCE live guarded(affine_nest_controls(affine_proposal_nest proposal)) WRITES SCOPE FRAME)
        as [finish [RUN EXIT]].
      exists finish; split; [exact RUN|eapply temp_agree_trans; eassumption]. }
  destruct SELECTED as [finish [RUN FRAME]].
  assert (EXEC:exec_stmt(adapter_entry temps)(globalenv p) locals target memory(affine_multi_guarded_region package code) E0 finish final Out_normal).
  { unfold affine_multi_guarded_region; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact GUARD|].
    eapply exec_Sifthenelse with(v1:=value)(b:=affine_multi_guard_flag parameters proposal(Entry(globalenv p) locals target memory)); eassumption. }
  destruct(@exec_stmt_steps(adapter_entry temps) p _ _ _ _ _ _ _ _ EXEC fn continuation) as [next [STEPS EXIT]].
  inversion EXIT; subst next; exists finish,final; split; [exact STEPS|split; [exact FRAME|apply memory_equivalent_refl]].
Qed.
Print Assumptions affine_multi_guarded_region_sound.
