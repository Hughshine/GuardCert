From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryArrayBackend GuardMemoryFramedNested GuardMemoryPointerBackend GuardMemoryMultiPointerBackend GuardMemoryMultiPointerCells
  GuardMemoryFiniteFootprint GuardMemoryFootprintRestriction GuardMemoryLoopTrace
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation GuardMemoryParametricChecker
  GuardMemoryParametricInstructionChecker GuardMemoryParametricSourceClight GuardMemoryParametricRestore.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** C_opt transport: the same mapped-domain/dependence certificate is consumed
    at a restricted actual source footprint. Candidate code is compiled by the
    existing pointer backend. Neither the envelope nor this transport validates
    a proposed schedule in place of the certificate. *)
Theorem memory_parametric_model_compiled_pointer_candidate base source_model row context
  validator_bounds expression pointers extent encoder_bounds live pool candidate code
  fe ge locals temps parameters memory final :
  extent <= Int.max_signed+1 ->
  compile_memory_multi_pointer_buffer_loop pointers context encoder_bounds live pool candidate = Some code ->
  memory_parametric_model_candidate_certificate base source_model row context validator_bounds expression candidate ->
  MemoryNested.A.typed_view context parameters temps ->
  MemoryNested.A.env_within validator_bounds parameters ->
  MemoryFramedNested.N.A.env_within encoder_bounds parameters ->
  length parameters = length context ->
  memory_source_width_model (rectangle_stride base) row context expression parameters = true ->
  locations_nonalias (memory_restrict_locations
    (memory_footprint_allowed (memory_events_footprint (memory_loop_trace source_model parameters)))
    (memory_multi_pointer_locations temps extent)) ->
  L.loop_semantics source_model parameters
    (RuntimeState (memory_multi_pointer_locations temps extent) memory)
    (RuntimeState (memory_multi_pointer_locations temps extent) final) ->
  exists target,
    exec_stmt fe ge locals temps memory code E0 target final Out_normal /\
    temp_agree (context++pointers++live) temps target.
Proof.
  intros EXTENT COMPILE CERTIFICATE VIEW WITHIN ENCODER LENGTH WIDTH SEPARATED SOURCE.
  set (allowed := memory_footprint_allowed (memory_events_footprint (memory_loop_trace source_model parameters))).
  set (restricted := memory_restrict_locations allowed (memory_multi_pointer_locations temps extent)).
  assert (RESTRICTED : L.loop_semantics source_model parameters
    (RuntimeState restricted memory) (RuntimeState restricted final)).
  { change (L.loop_semantics source_model parameters
      (memory_restrict_state allowed (RuntimeState (memory_multi_pointer_locations temps extent) memory))
      (memory_restrict_state allowed (RuntimeState (memory_multi_pointer_locations temps extent) final))).
    eapply memory_restrict_loop_execution; [apply memory_loop_own_footprint_covered|exact SOURCE]. }
  pose proof (@CERTIFICATE parameters (RuntimeState restricted memory) (RuntimeState restricted final)
    LENGTH WITHIN WIDTH SEPARATED RESTRICTED) as VALIDATED.
  assert (TARGET : L.loop_semantics candidate parameters
    (RuntimeState (memory_multi_pointer_locations temps extent) memory)
    (RuntimeState (memory_multi_pointer_locations temps extent) final)).
  { eapply memory_unrestrict_loop_execution; exact VALIDATED. }
  destruct (@compile_memory_multi_pointer_buffer_loop_correct temps extent EXTENT fe ge locals pointers
    context encoder_bounds live pool candidate code parameters temps
    (RuntimeState (memory_multi_pointer_locations temps extent) memory)
    (RuntimeState (memory_multi_pointer_locations temps extent) final) memory
    COMPILE VIEW ENCODER TARGET eq_refl (temp_agree_refl pointers temps))
    as [target [target_memory [MEMORY [POINTERS [FRAME RUN]]]]].
  unfold memory_multi_pointer_buffer_view in MEMORY; inversion MEMORY; subst target_memory.
  exists target; auto.
Qed.

(** Public exit is part of the local contract, including the last affine inner
    bound. A model/source decoder supplies SOURCE_EXIT; the language service
    realizes that exit after the candidate's private control variables. *)
Theorem memory_parametric_pointer_candidate_restore base source_model row bound column inner_bound context
  validator_bounds expression pointers extent encoder_bounds live pool candidate code
  fe ge locals temps parameters memory final source_after valuation N upper :
  extent <= Int.max_signed+1 ->
  compile_memory_multi_pointer_buffer_loop pointers context encoder_bounds live pool candidate = Some code ->
  memory_parametric_model_candidate_certificate base source_model row context validator_bounds expression candidate ->
  MemoryNested.A.typed_view context parameters temps ->
  MemoryNested.A.env_within validator_bounds parameters ->
  MemoryFramedNested.N.A.env_within encoder_bounds parameters ->
  length parameters = length context ->
  memory_source_width_model (rectangle_stride base) row context expression parameters = true ->
  locations_nonalias (memory_restrict_locations
    (memory_footprint_allowed (memory_events_footprint (memory_loop_trace source_model parameters)))
    (memory_multi_pointer_locations temps extent)) ->
  L.loop_semantics source_model parameters
    (RuntimeState (memory_multi_pointer_locations temps extent) memory)
    (RuntimeState (memory_multi_pointer_locations temps extent) final) ->
  row <> bound -> row <> column -> row <> inner_bound -> bound <> column -> bound <> inner_bound ->
  In bound context ->
  (forall identifier, In identifier (memory_source_affine_parameters row expression) -> In identifier context) ->
  temps ! bound = Some (Vint (Int.repr N)) ->
  (forall identifier, In identifier (memory_source_affine_parameters row expression) ->
    temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  upper (N-1) = memory_source_affine_math (memory_source_set_valuation valuation row (N-1)) expression ->
  source_after = PTree.set row (Vint (Int.repr N))
    (memory_parametric_settle column inner_bound upper (N-1) temps) ->
  exists target,
    exec_stmt fe ge locals temps memory
      (Ssequence code (memory_parametric_restore row bound column inner_bound expression)) E0 target final Out_normal /\
    temp_agree live source_after target.
Proof.
  intros EXTENT COMPILE CERTIFICATE VIEW WITHIN ENCODER LENGTH WIDTH SEPARATED SOURCE
    RN RC RK NC NK BOUND_MEMBER PARAM_MEMBERS BOUND WORDS LAST SOURCE_EXIT.
  destruct (@memory_parametric_model_compiled_pointer_candidate base source_model row context validator_bounds
    expression pointers extent encoder_bounds live pool candidate code fe ge locals temps parameters memory final
    EXTENT COMPILE CERTIFICATE VIEW WITHIN ENCODER LENGTH WIDTH SEPARATED SOURCE) as [private [RUN FRAME]].
  set (last_upper := fun i => memory_source_affine_math (memory_source_set_valuation valuation row i) expression).
  exists (PTree.set row (Vint (Int.repr N))
    (memory_parametric_settle column inner_bound last_upper (N-1) private)); split.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact RUN|].
    eapply memory_parametric_restore_execution; [exact RN|exact RC|exact RK|exact NC|exact NK| |].
    + rewrite FRAME by (apply in_or_app; left; exact BOUND_MEMBER); exact BOUND.
    + intros identifier MEMBER; rewrite FRAME by
        (apply in_or_app; left; apply PARAM_MEMBERS; exact MEMBER); apply WORDS; exact MEMBER.
  - rewrite SOURCE_EXIT.
    assert (PUBLIC : temp_agree live temps private).
    { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER.
      apply in_or_app; right; apply in_or_app; right; exact MEMBER. }
    assert (SAME : memory_parametric_settle column inner_bound last_upper (N-1) private =
      memory_parametric_settle column inner_bound upper (N-1) private).
    { unfold memory_parametric_settle,last_upper; rewrite <-LAST; reflexivity. }
    rewrite SAME; apply memory_parametric_exit_frame; exact PUBLIC.
Qed.

Print Assumptions memory_parametric_model_compiled_pointer_candidate.
Print Assumptions memory_parametric_pointer_candidate_restore.
