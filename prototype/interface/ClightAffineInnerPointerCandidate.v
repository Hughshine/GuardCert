From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame ClightRectangularStore
  ClightCountedLoop ClightFrontendLoopProtocol ClightPureExpr.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryPointerBackend
  GuardMemoryMultiPointerBackend GuardMemoryMultiPointerCells GuardMemoryAffineSourceExpressions
  GuardMemoryAffineSourceValuation GuardMemoryAffineSourceContext GuardMemoryAffineSourceLoop
  GuardMemoryParametricGuard GuardMemoryParametricSourceDomain GuardMemoryParametricSourceClight GuardMemoryParametricRestore
  GuardMemoryParametricChecker GuardMemoryParametricInstructionChecker GuardMemoryAffinePointerCandidate GuardMemoryLoopTrace
  GuardMemoryFiniteFootprint GuardMemoryFootprintRestriction GuardMemoryAffineParameterPointerFootprint
  GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain GuardMemoryAffineInnerPointerRegionSource.
From GuardInterface Require Import ClightAffineInnerPointerSourceGuard ClightAffineInnerPointerCandidateGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_inner_pointer_candidate_certificate source (package : memory_affine_inner_pointer_package source)
  validator_bounds candidate :=
  memory_parametric_model_candidate_certificate (affine_inner_pointer_candidate_base package)
    (memory_affine_inner_pointer_region_model package) (affine_inner_pointer_row (affine_inner_pointer_shape package))
    (memory_affine_inner_pointer_region_context package) validator_bounds (affine_inner_pointer_expression package) candidate.
Definition check_affine_inner_pointer_model source (package : memory_affine_inner_pointer_package source)
  validator_bounds candidate steps :=
  checked_parametric_model_candidate (affine_inner_pointer_candidate_base package)
    (memory_affine_inner_pointer_region_model package) (affine_inner_pointer_pointers package)
    (affine_inner_pointer_row (affine_inner_pointer_shape package)) (memory_affine_inner_pointer_region_context package)
    validator_bounds (affine_inner_pointer_expression package) candidate steps.
Theorem check_affine_inner_pointer_model_sound source (package : memory_affine_inner_pointer_package source)
  validator_bounds candidate steps :
  mayReturn (check_affine_inner_pointer_model package validator_bounds candidate steps) true ->
  affine_inner_pointer_candidate_certificate package validator_bounds candidate.
Proof. apply checked_parametric_model_candidate_correct. Qed.

(** The optimizer's certificate and the actual language lowering are bound to
    the same candidate. The runtime guard separately establishes their two
    range environments, on the source-derived entry domain. *)
Record affine_inner_pointer_candidate_package source (package : memory_affine_inner_pointer_package source) live := {
  affine_inner_candidate_validator_bounds : list MemoryNested.A.interval;
  affine_inner_candidate_encoder_bounds : list MemoryFramedNested.N.A.interval;
  affine_inner_candidate_loop : L.stmt;
  affine_inner_candidate_pool : list (ident * ident);
  affine_inner_candidate_code : statement;
  affine_inner_candidate_compiled : compile_memory_multi_pointer_buffer_loop (affine_inner_pointer_pointers package)
    (memory_affine_inner_pointer_region_context package) affine_inner_candidate_encoder_bounds live affine_inner_candidate_pool
    affine_inner_candidate_loop = Some affine_inner_candidate_code;
  affine_inner_candidate_certificate : affine_inner_pointer_candidate_certificate package
    affine_inner_candidate_validator_bounds affine_inner_candidate_loop
}.
Definition affine_inner_pointer_candidate_statement source (package : memory_affine_inner_pointer_package source)
  live (candidate : affine_inner_pointer_candidate_package package live) :=
  Ssequence (affine_inner_candidate_code candidate)
    (memory_parametric_restore (affine_inner_pointer_row (affine_inner_pointer_shape package))
      (affine_inner_pointer_bound (affine_inner_pointer_shape package))
      (affine_inner_pointer_column (affine_inner_pointer_shape package))
      (affine_inner_pointer_inner_bound (affine_inner_pointer_shape package)) (affine_inner_pointer_expression package)).

Theorem affine_inner_pointer_candidate_execution source (package : memory_affine_inner_pointer_package source)
  live (candidate : affine_inner_pointer_candidate_package package live) fe ge locals temps memory after final :
  affine_inner_pointer_ready package (Entry ge locals temps memory) ->
  affine_inner_pointer_source_nonalias package (Entry ge locals temps memory) ->
  affine_inner_pointer_candidate_ranges package (affine_inner_candidate_validator_bounds candidate)
    (affine_inner_candidate_encoder_bounds candidate) (Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists target, exec_stmt fe ge locals temps memory (affine_inner_pointer_candidate_statement candidate) E0 target final Out_normal /\
    temp_agree live after target.
Proof.
  intros READY SEPARATED [VALIDATOR ENCODER] SOURCE.
  set (shape := affine_inner_pointer_shape package).
  set (context := memory_affine_inner_pointer_region_context package).
  set (parameters := memory_source_parameter_values context (Entry ge locals temps memory)).
  set (valuation := fun id => Int.signed (temp_word id temps)).
  set (N := valuation (affine_inner_pointer_bound shape)).
  assert (DOMAIN : memory_affine_inner_pointer_completed fe shape (Entry ge locals temps memory)).
  { exists after,final; unfold shape; rewrite <- (affine_inner_pointer_source_exact (affine_inner_pointer_syntax package)); exact SOURCE. }
  assert (MEMBERS : forall identifier,
    In identifier (memory_source_affine_parameters (affine_inner_pointer_row shape) (affine_inner_pointer_expression package)) ->
    In identifier context).
  { intros identifier MEMBER; unfold context,memory_affine_inner_pointer_region_context.
    apply in_or_app; left; unfold memory_affine_inner_pointer_parameters; apply in_or_app; left.
    apply memory_source_context_read; apply memory_source_affine_parameter_member in MEMBER; tauto. }
  assert (BOUND_MEMBER : In (affine_inner_pointer_bound shape) context).
  { unfold context,memory_affine_inner_pointer_region_context,memory_affine_inner_pointer_parameters,
      memory_affine_inner_pointer_header,memory_source_context; apply in_or_app; left; apply in_or_app; left; cbn; auto. }
  assert (WORDS : forall identifier, In identifier context -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))).
  { intros identifier MEMBER.
    destruct (@memory_source_typed_word context parameters temps identifier (affine_inner_pointer_ready_view READY) MEMBER)
      as [word LOOK].
    unfold valuation,temp_word; rewrite LOOK,Int.repr_signed; reflexivity. }
  destruct (@memory_affine_inner_pointer_region_source_under_ranges source package fe ge locals temps memory after final
    (affine_inner_pointer_ready_header READY) (affine_inner_pointer_ready_width READY)
    (affine_inner_pointer_ready_ranges READY) SOURCE) as [MODEL EXIT].
  assert (WIDTH : memory_source_width_model (affine_inner_pointer_column_limit package) (affine_inner_pointer_row shape)
    context (affine_inner_pointer_expression package) parameters = true).
  { apply affine_inner_pointer_ready_width_model with (fe:=fe); assumption. }
  assert (LAST : L.eval_expr ((N-1)::parameters) (affine_inner_pointer_encoded package) =
    memory_source_affine_math (memory_source_set_valuation valuation (affine_inner_pointer_row shape) (N-1))
      (affine_inner_pointer_expression package)).
  { apply memory_source_loop_expression_value; exact (affine_inner_pointer_full_encoding (affine_inner_pointer_syntax package)). }
  assert (NONALIAS : locations_nonalias (memory_restrict_locations
    (memory_footprint_allowed (memory_events_footprint (memory_loop_trace (memory_affine_inner_pointer_region_model package) parameters)))
    (memory_multi_pointer_locations temps (affine_inner_pointer_extent package)))).
  { unfold affine_inner_pointer_source_nonalias,memory_affine_parameter_pointer_footprint in SEPARATED.
    unfold memory_affine_inner_pointer_region_model,memory_affine_inner_pointer_region_context,
      memory_affine_inner_pointer_region_instructions.
    unfold parameters,context,memory_source_parameter_values in SEPARATED; rewrite length_map in SEPARATED; exact SEPARATED. }
  eapply (@memory_parametric_pointer_candidate_restore (affine_inner_pointer_candidate_base package)
    (memory_affine_inner_pointer_region_model package) (affine_inner_pointer_row shape) (affine_inner_pointer_bound shape)
    (affine_inner_pointer_column shape) (affine_inner_pointer_inner_bound shape) context
    (affine_inner_candidate_validator_bounds candidate) (affine_inner_pointer_expression package)
    (affine_inner_pointer_pointers package) (affine_inner_pointer_extent package)
    (affine_inner_candidate_encoder_bounds candidate) live (affine_inner_candidate_pool candidate)
    (affine_inner_candidate_loop candidate) (affine_inner_candidate_code candidate)
    fe ge locals temps parameters memory final after valuation N (fun i => L.eval_expr (i::parameters) (affine_inner_pointer_encoded package)));
    [ |exact (affine_inner_candidate_compiled candidate)|exact (affine_inner_candidate_certificate candidate)|
     exact (affine_inner_pointer_ready_view READY)|exact VALIDATOR|exact ENCODER| |exact WIDTH|exact NONALIAS|exact MODEL|
     exact (affine_inner_pointer_rn (affine_inner_pointer_syntax package))|
     exact (affine_inner_pointer_rc (affine_inner_pointer_syntax package))|
     exact (affine_inner_pointer_rk (affine_inner_pointer_syntax package))|
     exact (affine_inner_pointer_nc (affine_inner_pointer_syntax package))|
     exact (affine_inner_pointer_nk (affine_inner_pointer_syntax package))|
     exact BOUND_MEMBER|exact MEMBERS|apply WORDS; exact BOUND_MEMBER|intros; apply WORDS,MEMBERS; assumption|exact LAST|exact EXIT].
  - exact (proj1 (proj2 (affine_inner_pointer_window (affine_inner_pointer_syntax package)))).
  - unfold parameters,memory_source_parameter_values; apply length_map.
Qed.

Print Assumptions check_affine_inner_pointer_model_sound.
Print Assumptions affine_inner_pointer_candidate_execution.
