From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From polcert.src Require Import TilingWitness.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame ClightRectangularStore
  ClightCountedLoop ClightFrontendLoopProtocol ClightPureExpr.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryPointerBackend
  GuardMemoryMultiPointerBackend GuardMemoryMultiPointerCells GuardMemoryAffineSourceExpressions
  GuardMemoryAffineSourceValuation GuardMemoryAffineSourceContext GuardMemoryAffineSourceLoop
  GuardMemoryAffineSourceEndpoints GuardMemoryAffineSourceEndpointEncoding
  GuardMemoryParametricGuard GuardMemoryParametricSourceDomain GuardMemoryParametricSourceClight GuardMemoryParametricRestore
  GuardMemoryParametricChecker GuardMemoryParametricInstructionChecker GuardMemoryAffinePointerCandidate GuardMemoryLoopTrace
  GuardMemoryParametricModelTiling
  GuardMemoryFiniteFootprint GuardMemoryFootprintRestriction GuardMemoryAffineParameterPointerFootprint
  GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain GuardMemoryAffineInnerPointerRegionSource GuardMemoryZeroWidthModel GuardMemoryZeroWidthPointerSource GuardMemoryZeroWidthPointerCandidate.
From GuardInterface Require Import ClightAffineInnerPointerSourceGuard ClightAffineInnerPointerCandidateGuard ClightAffineDomainFacts.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem affine_zero_pointer_ready_width_model source (package : memory_affine_inner_pointer_package source) fe entry :
  memory_affine_inner_pointer_completed fe (affine_inner_pointer_shape package) entry ->
  affine_domain_ready package entry ->
  memory_source_zero_width_model (affine_inner_pointer_column_limit package)
    (affine_inner_pointer_row (affine_inner_pointer_shape package)) (memory_affine_inner_pointer_region_context package)
    (affine_inner_pointer_expression package)
    (memory_source_parameter_values (memory_affine_inner_pointer_region_context package) entry) = true.
Proof.
  intros DOMAIN READY.
  set (shape := affine_inner_pointer_shape package).
  set (expression := affine_inner_pointer_expression package).
  set (context := memory_affine_inner_pointer_region_context package).
  set (valuation := fun id => Int.signed (temp_word id (entry_temps entry))).
  set (N := valuation (affine_inner_pointer_bound shape)).
  destruct (@memory_affine_inner_pointer_source_header_words source shape expression (affine_inner_pointer_encoded package)
    (affine_inner_pointer_row_limit package) (affine_inner_pointer_column_limit package)
    (affine_inner_pointer_header_limits package) (affine_inner_pointer_body_limits package)
    (affine_inner_pointer_body_parameters package) (affine_inner_pointer_pointers package)
    (affine_inner_pointer_scalars package) (affine_inner_pointer_extent package) (affine_inner_pointer_operations package)
    (affine_inner_pointer_syntax package) fe entry DOMAIN) as [ROW [BOUND WORDS]].
  assert (CAP : signed_range (affine_inner_pointer_row_limit package)).
  { pose proof (affine_inner_pointer_control_limits (affine_inner_pointer_syntax package)) as CAPS;
    inversion CAPS; subst; tauto. }
  pose proof (@memory_affine_inner_pointer_header_sound shape _ entry CAP ROW BOUND
    (affine_domain_ready_header READY)) as [_ [_ POSITIVE]].
  assert (POS : 0 < N) by exact (proj1 POSITIVE).
  assert (MATH : 0 <= memory_source_affine_math (memory_source_set_valuation valuation (affine_inner_pointer_row shape) 0) expression /\
    forall i, 0 <= i < N -> 0 <= memory_source_affine_math (memory_source_set_valuation valuation (affine_inner_pointer_row shape) i) expression <=
      affine_inner_pointer_column_limit package).
  { pose proof (affine_domain_ready_width READY) as WIDTH.
    unfold memory_affine_inner_pointer_width_property in WIDTH; split.
    - unfold valuation; rewrite <-memory_affine_inner_pointer_word_math; apply (proj1 (WIDTH 0 ltac:(rewrite memory_source_word_temp; exact (conj (Z.le_refl 0) POS)))).
    - intros i RANGE; unfold valuation; rewrite <-memory_affine_inner_pointer_word_math.
      apply WIDTH; rewrite memory_source_word_temp; exact RANGE. }
  destruct (@memory_source_loop_endpoint_encoding expression (affine_inner_pointer_row shape) context
    (affine_inner_pointer_encoded package) (affine_inner_pointer_full_encoding (affine_inner_pointer_syntax package)) (L.Constant 0))
    as [first FIRST].
  destruct (@memory_source_loop_endpoint_encoding expression (affine_inner_pointer_row shape) context
    (affine_inner_pointer_encoded package) (affine_inner_pointer_full_encoding (affine_inner_pointer_syntax package))
    (L.Sum (L.Var O) (L.Constant (-1)))) as [last LAST].
  change (memory_source_zero_width_model (affine_inner_pointer_column_limit package) (affine_inner_pointer_row shape)
    context expression (map valuation context) = true).
  unfold memory_source_zero_width_model,memory_source_endpoints; rewrite FIRST,LAST.
  unfold memory_source_zero_width_test; cbn [L.eval_test L.eval_expr].
  pose proof (@memory_source_endpoint_value expression (affine_inner_pointer_row shape) context (L.Constant 0) first valuation FIRST) as FIRST_VALUE.
  pose proof (@memory_source_endpoint_value expression (affine_inner_pointer_row shape) context
    (L.Sum (L.Var O) (L.Constant (-1))) last valuation LAST) as LAST_VALUE.
  cbn [L.eval_expr] in FIRST_VALUE,LAST_VALUE.
  change (L.eval_expr (@map positive Z valuation context) last = memory_source_affine_math
    (memory_source_set_valuation valuation (affine_inner_pointer_row shape) (N + -1)) expression) in LAST_VALUE.
  replace (N + -1) with (N-1) in LAST_VALUE by lia.
  change ((0 <=? L.eval_expr (@map positive Z valuation context) first) &&
    ((L.eval_expr (@map positive Z valuation context) first <=? affine_inner_pointer_column_limit package) &&
      ((0 <=? L.eval_expr (@map positive Z valuation context) last) &&
        (L.eval_expr (@map positive Z valuation context) last <=? affine_inner_pointer_column_limit package))) = true).
  rewrite FIRST_VALUE,LAST_VALUE.
  pose proof (proj2 MATH 0 ltac:(lia)) as START.
  pose proof (proj2 MATH (N-1) ltac:(lia)) as END.
  rewrite !andb_true_iff,!Z.leb_le; repeat split; lia.
Qed.

Definition affine_zero_pointer_candidate_certificate source (package : memory_affine_inner_pointer_package source)
  validator_bounds candidate :=
  memory_zero_width_candidate_certificate (affine_inner_pointer_column_limit package)
    (memory_affine_inner_pointer_region_model package) (affine_inner_pointer_row (affine_inner_pointer_shape package))
    (memory_affine_inner_pointer_region_context package) validator_bounds (affine_inner_pointer_expression package) candidate.
Definition check_affine_zero_pointer_model source (package : memory_affine_inner_pointer_package source)
  validator_bounds candidate steps :=
  checked_zero_width_model_candidate (affine_inner_pointer_column_limit package)
    (memory_affine_inner_pointer_region_model package) (affine_inner_pointer_pointers package)
    (affine_inner_pointer_row (affine_inner_pointer_shape package)) (memory_affine_inner_pointer_region_context package)
    validator_bounds (affine_inner_pointer_expression package) candidate steps.
Theorem check_affine_zero_pointer_model_sound source (package : memory_affine_inner_pointer_package source)
  validator_bounds candidate steps :
  mayReturn (check_affine_zero_pointer_model package validator_bounds candidate steps) true ->
  affine_zero_pointer_candidate_certificate package validator_bounds candidate.
Proof. apply checked_zero_width_model_candidate_correct. Qed.

Definition check_affine_zero_pointer_tiling_model source (package : memory_affine_inner_pointer_package source)
  validator_bounds candidate witnesses :=
  checked_zero_width_model_tiling (affine_inner_pointer_column_limit package)
    (memory_affine_inner_pointer_region_model package) (affine_inner_pointer_pointers package)
    (affine_inner_pointer_row (affine_inner_pointer_shape package)) (memory_affine_inner_pointer_region_context package)
    validator_bounds (affine_inner_pointer_expression package) candidate witnesses.
Theorem check_affine_zero_pointer_tiling_model_sound source (package : memory_affine_inner_pointer_package source)
  validator_bounds candidate witnesses :
  mayReturn (check_affine_zero_pointer_tiling_model package validator_bounds candidate witnesses) true ->
  affine_zero_pointer_candidate_certificate package validator_bounds candidate.
Proof. apply checked_zero_width_model_tiling_correct. Qed.

(** The optimizer's certificate and the actual language lowering are bound to
    the same candidate. The runtime guard separately establishes their two
    range environments, on the source-derived entry domain. *)
Record affine_zero_pointer_candidate_package source (package : memory_affine_inner_pointer_package source) live := {
  affine_zero_candidate_validator_bounds : list MemoryNested.A.interval;
  affine_zero_candidate_encoder_bounds : list MemoryFramedNested.N.A.interval;
  affine_zero_candidate_loop : L.stmt;
  affine_zero_candidate_pool : list (ident * ident);
  affine_zero_candidate_code : statement;
  affine_zero_candidate_compiled : compile_memory_multi_pointer_buffer_loop (affine_inner_pointer_pointers package)
    (memory_affine_inner_pointer_region_context package) affine_zero_candidate_encoder_bounds live affine_zero_candidate_pool
    affine_zero_candidate_loop = Some affine_zero_candidate_code;
  affine_zero_candidate_certificate : affine_zero_pointer_candidate_certificate package
    affine_zero_candidate_validator_bounds affine_zero_candidate_loop
}.
Definition affine_zero_pointer_candidate_statement source (package : memory_affine_inner_pointer_package source)
  live (candidate : affine_zero_pointer_candidate_package package live) :=
  Ssequence (affine_zero_candidate_code candidate)
    (memory_parametric_restore (affine_inner_pointer_row (affine_inner_pointer_shape package))
      (affine_inner_pointer_bound (affine_inner_pointer_shape package))
      (affine_inner_pointer_column (affine_inner_pointer_shape package))
      (affine_inner_pointer_inner_bound (affine_inner_pointer_shape package)) (affine_inner_pointer_expression package)).

Theorem affine_zero_pointer_candidate_execution source (package : memory_affine_inner_pointer_package source)
  live (candidate : affine_zero_pointer_candidate_package package live) fe ge locals temps memory after final :
  affine_domain_ready package (Entry ge locals temps memory) ->
  affine_inner_pointer_source_nonalias package (Entry ge locals temps memory) ->
  affine_inner_pointer_candidate_ranges package (affine_zero_candidate_validator_bounds candidate)
    (affine_zero_candidate_encoder_bounds candidate) (Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists target, exec_stmt fe ge locals temps memory (affine_zero_pointer_candidate_statement candidate) E0 target final Out_normal /\
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
    destruct (@memory_source_typed_word context parameters temps identifier (affine_domain_ready_view READY) MEMBER)
      as [word LOOK].
    unfold valuation,temp_word; rewrite LOOK,Int.repr_signed; reflexivity. }
  destruct (@memory_zero_width_pointer_region_source_under_ranges source package fe ge locals temps memory after final
    (affine_domain_ready_header READY) (affine_domain_ready_width READY)
    (affine_domain_ready_view READY) (affine_domain_ready_ranges READY) SOURCE) as [MODEL EXIT].
  assert (WIDTH : memory_source_zero_width_model (affine_inner_pointer_column_limit package) (affine_inner_pointer_row shape)
    context (affine_inner_pointer_expression package) parameters = true).
  { apply affine_zero_pointer_ready_width_model with (fe:=fe); assumption. }
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
  eapply (@memory_zero_width_pointer_candidate_restore (affine_inner_pointer_column_limit package)
    (memory_affine_inner_pointer_region_model package) (affine_inner_pointer_row shape) (affine_inner_pointer_bound shape)
    (affine_inner_pointer_column shape) (affine_inner_pointer_inner_bound shape) context
    (affine_zero_candidate_validator_bounds candidate) (affine_inner_pointer_expression package)
    (affine_inner_pointer_pointers package) (affine_inner_pointer_extent package)
    (affine_zero_candidate_encoder_bounds candidate) live (affine_zero_candidate_pool candidate)
    (affine_zero_candidate_loop candidate) (affine_zero_candidate_code candidate)
    fe ge locals temps parameters memory final after valuation N (fun i => L.eval_expr (i::parameters) (affine_inner_pointer_encoded package)));
    [ |exact (affine_zero_candidate_compiled candidate)|exact (affine_zero_candidate_certificate candidate)|
     exact (affine_domain_ready_view READY)|exact VALIDATOR|exact ENCODER| |exact WIDTH|exact NONALIAS|exact MODEL|
     exact (affine_inner_pointer_rn (affine_inner_pointer_syntax package))|
     exact (affine_inner_pointer_rc (affine_inner_pointer_syntax package))|
     exact (affine_inner_pointer_rk (affine_inner_pointer_syntax package))|
     exact (affine_inner_pointer_nc (affine_inner_pointer_syntax package))|
     exact (affine_inner_pointer_nk (affine_inner_pointer_syntax package))|
     exact BOUND_MEMBER|exact MEMBERS|apply WORDS; exact BOUND_MEMBER|intros; apply WORDS,MEMBERS; assumption|exact LAST|exact EXIT].
  - exact (proj1 (proj2 (affine_inner_pointer_window (affine_inner_pointer_syntax package)))).
  - unfold parameters,memory_source_parameter_values; apply length_map.
Qed.

Print Assumptions check_affine_zero_pointer_model_sound.
Print Assumptions check_affine_zero_pointer_tiling_model_sound.
Print Assumptions affine_zero_pointer_candidate_execution.

Print Assumptions affine_zero_pointer_ready_width_model.
