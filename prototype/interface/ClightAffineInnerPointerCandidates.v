From Stdlib Require Import List Bool ZArith.
From compcert.common Require Import AST.
From compcert.lib Require Import Coqlib.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From polcert.src Require Import TilingWitness.
From Guard Require Import ClightCondition ClightPrivateRegion ClightPrivatePool.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryPointerBackend GuardMemoryMultiPointerBackend GuardMemoryMultiPointerCompiler GuardMemoryAffineReindex GuardMemoryParametricChecker
  GuardMemoryTiledCompiler GuardMemoryParametricWidth GuardMemoryParametricRestore GuardMemoryScheduleProducer GuardMemoryAffineInnerPointerSyntax
  GuardMemoryParametricTiling
  GuardMemoryAffineInnerPointerRegionSource GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceContext GuardMemoryParamAxisDescribe
  GuardMemoryScalarPointerComputeSyntax GuardMemoryMultiPointerIdentifiers.
From GuardMemory Require Import GuardMemoryGeneratedBounds.
From Guard Require Import ClightStraightLine.
From GuardInterface Require Import ClightAffinePointerGuard ClightAffineInnerPointerSourceGuard
  ClightAffineInnerPointerCandidateGuard ClightAffineInnerPointerCandidate ClightAffineInnerPointerPreservation
  ClightSourceObservation ClightObservedPointerSyntax ClightSequenceContracts.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Both callbacks are untrusted. Source caps and pointer lists are checked
    against the actual AST. The optimizer receives the checked nonrectangular
    source model, rather than a rectangular surrogate. *)
Record affine_inner_pointer_source_profile := AffineInnerPointerSourceProfile {
  affine_profile_row_cap : Z;
  affine_profile_column_cap : Z;
  affine_profile_header_caps : list Z;
  affine_profile_body_parameters : list ident;
  affine_profile_body_caps : list Z;
  affine_profile_pointers : list ident;
  affine_profile_extent : Z
}.
Definition affine_inner_pointer_profiler := statement -> option affine_inner_pointer_source_profile.
Definition describe_affine_inner_pointer_at source profile :=
  describe_memory_affine_pointer source (affine_profile_row_cap profile) (affine_profile_column_cap profile)
    (affine_profile_header_caps profile) (affine_profile_body_parameters profile) (affine_profile_body_caps profile)
    (affine_profile_pointers profile) (affine_profile_extent profile).

(** A convenience metadata producer, outside the trusted boundary. Every
    returned profile is still validated by describe_affine_inner_pointer_at. *)
Definition propose_affine_inner_pointer_profile row_cap column_cap geometry_cap extent source :=
  match propose_memory_affine_inner_pointer_shape source with
  | Some (shape,expression) =>
    let header := memory_affine_inner_pointer_header shape expression in
    let parameters := propose_memory_pointer_address_parameters
      ([affine_inner_pointer_row shape;affine_inner_pointer_column shape]++header)
      (flatten_region (affine_inner_pointer_body shape)) in
    let layout := memory_affine_inner_pointer_layout shape expression parameters in
    let statements := flatten_region (affine_inner_pointer_body shape) in
    let scalars := propose_memory_pointer_scalars layout statements in
    match propose_memory_scalar_pointer_computes extent layout scalars statements with
    | Some operations => Some (AffineInnerPointerSourceProfile row_cap column_cap
        (repeat geometry_cap (length (memory_source_other_parameters (affine_inner_pointer_row shape)
          (affine_inner_pointer_bound shape) expression))) parameters (repeat geometry_cap (length parameters))
        (memory_multi_pointer_operation_identifiers operations) extent)
    | None => None end
  | None => None end.

Record affine_inner_pointer_request := AffineInnerPointerRequest {
  affine_request_source : L.stmt;
  affine_request_context : list ident;
  affine_request_pointers : list ident;
  affine_request_instructions : list memory_instruction;
  affine_request_row_cap : Z;
  affine_request_column_cap : Z;
  affine_request_geometry_caps : list Z;
  affine_request_encoded_width : L.expr
}.
Definition affine_inner_pointer_request_of source (package : memory_affine_inner_pointer_package source) :=
  AffineInnerPointerRequest (memory_affine_inner_pointer_region_model package)
    (memory_affine_inner_pointer_region_context package) (affine_inner_pointer_pointers package)
    (memory_affine_inner_pointer_region_instructions package) (affine_inner_pointer_row_limit package)
    (affine_inner_pointer_column_limit package)
    ((affine_inner_pointer_row_limit package+1)::affine_inner_pointer_header_limits package++affine_inner_pointer_body_limits package)
    (affine_inner_pointer_encoded package).
(** Convenience tiler, outside the trusted boundary. Tile control ranges use
    the proposed source caps; the point guards retain the actual source bounds.
    The extracted tiling checker validates all coverage and quotient links. *)
Fixpoint propose_affine_inner_tiling_expression depth expression :=
  match expression with
  | L.Constant value => L.Constant value
  | L.Var position => L.Var (if Nat.ltb position depth then position else (position+2)%nat)
  | L.Sum first second => L.Sum (propose_affine_inner_tiling_expression depth first) (propose_affine_inner_tiling_expression depth second)
  | L.Mult factor value => L.Mult factor (propose_affine_inner_tiling_expression depth value)
  | L.Div value divisor => L.Div (propose_affine_inner_tiling_expression depth value) divisor
  | L.Mod value divisor => L.Mod (propose_affine_inner_tiling_expression depth value) divisor
  | L.Min first second => L.Min (propose_affine_inner_tiling_expression depth first) (propose_affine_inner_tiling_expression depth second)
  | L.Max first second => L.Max (propose_affine_inner_tiling_expression depth first) (propose_affine_inner_tiling_expression depth second)
  end.
Fixpoint propose_affine_inner_tiling_test depth test :=
  match test with
  | L.TConstantTest value => L.TConstantTest value
  | L.LE first second => L.LE (propose_affine_inner_tiling_expression depth first) (propose_affine_inner_tiling_expression depth second)
  | L.EQ first second => L.EQ (propose_affine_inner_tiling_expression depth first) (propose_affine_inner_tiling_expression depth second)
  | L.And first second => L.And (propose_affine_inner_tiling_test depth first) (propose_affine_inner_tiling_test depth second)
  | L.Or first second => L.Or (propose_affine_inner_tiling_test depth first) (propose_affine_inner_tiling_test depth second)
  | L.Not value => L.Not (propose_affine_inner_tiling_test depth value)
  end.
Fixpoint propose_affine_inner_tiling_body depth body : L.stmt :=
  match body with
  | L.Instr instruction arguments => L.Instr instruction (map (propose_affine_inner_tiling_expression depth) arguments)
  | L.Guard test body => L.Guard (propose_affine_inner_tiling_test depth test) (propose_affine_inner_tiling_body depth body)
  | L.Loop lower upper body => L.Loop (propose_affine_inner_tiling_expression depth lower)
      (propose_affine_inner_tiling_expression depth upper) (propose_affine_inner_tiling_body (S depth) body)
  | L.Seq statements => L.Seq (propose_affine_inner_tiling_bodies depth statements)
  end
with propose_affine_inner_tiling_bodies depth statements : L.stmt_list :=
  match statements with
  | L.SNil => L.SNil
  | L.SCons body rest => L.SCons (propose_affine_inner_tiling_body depth body) (propose_affine_inner_tiling_bodies depth rest)
  end.
Definition propose_affine_inner_pointer_tiling request row_width column_width :=
  if (0 <? row_width) && (0 <? column_width) then
    match affine_request_source request with
    | L.Loop lower upper (L.Loop inner_lower inner_upper body) =>
      let outer_inside := L.And (L.LE (memory_generated_lift (memory_generated_lift
        (memory_generated_lift (memory_generated_lift lower)))) (L.Var 1))
        (L.LE (L.Var 1) (L.Sum (memory_generated_lift (memory_generated_lift
          (memory_generated_lift (memory_generated_lift upper)))) (L.Constant (-1)))) in
      let inner_inside := L.And (L.LE (memory_parametric_tiled_expression inner_lower) (L.Var 0))
        (L.LE (L.Var 0) (L.Sum (memory_parametric_tiled_expression inner_upper) (L.Constant (-1)))) in
      let candidate := L.Loop (L.Constant 0)
        (L.Constant ((affine_request_row_cap request+row_width)/row_width))
        (L.Loop (L.Constant 0) (L.Constant ((affine_request_column_cap request+column_width-1)/column_width))
          (L.Loop (L.Mult row_width (L.Var 1)) (L.Sum (L.Mult row_width (L.Var 1)) (L.Constant row_width))
            (L.Loop (L.Mult column_width (L.Var 1)) (L.Sum (L.Mult column_width (L.Var 1)) (L.Constant column_width))
              (L.Guard (L.And outer_inside inner_inside) (propose_affine_inner_tiling_body 2 body))))) in
      Some (candidate,repeat (memory_parametric_tiling_witness (length (affine_request_context request)) row_width column_width)
        (length (affine_request_instructions request)))
    | _ => None end
  else None.

Inductive affine_inner_pointer_candidate_proposal :=
| AffineInnerMappedProposal (candidate : L.stmt) (steps : list memory_affine_reindex)
| AffineInnerTilingProposal (candidate : L.stmt) (witnesses : list statement_tiling_witness)
| AffineInnerScheduleProposal (schedules : list (list (list Z * Z))) (steps : list memory_affine_reindex).
Record affine_inner_pointer_proposal := AffineInnerPointerProposal {
  affine_proposal_validator_bounds : list MemoryNested.A.interval;
  affine_proposal_encoder_bounds : list MemoryFramedNested.N.A.interval;
  affine_proposal_candidate : affine_inner_pointer_candidate_proposal
}.
Definition affine_inner_pointer_proposer := affine_inner_pointer_request -> option affine_inner_pointer_proposal.

Definition checked_affine_inner_pointer_target source (package : memory_affine_inner_pointer_package source)
  loads validator_bounds encoder_bounds width alias code :=
  Ssequence (source_load_prefix loads)
    (tree_statement (affine_inner_pointer_candidate_guard_tree package width alias validator_bounds encoder_bounds)
      (Ssequence code (memory_parametric_restore (affine_inner_pointer_row (affine_inner_pointer_shape package))
        (affine_inner_pointer_bound (affine_inner_pointer_shape package))
        (affine_inner_pointer_column (affine_inner_pointer_shape package))
        (affine_inner_pointer_inner_bound (affine_inner_pointer_shape package)) (affine_inner_pointer_expression package))) source).

Definition check_affine_inner_pointer_certified_package live pool source (package : memory_affine_inner_pointer_package source)
  loads validator_bounds encoder_bounds candidate (check : CoreAlarmed.Base.imp bool) : CoreAlarmed.Base.imp (option statement) :=
  if source_observations_check (affine_inner_pointer_pointers package) loads then
    match compile_memory_source_width (affine_inner_pointer_column_limit package)
      (affine_inner_pointer_row (affine_inner_pointer_shape package))
      (memory_affine_inner_pointer_header (affine_inner_pointer_shape package) (affine_inner_pointer_expression package))
      (affine_inner_pointer_header_bounds (affine_inner_pointer_row_limit package) (affine_inner_pointer_header_limits package))
      (affine_inner_pointer_expression package),compile_affine_inner_pointer_package_envelopes package,
      private_counter_pairs pool with
    | Some width,Some alias,Some pairs =>
      match compile_memory_multi_pointer_buffer_loop (affine_inner_pointer_pointers package)
        (memory_affine_inner_pointer_region_context package) encoder_bounds live pairs candidate with
      | Some code => BIND valid <- check -;
        pure (if valid then Some (checked_affine_inner_pointer_target package loads validator_bounds encoder_bounds width alias code) else None)
      | None => pure None end
    | _,_,_ => pure None end
  else pure None.

Theorem check_affine_inner_pointer_certified_package_sound live pool source (package : memory_affine_inner_pointer_package source)
  loads validator_bounds encoder_bounds candidate check target :
  (mayReturn check true -> affine_inner_pointer_candidate_certificate package validator_bounds candidate) ->
  mayReturn (check_affine_inner_pointer_certified_package live pool package loads validator_bounds encoder_bounds candidate check)
    (Some target) ->
  PrivateRegion.projected_region_contract live (Ssequence (source_load_prefix loads) source) target.
Proof.
  intro CERTIFICATE; unfold check_affine_inner_pointer_certified_package.
  destruct (source_observations_check (affine_inner_pointer_pointers package) loads) eqn:OBSERVED;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_memory_source_width _ _ _ _ _) as [width|] eqn:WIDTH;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_affine_inner_pointer_package_envelopes package) as [alias|] eqn:ALIAS;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (private_counter_pairs pool) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_memory_multi_pointer_buffer_loop _ _ _ _ _ _) as [code|] eqn:COMPILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN;
    destruct valid; [injection RUN as <-|discriminate].
  pose (certified := @Build_affine_inner_pointer_candidate_package source package live
    validator_bounds encoder_bounds candidate pairs code COMPILE
    (CERTIFICATE VALID)).
  change (PrivateRegion.projected_region_contract live (Ssequence (source_load_prefix loads) source)
    (affine_inner_pointer_observed_candidate certified width alias loads)).
  apply affine_inner_pointer_observed_candidate_contract; assumption.
Qed.

Definition check_affine_inner_pointer_mapped_package live pool source (package : memory_affine_inner_pointer_package source)
  loads validator_bounds encoder_bounds candidate steps :=
  check_affine_inner_pointer_certified_package live pool package loads validator_bounds encoder_bounds candidate
    (check_affine_inner_pointer_model package validator_bounds candidate steps).
Theorem check_affine_inner_pointer_mapped_package_sound live pool source (package : memory_affine_inner_pointer_package source)
  loads validator_bounds encoder_bounds candidate steps target :
  mayReturn (check_affine_inner_pointer_mapped_package live pool package loads validator_bounds encoder_bounds candidate steps) (Some target) ->
  PrivateRegion.projected_region_contract live (Ssequence (source_load_prefix loads) source) target.
Proof.
  apply check_affine_inner_pointer_certified_package_sound; apply check_affine_inner_pointer_model_sound.
Qed.
Definition check_affine_inner_pointer_tiled_package live pool source (package : memory_affine_inner_pointer_package source)
  loads validator_bounds encoder_bounds candidate witnesses :=
  check_affine_inner_pointer_certified_package live pool package loads validator_bounds encoder_bounds candidate
    (check_affine_inner_pointer_tiling_model package validator_bounds candidate witnesses).
Theorem check_affine_inner_pointer_tiled_package_sound live pool source (package : memory_affine_inner_pointer_package source)
  loads validator_bounds encoder_bounds candidate witnesses target :
  mayReturn (check_affine_inner_pointer_tiled_package live pool package loads validator_bounds encoder_bounds candidate witnesses) (Some target) ->
  PrivateRegion.projected_region_contract live (Ssequence (source_load_prefix loads) source) target.
Proof.
  apply check_affine_inner_pointer_certified_package_sound; apply check_affine_inner_pointer_tiling_model_sound.
Qed.

(** Proposal normalization, outside the trusted boundary. Parameter-only
    generated guards can be proposed for removal because the independent
    checker compares under the original assumptions. Quotient bounds can be
    replaced by a coarse range and a division-cleared affine body condition.
    Every change is re-extracted and checked, including its exact point set. *)
Fixpoint affine_inner_candidate_expr_coordinates depth expression :=
  match expression with
  | L.Constant _ => false
  | L.Var position => Nat.ltb position depth
  | L.Sum first second | L.Min first second | L.Max first second =>
      affine_inner_candidate_expr_coordinates depth first || affine_inner_candidate_expr_coordinates depth second
  | L.Mult _ value | L.Div value _ | L.Mod value _ => affine_inner_candidate_expr_coordinates depth value
  end.
Fixpoint affine_inner_candidate_test_coordinates depth test :=
  match test with
  | L.TConstantTest _ => false
  | L.LE first second | L.EQ first second =>
      affine_inner_candidate_expr_coordinates depth first || affine_inner_candidate_expr_coordinates depth second
  | L.And first second | L.Or first second =>
      affine_inner_candidate_test_coordinates depth first || affine_inner_candidate_test_coordinates depth second
  | L.Not value => affine_inner_candidate_test_coordinates depth value
  end.
Fixpoint propose_affine_inner_candidate_normalization bounds depth candidate : L.stmt :=
  match candidate with
  | L.Instr instruction arguments => L.Instr instruction arguments
  | L.Guard test body =>
      let body := propose_affine_inner_candidate_normalization bounds depth body in
      if affine_inner_candidate_test_coordinates depth test
      then L.Guard (memory_generated_affine_test test) body else body
  | L.Seq statements => L.Seq (propose_affine_inner_candidates_normalization bounds depth statements)
  | L.Loop lower upper body =>
      match MemoryFramedNested.N.A.analyze bounds lower,MemoryFramedNested.N.A.analyze bounds upper with
      | Some first,Some last =>
          let inside := MemoryFramedNested.N.A.Interval (MemoryFramedNested.N.A.lower first)
            (MemoryFramedNested.N.A.upper last)::bounds in
          let body := propose_affine_inner_candidate_normalization inside (S depth) body in
          if memory_generated_division_free lower && memory_generated_division_free upper
          then L.Loop lower upper body
          else L.Loop (L.Constant (MemoryFramedNested.N.A.lower first)) (L.Constant (MemoryFramedNested.N.A.upper last))
            (L.Guard (memory_generated_le (memory_generated_lift lower) (L.Var 0))
              (L.Guard (memory_generated_le (L.Var 0) (L.Sum (memory_generated_lift upper) (L.Constant (-1)))) body))
      | _,_ => candidate end
  end
with propose_affine_inner_candidates_normalization bounds depth statements : L.stmt_list :=
  match statements with
  | L.SNil => L.SNil
  | L.SCons candidate rest => L.SCons (propose_affine_inner_candidate_normalization bounds depth candidate)
      (propose_affine_inner_candidates_normalization bounds depth rest)
  end.

(** Schedule generation and normalization propose a candidate. Only the
    independent mapped-domain/dependence checker licenses its installation. *)
Definition check_affine_inner_pointer_scheduled_package live pool source (package : memory_affine_inner_pointer_package source)
  loads validator_bounds encoder_bounds schedules steps :=
  let context := memory_affine_inner_pointer_region_context package in
  let arrays := affine_inner_pointer_pointers package in
  BIND generated <- memory_generate_scheduled_loop
    (memory_parametric_assumed_loop (affine_inner_pointer_candidate_base package)
      (affine_inner_pointer_row (affine_inner_pointer_shape package)) context validator_bounds
      (affine_inner_pointer_expression package) (memory_affine_inner_pointer_region_model package),context,
      map (fun identifier => (identifier,tt)) (context++arrays)) schedules -;
  match generated with
  | Some candidate => check_affine_inner_pointer_mapped_package live pool package loads
      validator_bounds encoder_bounds (propose_affine_inner_candidate_normalization encoder_bounds O candidate) steps
  | None => pure None end.
Theorem check_affine_inner_pointer_scheduled_package_sound live pool source (package : memory_affine_inner_pointer_package source)
  loads validator_bounds encoder_bounds schedules steps target :
  mayReturn (check_affine_inner_pointer_scheduled_package live pool package loads validator_bounds encoder_bounds schedules steps)
    (Some target) ->
  PrivateRegion.projected_region_contract live (Ssequence (source_load_prefix loads) source) target.
Proof.
  unfold check_affine_inner_pointer_scheduled_package; intro RUN; bind_imp_destruct RUN generated GENERATED.
  destruct generated as [candidate|];
    [eapply check_affine_inner_pointer_mapped_package_sound; exact RUN|apply mayReturn_pure in RUN; discriminate].
Qed.

Definition check_affine_inner_pointer_package live pool (propose : affine_inner_pointer_proposer)
  source (package : memory_affine_inner_pointer_package source) loads :=
  match propose (affine_inner_pointer_request_of package) with
  | Some proposal =>
    let validator_bounds := affine_proposal_validator_bounds proposal in
    let encoder_bounds := affine_proposal_encoder_bounds proposal in
    match affine_proposal_candidate proposal with
    | AffineInnerMappedProposal candidate steps => check_affine_inner_pointer_mapped_package live pool package loads
        validator_bounds encoder_bounds candidate steps
    | AffineInnerTilingProposal candidate witnesses => check_affine_inner_pointer_tiled_package live pool package loads
        validator_bounds encoder_bounds candidate witnesses
    | AffineInnerScheduleProposal schedules steps => check_affine_inner_pointer_scheduled_package live pool package loads
        validator_bounds encoder_bounds schedules steps
    end
  | None => pure None end.
Theorem check_affine_inner_pointer_package_sound live pool propose source
  (package : memory_affine_inner_pointer_package source) loads target :
  mayReturn (check_affine_inner_pointer_package live pool propose package loads) (Some target) ->
  PrivateRegion.projected_region_contract live (Ssequence (source_load_prefix loads) source) target.
Proof.
  unfold check_affine_inner_pointer_package; destruct (propose (affine_inner_pointer_request_of package)) as [proposal|].
  - destruct (affine_proposal_candidate proposal); intro RUN;
      [eapply check_affine_inner_pointer_mapped_package_sound|eapply check_affine_inner_pointer_tiled_package_sound|
       eapply check_affine_inner_pointer_scheduled_package_sound]; exact RUN.
  - intro RUN; apply mayReturn_pure in RUN; discriminate.
Qed.

Definition check_affine_inner_pointer_source live pool (profile : affine_inner_pointer_profiler)
  (propose : affine_inner_pointer_proposer) source :=
  match describe_observed_pointer_source source with
  | Some observed =>
    match profile (observed_source_loop observed) with
    | Some proposed_profile => match describe_affine_inner_pointer_at (observed_source_loop observed) proposed_profile with
      | Some package =>
        BIND candidate <- check_affine_inner_pointer_package live pool propose package (observed_source_loads observed) -;
        pure (option_map (fun target => Ssequence target (observed_source_suffix observed)) candidate)
      | None => pure None end
    | None => pure None end
  | None => pure None end.
Theorem check_affine_inner_pointer_source_sound live pool profile propose source target :
  mayReturn (check_affine_inner_pointer_source live pool profile propose source) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold check_affine_inner_pointer_source; destruct (describe_observed_pointer_source source) as [observed|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (profile (observed_source_loop observed)) as [proposed|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (describe_affine_inner_pointer_at (observed_source_loop observed) proposed) as [package|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN candidate ACCEPTED; apply mayReturn_pure in RUN;
    destruct candidate as [candidate|]; [injection RUN as <-|discriminate].
  eapply flattened_projected_region_contract; [exact (observed_source_flat observed)|].
  apply projected_region_quiet_suffix; [exact (observed_source_suffix_quiet observed)|].
  eapply check_affine_inner_pointer_package_sound; exact ACCEPTED.
Qed.

Print Assumptions check_affine_inner_pointer_mapped_package_sound.
Print Assumptions check_affine_inner_pointer_certified_package_sound.
Print Assumptions check_affine_inner_pointer_tiled_package_sound.
Print Assumptions check_affine_inner_pointer_scheduled_package_sound.
Print Assumptions check_affine_inner_pointer_package_sound.
Print Assumptions check_affine_inner_pointer_source_sound.
