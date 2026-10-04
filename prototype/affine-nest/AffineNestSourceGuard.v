From Stdlib Require Import List.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame ClightRedundantSet.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestFirstDomain AffineNestFirstLeaf
  AffineNestLeafModel AffineNestGuardParameterCheck AffineNestGuardDomain AffineNestProbeRenaming
  AffineNestProbe AffineNestProbeStage AffineNestMathDomain AffineNestProfile AffineNestNumericGuard
  AffineNestDomainGuard AffineNestAcceptedDomain.
Import ListNotations.
Set Implicit Arguments.

Theorem affine_source_domain_guard_execution iterator bound expression body child bounds window_lower window_upper
  layout scalars pointers operations
  (certificate:affine_leaf_certificate(affine_nest_leaf child) bounds window_lower window_upper layout scalars pointers operations)
  parameter_ranges parameters floor cap remaining live registers rename result fe ge locals temps memory source_after source_final :
  affine_nest_shapes(AffineSourceAxis iterator bound expression body child) ->
  NoDup(affine_nest_controls(AffineSourceAxis iterator bound expression body child)) ->
  affine_nest_bound_dependencies [] parameters(AffineSourceAxis iterator bound expression body child) ->
  check_affine_guard_parameters(AffineSourceAxis iterator bound expression body child) layout scalars operations parameters=true ->
  check_affine_math_profile(AffineSourceAxis iterator bound expression body child) [] parameters [] parameter_ranges
    ((floor,cap)::remaining) bounds layout=true -> affine_parameter_intervals_check parameter_ranges=true ->
  affine_probe_stage_coverage registers(AffineSourceAxis iterator bound expression body child) [] parameters ->
  affine_rename_injective registers rename -> rename iterator<>rename bound ->
  ~In result(parameters++[iterator;bound]++live) ->
  (forall identifier, In identifier(affine_nest_controls(AffineSourceAxis iterator bound expression body child)) ->
    ~In(rename identifier)(parameters++[iterator;bound]++live)) ->
  (forall identifier, In identifier parameters -> identifier<>iterator -> identifier<>bound -> rename identifier=identifier) ->
  exec_stmt fe ge locals temps memory(affine_nest_source(AffineSourceAxis iterator bound expression body child))
    E0 source_after source_final Out_normal ->
  exists after,
    exec_stmt fe ge locals temps memory
      (affine_domain_guard_code iterator bound expression body child parameter_ranges parameters floor cap rename result)
      E0 after memory Out_normal /\
    temp_agree(parameters++[iterator;bound]++live) temps after /\
    after!result=Some(Vint(if affine_domain_guard_flag(AffineSourceAxis iterator bound expression body child)
      parameter_ranges parameters iterator floor cap(Entry ge locals temps memory) then Int.one else Int.zero)) /\
    (affine_domain_guard_flag(AffineSourceAxis iterator bound expression body child)
      parameter_ranges parameters iterator floor cap(Entry ge locals temps memory)=true ->
      affine_math_domain bounds layout(AffineSourceAxis iterator bound expression body child)
        (affine_word_valuation temps)(affine_word_valuation temps iterator)).
Proof.
  intros SHAPES FRESH DEPENDENCIES REGISTER_CHECK PROFILE PARAMETER_CHECK COVERAGE UNIQUE DISTINCT PRIVATE_RESULT PRIVATE PARAMETERS SOURCE.
  pose proof(@affine_source_first_header_domain(AffineSourceAxis iterator bound expression body child)
    fe ge locals temps memory source_after source_final SHAPES FRESH (affine_leaf_normal certificate)
    (affine_leaf_quiet certificate) (affine_leaf_writes certificate) SOURCE) as DOMAIN.
  assert (PARAMETER_DOMAINS:affine_first_path_flag(AffineSourceAxis iterator bound expression body child) temps=true ->
    Forall(fun identifier=>register_domain identifier(Entry ge locals temps memory)) parameters).
  { intro ACTIVE; exact(@affine_source_guard_parameter_domains(AffineSourceAxis iterator bound expression body child)
      bounds window_lower window_upper layout scalars pointers operations certificate parameters
      fe ge locals temps memory source_after source_final REGISTER_CHECK SHAPES FRESH
      (proj1(@affine_first_path_flag_exact(AffineSourceAxis iterator bound expression body child) temps) ACTIVE) SOURCE). }
  destruct(@affine_domain_guard_execution iterator bound expression body child parameter_ranges parameters floor cap live registers rename result
    fe ge locals temps memory DEPENDENCIES COVERAGE UNIQUE DISTINCT PRIVATE_RESULT PRIVATE PARAMETERS DOMAIN PARAMETER_DOMAINS)
    as [after [RUN [FRAME RESULT]]].
  exists after; split; [exact RUN|split; [exact FRAME|split; [exact RESULT|]]].
  intro ACCEPT; exact(@affine_domain_guard_accepted iterator bound expression body child parameter_ranges parameters floor cap remaining
    bounds layout (Entry ge locals temps memory) PROFILE PARAMETER_CHECK FRESH
    ltac:(intros identifier MEMBER; exact(proj2(@check_affine_guard_parameters_sound
      (AffineSourceAxis iterator bound expression body child) layout scalars operations parameters REGISTER_CHECK identifier MEMBER))) ACCEPT).
Qed.
Print Assumptions affine_source_domain_guard_execution.
