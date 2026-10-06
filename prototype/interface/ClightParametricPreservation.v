From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Ctypes Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition ClightPureExpr ClightPrivateRule ClightPrivateRegion
  ClightPrivatePool ClightTempFootprint ClightRectangularStore ClightRectangularSelector ClightStraightLine ClightRegionProgress.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemoryAffineReindex GuardMemoryTiledCompiler
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceContext GuardMemoryAffineSourceLoop
  GuardMemoryParametricBody GuardMemoryParametricBodyCandidate GuardMemoryParametricRegion
  GuardMemoryParametricRegionInstances GuardMemoryParametricRegionCompiler GuardMemoryParametricWidthSearch
  GuardMemoryParametricChecker GuardMemoryParametricInstructionChecker GuardMemoryParametricInstructionTiling
  GuardMemoryParametricGuard GuardMemoryParametricWidth GuardMemoryParametricCandidate
  GuardMemoryParametricLoops GuardMemoryParametricTiling GuardMemoryScheduleProducer.
From GuardInterface Require Import ClightReadonlyPreservation ClightReadonlyRuleEmbedding
  ClightGuardRealization ClightSharedGuard ClightPolyhedralCompiler.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The proposer sees checked source metadata; it still returns untrusted data.
    This record contains neither a language execution nor a correctness proof. *)
Record parametric_preserving_request := ParametricPreservingRequest {
  parametric_request_instructions : list memory_instruction;
  parametric_request_coordinates : nat;
  parametric_request_context_arity : nat
}.
Inductive parametric_preserving_proposal :=
| ParametricMappedProposal (candidate : L.stmt) (steps : list memory_affine_reindex)
| ParametricTilingProposal (rows columns : Z)
| ParametricScheduleProposal (schedules : list (list (list Z * Z))) (steps : list memory_affine_reindex).
Definition parametric_preserving_proposer := parametric_preserving_request -> option parametric_preserving_proposal.

Definition parametric_preserving_tree source (package : memory_parametric_region_package source) bounds width_tree :=
  let d := parametric_region_description package in
  decision_bind (memory_source_guard_tree (described_shape d)
    (memory_parametric_region_descriptors package) (rectangle_row d) (rectangle_bound d)
    (memory_source_context (rectangle_row d) (rectangle_bound d) (parametric_region_expression package))
    bounds width_tree) (Decision true) (Decision false).
Definition parametric_preserving_branch source (package : memory_parametric_region_package source) code :=
  let d := parametric_region_description package in
  memory_parametric_candidate code (rectangle_row d) (rectangle_bound d)
    (rectangle_column d) (rectangle_inner_bound d) (parametric_region_expression package).

(** Reusable language dispatch: shared lowering reserves a private Boolean;
    direct lowering uses the same tree and candidate without that slot. *)
Definition choose_preserving_dispatch live source guard candidate (shared : bool) result : option statement :=
  if shared then
    if Bool.bool_dec (quiet_statement candidate) true then
      if in_dec peq result (statement_temps candidate ++ statement_temps source ++ live)
      then None else Some (shared_guard_statement guard result candidate source)
    else None
  else Some (tree_statement guard candidate source).
Theorem choose_preserving_dispatch_sound live source (rule : readonly_preserving_clight_rule live source) shared result target :
  choose_preserving_dispatch live source (preserving_guard rule) (preserving_candidate rule) shared result = Some target ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold choose_preserving_dispatch; destruct shared.
  - destruct (Bool.bool_dec (quiet_statement (preserving_candidate rule)) true) as [QUIET|]; [|discriminate].
    destruct (in_dec peq result (statement_temps (preserving_candidate rule) ++ statement_temps source ++ live))
      as [|FRESH]; [discriminate|].
    intro SAME; injection SAME as SAME; subst target.
    exact (@preserving_realized_region_contract live source rule
      (@shared_normal_realization live (preserving_guard rule) (preserving_candidate rule) source result
        (statement_temps (preserving_candidate rule)) (preserving_writes rule)
        (@quiet_source_write_bound (preserving_candidate rule) QUIET) (preserving_source_writes rule) FRESH)).
  - intro SAME; injection SAME as SAME; subst target.
    exact (@preserving_realized_region_contract live source rule
      (direct_normal_realization live (preserving_guard rule) (preserving_candidate rule) source)).
Qed.

Definition choose_parametric_preserving_target live source (package : memory_parametric_region_package source)
  bounds width_tree code shared result :=
  choose_preserving_dispatch live source (parametric_preserving_tree package bounds width_tree)
    (parametric_preserving_branch package code) shared result.
Theorem choose_parametric_preserving_target_sound source (package : memory_parametric_region_package source)
  bounds live pairs encoded candidate width_tree code shared result target :
  memory_source_loop_expression (rectangle_row (parametric_region_description package))
    (memory_source_context (rectangle_row (parametric_region_description package))
      (rectangle_bound (parametric_region_description package)) (parametric_region_expression package))
    (parametric_region_expression package) = Some encoded ->
  compile_memory_parametric_region_candidate package bounds live pairs candidate = Some code ->
  compile_memory_source_width (rectangle_stride (described_shape (parametric_region_description package)))
    (rectangle_row (parametric_region_description package))
    (memory_source_context (rectangle_row (parametric_region_description package))
      (rectangle_bound (parametric_region_description package)) (parametric_region_expression package))
    bounds (parametric_region_expression package) = Some width_tree ->
  memory_parametric_instruction_candidate_certificate (described_shape (parametric_region_description package))
    (memory_parametric_region_instructions package) (rectangle_row (parametric_region_description package))
    (memory_source_context (rectangle_row (parametric_region_description package))
      (rectangle_bound (parametric_region_description package)) (parametric_region_expression package))
    bounds (parametric_region_expression package) encoded candidate ->
  choose_parametric_preserving_target live package bounds width_tree code shared result = Some target ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  destruct package as [d expression CERT]; cbn; intros ENCODE COMPILE LOWER CHECK.
  destruct CERT as [SOURCE MODEL VALID OUTER RN RC NC RK NK CK SC SK]; subst source.
  unfold choose_parametric_preserving_target,parametric_preserving_tree,parametric_preserving_branch,
    memory_parametric_region_descriptors,memory_parametric_region_instructions,memory_parametric_region_model,
    compile_memory_parametric_region_candidate in *; cbn in *.
  exact (@choose_preserving_dispatch_sound live
    (rectangle_described_source d)
    (encoded_private_as_preserving (@memory_parametric_body_candidate_rule (described_shape d) VALID
      (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d) expression encoded ENCODE
      (rectangle_inner_body d) (rectangle_described_outer_body d) MODEL RN RC NC RK NK CK SC SK OUTER
      bounds live pairs candidate code COMPILE CHECK width_tree LOWER)) shared result target).
Qed.

Definition checked_parametric_preserving_candidate source (package : memory_parametric_region_package source)
  bounds encoded proposal : CoreAlarmed.Base.imp (option L.stmt) :=
  let d := parametric_region_description package in let expression := parametric_region_expression package in
  let instructions := memory_parametric_region_instructions package in
  let context := memory_source_context (rectangle_row d) (rectangle_bound d) expression in
  let arrays := memory_parametric_region_arrays package in
  match proposal with
  | ParametricMappedProposal candidate steps =>
    BIND valid <- checked_parametric_instruction_candidate (described_shape d) instructions arrays
      (rectangle_row d) context bounds expression encoded candidate steps -;
    pure (if valid then Some candidate else None)
  | ParametricTilingProposal rows columns =>
    match Z_lt_dec 0 rows, Z_lt_dec 0 columns with
    | left _,left _ => if memory_bounds_positive bounds then
      BIND valid <- checked_parametric_instruction_tiling (described_shape d) instructions arrays
        (rectangle_row d) context bounds expression encoded rows columns -;
      pure (if valid then Some (memory_parametric_tiled_loop instructions encoded
        (rectangle_stride (described_shape d)) rows columns true) else None)
      else pure None
    | _,_ => pure None end
  | ParametricScheduleProposal schedules steps =>
    BIND generated <- memory_generate_scheduled_loop
      (memory_parametric_assumed_loop (described_shape d) (rectangle_row d) context bounds expression
        (memory_parametric_sequence encoded instructions),context,map (fun array => (array,tt)) (context++arrays)) schedules -;
    match generated with
    | Some candidate =>
      BIND valid <- checked_parametric_instruction_candidate (described_shape d) instructions arrays
        (rectangle_row d) context bounds expression encoded candidate steps -;
      pure (if valid then Some candidate else None)
    | None => pure None end
  end.
Theorem checked_parametric_preserving_candidate_sound source (package : memory_parametric_region_package source)
  bounds encoded proposal candidate :
  mayReturn (checked_parametric_preserving_candidate package bounds encoded proposal) (Some candidate) ->
  memory_parametric_instruction_candidate_certificate (described_shape (parametric_region_description package))
    (memory_parametric_region_instructions package) (rectangle_row (parametric_region_description package))
    (memory_source_context (rectangle_row (parametric_region_description package))
      (rectangle_bound (parametric_region_description package)) (parametric_region_expression package))
    bounds (parametric_region_expression package) encoded candidate.
Proof.
  destruct proposal as [loop steps|rows columns|schedules steps]; cbn [checked_parametric_preserving_candidate].
  - intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN.
    destruct valid; [inversion RUN; subst candidate|discriminate].
    eapply checked_parametric_instruction_candidate_correct; exact VALID.
  - destruct (Z_lt_dec 0 rows) as [ROWS|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
    destruct (Z_lt_dec 0 columns) as [COLUMNS|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
    destruct (memory_bounds_positive bounds) eqn:POSITIVE; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
    intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN.
    destruct valid; [inversion RUN; subst candidate|discriminate].
    eapply checked_parametric_instruction_tiling_correct; [|exact ROWS|exact COLUMNS| |exact VALID].
    + pose proof (parametric_region_layout (parametric_region_syntax package)) as LAYOUT.
      unfold rectangle_layout_valid in LAYOUT; tauto.
    + eapply memory_bounds_positive_sound; exact POSITIVE.
  - intro RUN; bind_imp_destruct RUN generated GENERATED.
    destruct generated as [loop|]; [|apply mayReturn_pure in RUN; discriminate].
    bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN.
    destruct valid; [inversion RUN; subst candidate|discriminate].
    eapply checked_parametric_instruction_candidate_correct; exact VALID.
Qed.

Definition check_parametric_preserving_region shared live pool
  (describe : memory_parametric_describer) (bounder : memory_parametric_region_bounder)
  (propose : parametric_preserving_proposer) source : CoreAlarmed.Base.imp (option statement) :=
  match preserving_dispatch_pool shared pool, describe source with
  | Some (result,private),Some package =>
    match private_counter_pairs private with
    | Some pairs =>
      let d := parametric_region_description package in let expression := parametric_region_expression package in
      let context := memory_source_context (rectangle_row d) (rectangle_bound d) expression in
      let bounds := bounder (described_shape d) (rectangle_row d) (rectangle_bound d) expression in
      match memory_source_loop_expression (rectangle_row d) context expression,
        compile_memory_source_width (rectangle_stride (described_shape d)) (rectangle_row d) context bounds expression,
        propose (ParametricPreservingRequest (memory_parametric_region_instructions package) 2%nat (length context)) with
      | Some encoded,Some width_tree,Some proposal =>
        BIND candidate <- checked_parametric_preserving_candidate package bounds encoded proposal -;
        pure (match candidate with
          | Some loop => match compile_memory_parametric_region_candidate package bounds live pairs loop with
            | Some code => choose_parametric_preserving_target live package bounds width_tree code shared result
            | None => None end
          | None => None end)
      | _,_,_ => pure None end
    | None => pure None end
  | _,_ => pure None end.
Theorem check_parametric_preserving_region_sound shared live pool describe bounder propose source target :
  mayReturn (check_parametric_preserving_region shared live pool describe bounder propose source) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold check_parametric_preserving_region.
  destruct (preserving_dispatch_pool shared pool) as [[result private]|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (describe source) as [package|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (private_counter_pairs private) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (memory_source_loop_expression (rectangle_row (parametric_region_description package))
    (memory_source_context (rectangle_row (parametric_region_description package))
      (rectangle_bound (parametric_region_description package)) (parametric_region_expression package))
    (parametric_region_expression package)) as [encoded|] eqn:ENCODE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_memory_source_width (rectangle_stride (described_shape (parametric_region_description package)))
    (rectangle_row (parametric_region_description package))
    (memory_source_context (rectangle_row (parametric_region_description package))
      (rectangle_bound (parametric_region_description package)) (parametric_region_expression package))
    (bounder (described_shape (parametric_region_description package)) (rectangle_row (parametric_region_description package))
      (rectangle_bound (parametric_region_description package)) (parametric_region_expression package))
    (parametric_region_expression package)) as [width_tree|] eqn:LOWER;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (propose (ParametricPreservingRequest (memory_parametric_region_instructions package) 2%nat
    (length (memory_source_context (rectangle_row (parametric_region_description package))
      (rectangle_bound (parametric_region_description package)) (parametric_region_expression package))))) as [proposal|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN candidate CANDIDATE; apply mayReturn_pure in RUN.
  destruct candidate as [loop|]; [|discriminate].
  destruct (compile_memory_parametric_region_candidate package
    (bounder (described_shape (parametric_region_description package)) (rectangle_row (parametric_region_description package))
      (rectangle_bound (parametric_region_description package)) (parametric_region_expression package)) live pairs loop)
    as [code|] eqn:COMPILE; [|discriminate].
  eapply choose_parametric_preserving_target_sound; [exact ENCODE|exact COMPILE|exact LOWER| |exact RUN].
  eapply checked_parametric_preserving_candidate_sound; exact CANDIDATE.
Qed.

Fixpoint check_parametric_preserving_bounds shared live pool describe propose bounders source :=
  match bounders with
  | [] => pure None
  | bounder::rest =>
    BIND selected <- check_parametric_preserving_region shared live pool describe bounder propose source -;
    match selected with
    | Some target => pure (Some target)
    | None => check_parametric_preserving_bounds shared live pool describe propose rest source end
  end.
Theorem check_parametric_preserving_bounds_sound shared live pool describe propose bounders source target :
  mayReturn (check_parametric_preserving_bounds shared live pool describe propose bounders source) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  induction bounders as [|bounder rest IH]; cbn; intro RUN.
  - apply mayReturn_pure in RUN; discriminate.
  - bind_imp_destruct RUN selected CHECK; destruct selected as [chosen|].
    + apply mayReturn_pure in RUN; inversion RUN; subst chosen.
      eapply check_parametric_preserving_region_sound; exact CHECK.
    + apply IH; exact RUN.
Qed.
Definition check_parametric_preserving_conditioned shared live pool describe propose source :=
  check_parametric_preserving_bounds shared live pool describe propose
    (memory_parametric_default_bounds :: map memory_parametric_capped_bounds [8;4;3;2;1]) source.
Definition check_parametric_preserving_source shared live pool propose source :=
  check_memory_parametric_with_widths
    (fun describe source => check_parametric_preserving_conditioned shared live pool describe propose source)
    describe_memory_parametric_region [1] source.
Theorem check_parametric_preserving_source_sound shared live pool propose source target :
  mayReturn (check_parametric_preserving_source shared live pool propose source) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold check_parametric_preserving_source; intro RUN.
  eapply check_memory_parametric_with_widths_sound; [|exact RUN].
  intros describe original chosen CHECK; unfold check_parametric_preserving_conditioned in CHECK.
  eapply check_parametric_preserving_bounds_sound; exact CHECK.
Qed.

Print Assumptions choose_preserving_dispatch_sound.
Print Assumptions choose_parametric_preserving_target_sound.
Print Assumptions checked_parametric_preserving_candidate_sound.
Print Assumptions check_parametric_preserving_region_sound.
Print Assumptions check_parametric_preserving_source_sound.
