From Stdlib Require Import List Bool ZArith Lia.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition ClightPureExpr ClightPrivateRule ClightPrivateRegion ClightPrivatePool
  ClightRectangularSelector ClightRectangularStore ClightRectangularGuard ClightFrontendLoopProtocol ClightSharedRegion.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryAffineReindex GuardMemoryTiledCompiler
  GuardMemoryNamedOperations GuardMemoryNamedRegistrySource GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceContext
  GuardMemoryAffineSourceLoop GuardMemoryParametricSyntax GuardMemoryParametricWidth GuardMemoryParametricGuard
  GuardMemoryParametricChecker GuardMemoryParametricCandidate GuardMemoryParametricLoops GuardMemoryParametricTiling GuardMemoryScheduleProducer GuardMemoryCommonLayout GuardMemoryLayoutCopyInstruction
  GuardMemoryParametricBody GuardMemoryParametricBodyCandidate GuardMemoryParametricRegion
  GuardMemoryParametricInstructionChecker GuardMemoryParametricInstructionTiling GuardMemoryParametricCompiler GuardMemoryRegistryBackend.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition compile_memory_parametric_region_candidate source (package : memory_parametric_region_package source) bounds live pool candidate :=
  let d := parametric_region_description package in let expression := parametric_region_expression package in
  compile_memory_registry_loop (memory_parametric_region_descriptors package)
    (memory_source_context (rectangle_row d) (rectangle_bound d) expression) bounds live pool candidate.
Definition memory_parametric_region_arrays source (package : memory_parametric_region_package source) :=
  map memory_descriptor_variable (memory_parametric_region_descriptors package).
Definition memory_parametric_region_bounder :=
  rectangle_shape -> ident -> ident -> memory_source_affine -> list MemoryNested.A.interval.
Definition memory_parametric_region_target source (package : memory_parametric_region_package source) bounds width_tree code :=
  let d := parametric_region_description package in let expression := parametric_region_expression package in
  shared_guarded_statement
    (decision_bind (memory_source_guard_tree (described_shape d)
      (memory_parametric_region_descriptors package) (rectangle_row d) (rectangle_bound d)
      (memory_source_context (rectangle_row d) (rectangle_bound d) expression)
      bounds width_tree)
      (Decision true) (Decision false))
    (memory_parametric_candidate code (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d) expression) source.
Theorem memory_parametric_region_target_sound source (package : memory_parametric_region_package source) bounds live pairs encoded candidate width_tree code :
  memory_source_loop_expression (rectangle_row (parametric_region_description package))
    (memory_source_context (rectangle_row (parametric_region_description package)) (rectangle_bound (parametric_region_description package))
      (parametric_region_expression package)) (parametric_region_expression package) = Some encoded ->
  compile_memory_parametric_region_candidate package bounds live pairs candidate = Some code ->
  compile_memory_source_width (rectangle_stride (described_shape (parametric_region_description package)))
    (rectangle_row (parametric_region_description package))
    (memory_source_context (rectangle_row (parametric_region_description package)) (rectangle_bound (parametric_region_description package))
      (parametric_region_expression package))
    bounds (parametric_region_expression package) = Some width_tree ->
  memory_parametric_instruction_candidate_certificate (described_shape (parametric_region_description package)) (memory_parametric_region_instructions package)
    (rectangle_row (parametric_region_description package))
    (memory_source_context (rectangle_row (parametric_region_description package)) (rectangle_bound (parametric_region_description package))
      (parametric_region_expression package))
    bounds (parametric_region_expression package) encoded candidate ->
  projected_region_contract live source (memory_parametric_region_target package bounds width_tree code).
Proof.
  destruct package as [d expression CERT]; cbn; intros ENCODE COMPILE LOWER CHECK.
  destruct CERT as [SOURCE MODEL VALID OUTER RN RC NC RK NK CK SC SK]; subst source.
  unfold memory_parametric_region_target,rectangle_described_source,
    memory_parametric_region_descriptors,memory_parametric_region_instructions,memory_parametric_region_model,
    compile_memory_parametric_region_candidate in *; cbn in *.
  change (projected_region_contract live
    (frontend_counted_loop (rectangle_row d) (rectangle_bound d) (rectangle_described_outer_body d))
    (generated_private_region (@memory_parametric_body_candidate_rule (described_shape d) VALID
      (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d) expression encoded ENCODE
      (rectangle_inner_body d) (rectangle_described_outer_body d) MODEL RN RC NC RK NK CK SC SK OUTER
      bounds
      live pairs candidate code COMPILE CHECK width_tree LOWER))).
  apply encoded_private_rule_sound.
Qed.
Definition check_memory_parametric_region_mapped live pool
  (describe : forall source, option (memory_parametric_region_package source)) (bounder : memory_parametric_region_bounder)
  (propose : list memory_instruction -> option (L.stmt*list memory_affine_reindex)) source : CoreAlarmed.Base.imp (option statement) :=
  match private_counter_pairs pool,describe source with
  | Some pairs,Some package =>
    let d := parametric_region_description package in let expression := parametric_region_expression package in
    let context := memory_source_context (rectangle_row d) (rectangle_bound d) expression in
    let bounds := bounder (described_shape d) (rectangle_row d) (rectangle_bound d) expression in
    match memory_source_loop_expression (rectangle_row d) context expression,
      propose (memory_parametric_region_instructions package),
      compile_memory_source_width (rectangle_stride (described_shape d)) (rectangle_row d) context bounds expression with
    | Some encoded,Some (candidate,steps),Some width_tree =>
      match compile_memory_parametric_region_candidate package bounds live pairs candidate with
      | Some code => BIND valid <- checked_parametric_instruction_candidate (described_shape d) (memory_parametric_region_instructions package) (memory_parametric_region_arrays package)
        (rectangle_row d) context bounds expression encoded candidate steps -;
        pure (if valid then Some (memory_parametric_region_target package bounds width_tree code) else None)
      | None => pure None end
    | _,_,_ => pure None end
  | _,_ => pure None end.
Theorem check_memory_parametric_region_mapped_sound live pool describe bounder propose source target :
  mayReturn (check_memory_parametric_region_mapped live pool describe bounder propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_parametric_region_mapped.
  destruct (private_counter_pairs pool) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (describe source) as [package|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (memory_source_loop_expression (rectangle_row (parametric_region_description package))
    (memory_source_context (rectangle_row (parametric_region_description package)) (rectangle_bound (parametric_region_description package))
      (parametric_region_expression package)) (parametric_region_expression package)) as [encoded|] eqn:ENCODE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (propose (memory_parametric_region_instructions package)) as [[candidate steps]|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_memory_source_width (rectangle_stride (described_shape (parametric_region_description package)))
    (rectangle_row (parametric_region_description package))
    (memory_source_context (rectangle_row (parametric_region_description package)) (rectangle_bound (parametric_region_description package))
      (parametric_region_expression package))
    (bounder (described_shape (parametric_region_description package)) (rectangle_row (parametric_region_description package))
      (rectangle_bound (parametric_region_description package)) (parametric_region_expression package)) (parametric_region_expression package)) as [width_tree|] eqn:LOWER;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_memory_parametric_region_candidate package (bounder (described_shape (parametric_region_description package)) (rectangle_row (parametric_region_description package))
      (rectangle_bound (parametric_region_description package)) (parametric_region_expression package)) live pairs candidate) as [code|] eqn:COMPILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN.
  destruct valid; [inversion RUN; subst target|discriminate].
  apply memory_parametric_region_target_sound with (pairs := pairs) (encoded := encoded) (candidate := candidate);
    [exact ENCODE|exact COMPILE|exact LOWER|].
  eapply checked_parametric_instruction_candidate_correct; exact VALID.
Qed.

Print Assumptions check_memory_parametric_region_mapped_sound.

Definition memory_parametric_default_bounds : memory_parametric_region_bounder := memory_parametric_bounds.
Definition memory_parametric_capped_bounds cap : memory_parametric_region_bounder :=
  fun base row bound expression =>
    match memory_parametric_bounds base row bound expression with
    | [] => []
    | _::rest => MemoryNested.A.Interval 1 (Z.min cap (rectangle_outer_limit base))::rest
    end.
Fixpoint check_memory_parametric_region_caps live pool describe propose caps source : CoreAlarmed.Base.imp (option statement) :=
  match caps with
  | [] => pure None
  | cap::rest =>
    BIND target <- check_memory_parametric_region_mapped live pool describe (memory_parametric_capped_bounds cap) propose source -;
    match target with
    | Some target => pure (Some target)
    | None => check_memory_parametric_region_caps live pool describe propose rest source
    end
  end.
Theorem check_memory_parametric_region_caps_sound live pool describe propose caps source target :
  mayReturn (check_memory_parametric_region_caps live pool describe propose caps source) (Some target) ->
  projected_region_contract live source target.
Proof.
  induction caps as [|cap rest IH]; cbn; intro RUN.
  - apply mayReturn_pure in RUN; discriminate.
  - bind_imp_destruct RUN selected CHECK; destruct selected as [chosen|].
    + apply mayReturn_pure in RUN; inversion RUN; subst chosen.
      eapply check_memory_parametric_region_mapped_sound; exact CHECK.
    + apply IH; exact RUN.
Qed.
Definition check_memory_parametric_region_conditioned live pool describe propose source :=
  BIND target <- check_memory_parametric_region_mapped live pool describe memory_parametric_default_bounds propose source -;
  match target with
  | Some target => pure (Some target)
  | None => check_memory_parametric_region_caps live pool describe propose [8;4;3;2;1] source
  end.
Theorem check_memory_parametric_region_conditioned_sound live pool describe propose source target :
  mayReturn (check_memory_parametric_region_conditioned live pool describe propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_parametric_region_conditioned; intro RUN.
  bind_imp_destruct RUN selected CHECK; destruct selected as [chosen|].
  - apply mayReturn_pure in RUN; inversion RUN; subst chosen.
    eapply check_memory_parametric_region_mapped_sound; exact CHECK.
  - eapply check_memory_parametric_region_caps_sound; exact RUN.
Qed.
Definition check_memory_parametric_region_scheduled live pool describe schedules steps source : CoreAlarmed.Base.imp (option statement) :=
  match describe source with
  | Some package =>
    let d := parametric_region_description package in let expression := parametric_region_expression package in
    let instructions := memory_parametric_region_instructions package in
    let context := memory_source_context (rectangle_row d) (rectangle_bound d) expression in
    let bounds := memory_parametric_bounds (described_shape d) (rectangle_row d) (rectangle_bound d) expression in
    let vars := map (fun array => (array,tt)) (context++memory_parametric_region_arrays package) in
    match memory_source_loop_expression (rectangle_row d) context expression with
    | Some encoded => BIND candidate <- memory_generate_scheduled_loop
        (memory_parametric_assumed_loop (described_shape d) (rectangle_row d) context bounds expression
          (memory_parametric_sequence encoded instructions),context,vars) schedules -;
      match candidate with
      | Some candidate => check_memory_parametric_region_conditioned live pool describe (fun _ => Some (candidate,steps)) source
      | None => pure None end
    | None => pure None end
  | None => pure None end.
Theorem check_memory_parametric_region_scheduled_sound live pool describe schedules steps source target :
  mayReturn (check_memory_parametric_region_scheduled live pool describe schedules steps source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_parametric_region_scheduled.
  destruct (describe source) as [package|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (memory_source_loop_expression (rectangle_row (parametric_region_description package))
    (memory_source_context (rectangle_row (parametric_region_description package)) (rectangle_bound (parametric_region_description package))
      (parametric_region_expression package)) (parametric_region_expression package)) as [encoded|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN generated GENERATED.
  destruct generated as [candidate|]; [|apply mayReturn_pure in RUN; discriminate].
  eapply check_memory_parametric_region_conditioned_sound; exact RUN.
Qed.
Print Assumptions check_memory_parametric_region_conditioned_sound.
Print Assumptions check_memory_parametric_region_scheduled_sound.

Definition memory_bounds_positive bounds :=
  match bounds with [] => false | first::_ => Z.ltb 0 (MemoryNested.A.lower first) end.
Lemma memory_bounds_positive_sound bounds :
  memory_bounds_positive bounds = true ->
  forall parameters, MemoryNested.A.env_within bounds parameters -> 0 < nth O parameters 0.
Proof.
  destruct bounds as [|first rest]; [discriminate|].
  cbn [memory_bounds_positive]; intro SAFE; apply Z.ltb_lt in SAFE.
  intros parameters WITHIN; specialize (WITHIN O first eq_refl).
  unfold MemoryNested.A.contains in WITHIN; lia.
Qed.
Definition check_memory_parametric_region_tiled live pool
  (describe : forall source, option (memory_parametric_region_package source)) (bounder : memory_parametric_region_bounder)
  rows columns source : CoreAlarmed.Base.imp (option statement) :=
  match Z_lt_dec 0 rows,Z_lt_dec 0 columns,private_counter_pairs pool,describe source with
  | left _,left _,Some pairs,Some package =>
    let d := parametric_region_description package in let expression := parametric_region_expression package in
    let context := memory_source_context (rectangle_row d) (rectangle_bound d) expression in
    let bounds := bounder (described_shape d) (rectangle_row d) (rectangle_bound d) expression in
    if memory_bounds_positive bounds then
    match memory_source_loop_expression (rectangle_row d) context expression,
      compile_memory_source_width (rectangle_stride (described_shape d)) (rectangle_row d) context bounds expression with
    | Some encoded,Some width_tree =>
      let candidate := memory_parametric_tiled_loop (memory_parametric_region_instructions package)
        encoded (rectangle_stride (described_shape d)) rows columns true in
      match compile_memory_parametric_region_candidate package bounds live pairs candidate with
      | Some code => BIND valid <- checked_parametric_instruction_tiling (described_shape d)
          (memory_parametric_region_instructions package) (memory_parametric_region_arrays package)
          (rectangle_row d) context bounds expression encoded rows columns -;
        pure (if valid then Some (memory_parametric_region_target package bounds width_tree code) else None)
      | None => pure None end
    | _,_ => pure None end
    else pure None
  | _,_,_,_ => pure None end.
Theorem check_memory_parametric_region_tiled_sound live pool describe bounder rows columns source target :
  mayReturn (check_memory_parametric_region_tiled live pool describe bounder rows columns source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_parametric_region_tiled.
  destruct (Z_lt_dec 0 rows) as [ROWS|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (Z_lt_dec 0 columns) as [COLS|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (private_counter_pairs pool) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (describe source) as [package|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (memory_bounds_positive (bounder (described_shape (parametric_region_description package))
    (rectangle_row (parametric_region_description package)) (rectangle_bound (parametric_region_description package))
    (parametric_region_expression package))) eqn:POSITIVE; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (memory_source_loop_expression (rectangle_row (parametric_region_description package))
    (memory_source_context (rectangle_row (parametric_region_description package)) (rectangle_bound (parametric_region_description package))
      (parametric_region_expression package)) (parametric_region_expression package)) as [encoded|] eqn:ENCODE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_memory_source_width (rectangle_stride (described_shape (parametric_region_description package)))
    (rectangle_row (parametric_region_description package))
    (memory_source_context (rectangle_row (parametric_region_description package)) (rectangle_bound (parametric_region_description package))
      (parametric_region_expression package))
    (bounder (described_shape (parametric_region_description package)) (rectangle_row (parametric_region_description package))
      (rectangle_bound (parametric_region_description package)) (parametric_region_expression package)) (parametric_region_expression package)) as [width_tree|] eqn:LOWER;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_memory_parametric_region_candidate package
    (bounder (described_shape (parametric_region_description package)) (rectangle_row (parametric_region_description package))
      (rectangle_bound (parametric_region_description package)) (parametric_region_expression package)) live pairs
    (memory_parametric_tiled_loop (memory_parametric_region_instructions package) encoded
      (rectangle_stride (described_shape (parametric_region_description package))) rows columns true)) as [code|] eqn:COMPILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN.
  destruct valid; [inversion RUN; subst target|discriminate].
  eapply memory_parametric_region_target_sound; [exact ENCODE|exact COMPILE|exact LOWER|].
  eapply checked_parametric_instruction_tiling_correct; [|exact ROWS|exact COLS| |exact VALID].
  - pose proof (parametric_region_layout (parametric_region_syntax package)) as LAYOUT.
    unfold rectangle_layout_valid in LAYOUT; tauto.
  - eapply memory_bounds_positive_sound; exact POSITIVE.
Qed.
Fixpoint check_memory_parametric_region_tiling_caps live pool describe rows columns caps source : CoreAlarmed.Base.imp (option statement) :=
  match caps with
  | [] => pure None
  | cap::rest =>
    BIND target <- check_memory_parametric_region_tiled live pool describe (memory_parametric_capped_bounds cap) rows columns source -;
    match target with
    | Some target => pure (Some target)
    | None => check_memory_parametric_region_tiling_caps live pool describe rows columns rest source
    end
  end.
Theorem check_memory_parametric_region_tiling_caps_sound live pool describe rows columns caps source target :
  mayReturn (check_memory_parametric_region_tiling_caps live pool describe rows columns caps source) (Some target) ->
  projected_region_contract live source target.
Proof.
  induction caps as [|cap rest IH]; cbn; intro RUN.
  - apply mayReturn_pure in RUN; discriminate.
  - bind_imp_destruct RUN selected CHECK; destruct selected as [chosen|].
    + apply mayReturn_pure in RUN; inversion RUN; subst chosen.
      eapply check_memory_parametric_region_tiled_sound; exact CHECK.
    + apply IH; exact RUN.
Qed.
Definition check_memory_parametric_region_conditioned_tiling live pool describe rows columns source :=
  BIND target <- check_memory_parametric_region_tiled live pool describe memory_parametric_default_bounds rows columns source -;
  match target with
  | Some target => pure (Some target)
  | None => check_memory_parametric_region_tiling_caps live pool describe rows columns [8;4;3;2;1] source
  end.
Theorem check_memory_parametric_region_conditioned_tiling_sound live pool describe rows columns source target :
  mayReturn (check_memory_parametric_region_conditioned_tiling live pool describe rows columns source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_parametric_region_conditioned_tiling; intro RUN.
  bind_imp_destruct RUN selected CHECK; destruct selected as [chosen|].
  - apply mayReturn_pure in RUN; inversion RUN; subst chosen.
    eapply check_memory_parametric_region_tiled_sound; exact CHECK.
  - eapply check_memory_parametric_region_tiling_caps_sound; exact RUN.
Qed.
Print Assumptions check_memory_parametric_region_conditioned_tiling_sound.
