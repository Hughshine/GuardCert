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
  GuardMemoryLayoutCopyRegistry GuardMemoryLayoutCopyCandidate GuardMemoryLayoutCopySyntax
  GuardMemoryParametricInstructionChecker GuardMemoryParametricInstructionTiling GuardMemoryParametricCompiler GuardMemoryRegistryBackend.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_layout_copy_package_instructions source (package : memory_layout_copy_package source) :=
  [memory_layout_copy_instruction (layout_copy_write_shape package) (layout_copy_read_shape package)
    (layout_copy_write_array package) (layout_copy_read_array package)].
Definition memory_layout_copy_package_descriptors source (package : memory_layout_copy_package source) :=
  memory_layout_copy_descriptors (layout_copy_write_shape package) (layout_copy_read_shape package)
    (layout_copy_write_array package) (layout_copy_read_array package).
Definition compile_memory_layout_copy_candidate ws rs wa ra row bound expression bounds live pool candidate :=
  compile_memory_registry_loop (memory_layout_copy_descriptors ws rs wa ra)
    (memory_source_context row bound expression) bounds live pool candidate.
Definition memory_layout_copy_target source (package : memory_layout_copy_package source) width_tree code :=
  let d := layout_copy_description package in let expression := layout_copy_expression package in
  shared_guarded_statement
    (decision_bind (memory_source_guard_tree (described_shape d)
      (memory_layout_copy_package_descriptors package) (rectangle_row d) (rectangle_bound d)
      (memory_source_context (rectangle_row d) (rectangle_bound d) expression)
      (memory_parametric_bounds (described_shape d) (rectangle_row d) (rectangle_bound d) expression) width_tree)
      (Decision true) (Decision false))
    (memory_parametric_candidate code (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d) expression) source.
Theorem memory_layout_copy_target_sound source (package : memory_layout_copy_package source) live pairs encoded candidate width_tree code :
  memory_source_loop_expression (rectangle_row (layout_copy_description package))
    (memory_source_context (rectangle_row (layout_copy_description package)) (rectangle_bound (layout_copy_description package))
      (layout_copy_expression package)) (layout_copy_expression package) = Some encoded ->
  compile_memory_layout_copy_candidate (layout_copy_write_shape package) (layout_copy_read_shape package) (layout_copy_write_array package) (layout_copy_read_array package)
    (rectangle_row (layout_copy_description package)) (rectangle_bound (layout_copy_description package)) (layout_copy_expression package)
    (memory_parametric_bounds (described_shape (layout_copy_description package)) (rectangle_row (layout_copy_description package))
      (rectangle_bound (layout_copy_description package)) (layout_copy_expression package)) live pairs candidate = Some code ->
  compile_memory_source_width (rectangle_stride (described_shape (layout_copy_description package)))
    (rectangle_row (layout_copy_description package))
    (memory_source_context (rectangle_row (layout_copy_description package)) (rectangle_bound (layout_copy_description package))
      (layout_copy_expression package))
    (memory_parametric_bounds (described_shape (layout_copy_description package)) (rectangle_row (layout_copy_description package))
      (rectangle_bound (layout_copy_description package)) (layout_copy_expression package)) (layout_copy_expression package) = Some width_tree ->
  memory_parametric_instruction_candidate_certificate (described_shape (layout_copy_description package)) (memory_layout_copy_package_instructions package)
    (rectangle_row (layout_copy_description package))
    (memory_source_context (rectangle_row (layout_copy_description package)) (rectangle_bound (layout_copy_description package))
      (layout_copy_expression package))
    (memory_parametric_bounds (described_shape (layout_copy_description package)) (rectangle_row (layout_copy_description package))
      (rectangle_bound (layout_copy_description package)) (layout_copy_expression package)) (layout_copy_expression package) encoded candidate ->
  projected_region_contract live source (memory_layout_copy_target package width_tree code).
Proof.
  destruct package as [d expression ws rs wa ra CERT]; cbn; intros ENCODE COMPILE LOWER CHECK.
  destruct CERT as [SOURCE BODY OUTER RN RC NC RK NK CK SC SK COMMON WVALID RVALID DISTINCT]; subst source.
  unfold memory_layout_copy_target,rectangle_described_source,
    memory_layout_copy_package_descriptors,memory_layout_copy_package_instructions,compile_memory_layout_copy_candidate in *; cbn in *.
  rewrite COMMON in COMPILE,LOWER,CHECK |- *.
  change (projected_region_contract live
    (frontend_counted_loop (rectangle_row d) (rectangle_bound d) (rectangle_described_outer_body d))
    (generated_private_region (@memory_layout_copy_candidate_rule ws rs WVALID RVALID wa ra DISTINCT
      (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d) expression encoded ENCODE
      (rectangle_inner_body d) (rectangle_described_outer_body d) RN RC NC RK NK CK SC SK BODY OUTER
      (memory_parametric_bounds (memory_common_layout ws rs) (rectangle_row d) (rectangle_bound d) expression)
      live pairs candidate code COMPILE CHECK width_tree LOWER))).
  apply encoded_private_rule_sound.
Qed.
Definition check_memory_layout_copy_mapped_region live pool
  (propose : list memory_instruction -> option (L.stmt*list memory_affine_reindex)) source : CoreAlarmed.Base.imp (option statement) :=
  match private_counter_pairs pool,describe_memory_layout_copy source with
  | Some pairs,Some package =>
    let d := layout_copy_description package in let expression := layout_copy_expression package in
    let context := memory_source_context (rectangle_row d) (rectangle_bound d) expression in
    let bounds := memory_parametric_bounds (described_shape d) (rectangle_row d) (rectangle_bound d) expression in
    match memory_source_loop_expression (rectangle_row d) context expression,
      propose (memory_layout_copy_package_instructions package),
      compile_memory_source_width (rectangle_stride (described_shape d)) (rectangle_row d) context bounds expression with
    | Some encoded,Some (candidate,steps),Some width_tree =>
      match compile_memory_layout_copy_candidate (layout_copy_write_shape package) (layout_copy_read_shape package) (layout_copy_write_array package) (layout_copy_read_array package)
        (rectangle_row d) (rectangle_bound d) expression bounds live pairs candidate with
      | Some code => BIND valid <- checked_parametric_instruction_candidate (described_shape d) (memory_layout_copy_package_instructions package) [layout_copy_write_array package;layout_copy_read_array package]
        (rectangle_row d) context bounds expression encoded candidate steps -;
        pure (if valid then Some (memory_layout_copy_target package width_tree code) else None)
      | None => pure None end
    | _,_,_ => pure None end
  | _,_ => pure None end.
Theorem check_memory_layout_copy_mapped_region_sound live pool propose source target :
  mayReturn (check_memory_layout_copy_mapped_region live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_layout_copy_mapped_region.
  destruct (private_counter_pairs pool) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (describe_memory_layout_copy source) as [package|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (memory_source_loop_expression (rectangle_row (layout_copy_description package))
    (memory_source_context (rectangle_row (layout_copy_description package)) (rectangle_bound (layout_copy_description package))
      (layout_copy_expression package)) (layout_copy_expression package)) as [encoded|] eqn:ENCODE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (propose (memory_layout_copy_package_instructions package)) as [[candidate steps]|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_memory_source_width (rectangle_stride (described_shape (layout_copy_description package)))
    (rectangle_row (layout_copy_description package))
    (memory_source_context (rectangle_row (layout_copy_description package)) (rectangle_bound (layout_copy_description package))
      (layout_copy_expression package))
    (memory_parametric_bounds (described_shape (layout_copy_description package)) (rectangle_row (layout_copy_description package))
      (rectangle_bound (layout_copy_description package)) (layout_copy_expression package)) (layout_copy_expression package)) as [width_tree|] eqn:LOWER;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_memory_layout_copy_candidate (layout_copy_write_shape package) (layout_copy_read_shape package) (layout_copy_write_array package) (layout_copy_read_array package)
    (rectangle_row (layout_copy_description package)) (rectangle_bound (layout_copy_description package)) (layout_copy_expression package)
    (memory_parametric_bounds (described_shape (layout_copy_description package)) (rectangle_row (layout_copy_description package))
      (rectangle_bound (layout_copy_description package)) (layout_copy_expression package)) live pairs candidate) as [code|] eqn:COMPILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN.
  destruct valid; [inversion RUN; subst target|discriminate].
  apply memory_layout_copy_target_sound with (pairs := pairs) (encoded := encoded) (candidate := candidate);
    [exact ENCODE|exact COMPILE|exact LOWER|].
  eapply checked_parametric_instruction_candidate_correct; exact VALID.
Qed.

Definition check_memory_layout_copy_scheduled_region live pool schedules steps source : CoreAlarmed.Base.imp (option statement) :=
  match describe_memory_layout_copy source with
  | Some package =>
    let d := layout_copy_description package in let expression := layout_copy_expression package in
    let instructions := memory_layout_copy_package_instructions package in
    let context := memory_source_context (rectangle_row d) (rectangle_bound d) expression in
    let bounds := memory_parametric_bounds (described_shape d) (rectangle_row d) (rectangle_bound d) expression in
    let vars := map (fun array => (array,tt)) (context++[layout_copy_write_array package;layout_copy_read_array package]) in
    match memory_source_loop_expression (rectangle_row d) context expression with
    | Some encoded => BIND candidate <- memory_generate_scheduled_loop
        (memory_parametric_assumed_loop (described_shape d) (rectangle_row d) context bounds expression
          (memory_parametric_sequence encoded instructions),context,vars) schedules -;
      match candidate with
      | Some candidate => check_memory_layout_copy_mapped_region live pool (fun _ => Some (candidate,steps)) source
      | None => pure None end
    | None => pure None end
  | None => pure None end.
Theorem check_memory_layout_copy_scheduled_region_sound live pool schedules steps source target :
  mayReturn (check_memory_layout_copy_scheduled_region live pool schedules steps source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_layout_copy_scheduled_region.
  destruct (describe_memory_layout_copy source) as [package|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (memory_source_loop_expression (rectangle_row (layout_copy_description package))
    (memory_source_context (rectangle_row (layout_copy_description package)) (rectangle_bound (layout_copy_description package))
      (layout_copy_expression package)) (layout_copy_expression package)) as [encoded|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN generated GENERATED.
  destruct generated as [candidate|]; [|apply mayReturn_pure in RUN; discriminate].
  eapply check_memory_layout_copy_mapped_region_sound; exact RUN.
Qed.
Print Assumptions check_memory_layout_copy_mapped_region_sound.
Print Assumptions check_memory_layout_copy_scheduled_region_sound.

Definition check_memory_layout_copy_tiled_region live pool rows columns source : CoreAlarmed.Base.imp (option statement) :=
  match Z_lt_dec 0 rows,Z_lt_dec 0 columns,private_counter_pairs pool,describe_memory_layout_copy source with
  | left _,left _,Some pairs,Some package =>
    let d := layout_copy_description package in let expression := layout_copy_expression package in
    let context := memory_source_context (rectangle_row d) (rectangle_bound d) expression in
    let bounds := memory_parametric_bounds (described_shape d) (rectangle_row d) (rectangle_bound d) expression in
    match memory_source_loop_expression (rectangle_row d) context expression,
      compile_memory_source_width (rectangle_stride (described_shape d)) (rectangle_row d) context bounds expression with
    | Some encoded,Some width_tree =>
      let candidate := memory_parametric_tiled_loop (memory_layout_copy_package_instructions package)
        encoded (rectangle_stride (described_shape d)) rows columns true in
      match compile_memory_layout_copy_candidate (layout_copy_write_shape package) (layout_copy_read_shape package) (layout_copy_write_array package) (layout_copy_read_array package)
        (rectangle_row d) (rectangle_bound d) expression bounds live pairs candidate with
      | Some code => BIND valid <- checked_parametric_instruction_tiling (described_shape d) (memory_layout_copy_package_instructions package) [layout_copy_write_array package;layout_copy_read_array package]
        (rectangle_row d) context bounds expression encoded rows columns -;
        pure (if valid then Some (memory_layout_copy_target package width_tree code) else None)
      | None => pure None end
    | _,_ => pure None end
  | _,_,_,_ => pure None end.
Theorem check_memory_layout_copy_tiled_region_sound live pool rows columns source target :
  mayReturn (check_memory_layout_copy_tiled_region live pool rows columns source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_layout_copy_tiled_region.
  destruct (Z_lt_dec 0 rows) as [ROWS|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (Z_lt_dec 0 columns) as [COLS|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (private_counter_pairs pool) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (describe_memory_layout_copy source) as [package|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (memory_source_loop_expression (rectangle_row (layout_copy_description package))
    (memory_source_context (rectangle_row (layout_copy_description package)) (rectangle_bound (layout_copy_description package))
      (layout_copy_expression package)) (layout_copy_expression package)) as [encoded|] eqn:ENCODE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_memory_source_width (rectangle_stride (described_shape (layout_copy_description package)))
    (rectangle_row (layout_copy_description package))
    (memory_source_context (rectangle_row (layout_copy_description package)) (rectangle_bound (layout_copy_description package))
      (layout_copy_expression package))
    (memory_parametric_bounds (described_shape (layout_copy_description package)) (rectangle_row (layout_copy_description package))
      (rectangle_bound (layout_copy_description package)) (layout_copy_expression package)) (layout_copy_expression package)) as [width_tree|] eqn:LOWER;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_memory_layout_copy_candidate (layout_copy_write_shape package) (layout_copy_read_shape package) (layout_copy_write_array package) (layout_copy_read_array package)
    (rectangle_row (layout_copy_description package)) (rectangle_bound (layout_copy_description package)) (layout_copy_expression package)
    (memory_parametric_bounds (described_shape (layout_copy_description package)) (rectangle_row (layout_copy_description package))
      (rectangle_bound (layout_copy_description package)) (layout_copy_expression package)) live pairs
    (memory_parametric_tiled_loop (memory_layout_copy_package_instructions package) encoded
      (rectangle_stride (described_shape (layout_copy_description package))) rows columns true)) as [code|] eqn:COMPILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN.
  destruct valid; [inversion RUN; subst target|discriminate].
  eapply memory_layout_copy_target_sound; [exact ENCODE|exact COMPILE|exact LOWER|].
  eapply checked_parametric_instruction_tiling_correct; [|exact ROWS|exact COLS| |exact VALID].
  - pose proof (memory_common_layout_valid (layout_copy_write_layout (layout_copy_syntax package))
      (layout_copy_read_layout (layout_copy_syntax package))) as LAYOUT.
    rewrite <- (layout_copy_common (layout_copy_syntax package)) in LAYOUT.
    unfold rectangle_layout_valid in LAYOUT; tauto.
  - intros parameters WITHIN.
    specialize (WITHIN O (MemoryNested.A.Interval 1 (rectangle_outer_limit (described_shape (layout_copy_description package)))) eq_refl).
    unfold MemoryNested.A.contains in WITHIN; cbn [MemoryNested.A.lower MemoryNested.A.upper] in WITHIN; lia.
Qed.
Print Assumptions check_memory_layout_copy_tiled_region_sound.
