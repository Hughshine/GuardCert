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
  GuardMemoryParametricChecker GuardMemoryParametricCandidate GuardMemoryParametricLoops GuardMemoryParametricTiling GuardMemoryScheduleProducer.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_parametric_bounds base row bound expression :=
  MemoryNested.A.Interval 1 (rectangle_outer_limit base)::
    map (fun _ => MemoryNested.A.Interval (-rectangle_stride base) (rectangle_stride base))
      (memory_source_other_parameters row bound expression).
Definition memory_parametric_target source (package : memory_parametric_package source) width_tree code :=
  let d := parametric_description package in let expression := parametric_expression package in
  shared_guarded_statement
    (decision_bind (memory_source_guard_tree (described_shape d)
      (named_array_descriptors (described_shape d) (parametric_operations package)) (rectangle_row d) (rectangle_bound d)
      (memory_source_context (rectangle_row d) (rectangle_bound d) expression)
      (memory_parametric_bounds (described_shape d) (rectangle_row d) (rectangle_bound d) expression) width_tree)
      (Decision true) (Decision false))
    (memory_parametric_candidate code (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d) expression) source.
Theorem memory_parametric_target_sound source (package : memory_parametric_package source) live pairs encoded candidate width_tree code :
  memory_source_loop_expression (rectangle_row (parametric_description package))
    (memory_source_context (rectangle_row (parametric_description package)) (rectangle_bound (parametric_description package))
      (parametric_expression package)) (parametric_expression package) = Some encoded ->
  compile_named_parametric_array_candidate (described_shape (parametric_description package)) (parametric_operations package)
    (rectangle_row (parametric_description package)) (rectangle_bound (parametric_description package)) (parametric_expression package)
    (memory_parametric_bounds (described_shape (parametric_description package)) (rectangle_row (parametric_description package))
      (rectangle_bound (parametric_description package)) (parametric_expression package)) live pairs candidate = Some code ->
  compile_memory_source_width (rectangle_stride (described_shape (parametric_description package)))
    (rectangle_row (parametric_description package))
    (memory_source_context (rectangle_row (parametric_description package)) (rectangle_bound (parametric_description package))
      (parametric_expression package))
    (memory_parametric_bounds (described_shape (parametric_description package)) (rectangle_row (parametric_description package))
      (rectangle_bound (parametric_description package)) (parametric_expression package)) (parametric_expression package) = Some width_tree ->
  memory_parametric_candidate_certificate (described_shape (parametric_description package)) (parametric_operations package)
    (rectangle_row (parametric_description package))
    (memory_source_context (rectangle_row (parametric_description package)) (rectangle_bound (parametric_description package))
      (parametric_expression package))
    (memory_parametric_bounds (described_shape (parametric_description package)) (rectangle_row (parametric_description package))
      (rectangle_bound (parametric_description package)) (parametric_expression package)) (parametric_expression package) encoded candidate ->
  projected_region_contract live source (memory_parametric_target package width_tree code).
Proof.
  destruct package as [d expression operations CERT]; cbn; intros ENCODE COMPILE LOWER CHECK.
  destruct CERT as [SOURCE BODY OUTER RN RC NC RK NK CK SC SK VALID LAYOUTS NONEMPTY]; subst source.
  unfold memory_parametric_target,rectangle_described_source; cbn.
  change (projected_region_contract live
    (frontend_counted_loop (rectangle_row d) (rectangle_bound d) (rectangle_described_outer_body d))
    (generated_private_region (@memory_parametric_array_candidate_rule (described_shape d) VALID operations LAYOUTS
      (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d) expression encoded ENCODE
      (rectangle_inner_body d) (rectangle_described_outer_body d) RN RC NC RK NK CK SC SK BODY OUTER
      (memory_parametric_bounds (described_shape d) (rectangle_row d) (rectangle_bound d) expression)
      live pairs candidate code COMPILE CHECK width_tree LOWER))).
  apply encoded_private_rule_sound.
Qed.
Definition check_memory_parametric_mapped_region live pool
  (propose : list memory_instruction -> option (L.stmt*list memory_affine_reindex)) source : CoreAlarmed.Base.imp (option statement) :=
  match private_counter_pairs pool,describe_memory_parametric source with
  | Some pairs,Some package =>
    let d := parametric_description package in let expression := parametric_expression package in
    let context := memory_source_context (rectangle_row d) (rectangle_bound d) expression in
    let bounds := memory_parametric_bounds (described_shape d) (rectangle_row d) (rectangle_bound d) expression in
    match memory_source_loop_expression (rectangle_row d) context expression,
      propose (map named_operation_instruction (parametric_operations package)),
      compile_memory_source_width (rectangle_stride (described_shape d)) (rectangle_row d) context bounds expression with
    | Some encoded,Some (candidate,steps),Some width_tree =>
      match compile_named_parametric_array_candidate (described_shape d) (parametric_operations package)
        (rectangle_row d) (rectangle_bound d) expression bounds live pairs candidate with
      | Some code => BIND valid <- checked_named_parametric_candidate (described_shape d) (parametric_operations package)
        (rectangle_row d) context bounds expression encoded candidate steps -;
        pure (if valid then Some (memory_parametric_target package width_tree code) else None)
      | None => pure None end
    | _,_,_ => pure None end
  | _,_ => pure None end.
Theorem check_memory_parametric_mapped_region_sound live pool propose source target :
  mayReturn (check_memory_parametric_mapped_region live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_parametric_mapped_region.
  destruct (private_counter_pairs pool) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (describe_memory_parametric source) as [package|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (memory_source_loop_expression (rectangle_row (parametric_description package))
    (memory_source_context (rectangle_row (parametric_description package)) (rectangle_bound (parametric_description package))
      (parametric_expression package)) (parametric_expression package)) as [encoded|] eqn:ENCODE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (propose (map named_operation_instruction (parametric_operations package))) as [[candidate steps]|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_memory_source_width (rectangle_stride (described_shape (parametric_description package)))
    (rectangle_row (parametric_description package))
    (memory_source_context (rectangle_row (parametric_description package)) (rectangle_bound (parametric_description package))
      (parametric_expression package))
    (memory_parametric_bounds (described_shape (parametric_description package)) (rectangle_row (parametric_description package))
      (rectangle_bound (parametric_description package)) (parametric_expression package)) (parametric_expression package)) as [width_tree|] eqn:LOWER;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_named_parametric_array_candidate (described_shape (parametric_description package)) (parametric_operations package)
    (rectangle_row (parametric_description package)) (rectangle_bound (parametric_description package)) (parametric_expression package)
    (memory_parametric_bounds (described_shape (parametric_description package)) (rectangle_row (parametric_description package))
      (rectangle_bound (parametric_description package)) (parametric_expression package)) live pairs candidate) as [code|] eqn:COMPILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN.
  destruct valid; [inversion RUN; subst target|discriminate].
  apply memory_parametric_target_sound with (pairs := pairs) (encoded := encoded) (candidate := candidate);
    [exact ENCODE|exact COMPILE|exact LOWER|].
  eapply checked_named_parametric_candidate_correct; exact VALID.
Qed.

Definition check_memory_parametric_scheduled_region live pool schedules steps source : CoreAlarmed.Base.imp (option statement) :=
  match describe_memory_parametric source with
  | Some package =>
    let d := parametric_description package in let expression := parametric_expression package in
    let operations := parametric_operations package in
    let context := memory_source_context (rectangle_row d) (rectangle_bound d) expression in
    let bounds := memory_parametric_bounds (described_shape d) (rectangle_row d) (rectangle_bound d) expression in
    let vars := map (fun array => (array,tt)) (context++flat_map named_operation_arrays operations) in
    match memory_source_loop_expression (rectangle_row d) context expression with
    | Some encoded => BIND candidate <- memory_generate_scheduled_loop
        (memory_parametric_assumed_loop (described_shape d) (rectangle_row d) context bounds expression
          (memory_parametric_sequence encoded (map named_operation_instruction operations)),context,vars) schedules -;
      match candidate with
      | Some candidate => check_memory_parametric_mapped_region live pool (fun _ => Some (candidate,steps)) source
      | None => pure None end
    | None => pure None end
  | None => pure None end.
Theorem check_memory_parametric_scheduled_region_sound live pool schedules steps source target :
  mayReturn (check_memory_parametric_scheduled_region live pool schedules steps source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_parametric_scheduled_region.
  destruct (describe_memory_parametric source) as [package|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (memory_source_loop_expression (rectangle_row (parametric_description package))
    (memory_source_context (rectangle_row (parametric_description package)) (rectangle_bound (parametric_description package))
      (parametric_expression package)) (parametric_expression package)) as [encoded|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN generated GENERATED.
  destruct generated as [candidate|]; [|apply mayReturn_pure in RUN; discriminate].
  eapply check_memory_parametric_mapped_region_sound; exact RUN.
Qed.
Print Assumptions check_memory_parametric_mapped_region_sound.
Print Assumptions check_memory_parametric_scheduled_region_sound.

Definition check_memory_parametric_tiled_region live pool rows columns source : CoreAlarmed.Base.imp (option statement) :=
  match Z_lt_dec 0 rows,Z_lt_dec 0 columns,private_counter_pairs pool,describe_memory_parametric source with
  | left _,left _,Some pairs,Some package =>
    let d := parametric_description package in let expression := parametric_expression package in
    let context := memory_source_context (rectangle_row d) (rectangle_bound d) expression in
    let bounds := memory_parametric_bounds (described_shape d) (rectangle_row d) (rectangle_bound d) expression in
    match memory_source_loop_expression (rectangle_row d) context expression,
      compile_memory_source_width (rectangle_stride (described_shape d)) (rectangle_row d) context bounds expression with
    | Some encoded,Some width_tree =>
      let candidate := memory_parametric_tiled_loop (map named_operation_instruction (parametric_operations package))
        encoded (rectangle_stride (described_shape d)) rows columns true in
      match compile_named_parametric_array_candidate (described_shape d) (parametric_operations package)
        (rectangle_row d) (rectangle_bound d) expression bounds live pairs candidate with
      | Some code => BIND valid <- checked_named_parametric_tiling (described_shape d) (parametric_operations package)
        (rectangle_row d) context bounds expression encoded rows columns -;
        pure (if valid then Some (memory_parametric_target package width_tree code) else None)
      | None => pure None end
    | _,_ => pure None end
  | _,_,_,_ => pure None end.
Theorem check_memory_parametric_tiled_region_sound live pool rows columns source target :
  mayReturn (check_memory_parametric_tiled_region live pool rows columns source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_parametric_tiled_region.
  destruct (Z_lt_dec 0 rows) as [ROWS|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (Z_lt_dec 0 columns) as [COLS|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (private_counter_pairs pool) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (describe_memory_parametric source) as [package|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (memory_source_loop_expression (rectangle_row (parametric_description package))
    (memory_source_context (rectangle_row (parametric_description package)) (rectangle_bound (parametric_description package))
      (parametric_expression package)) (parametric_expression package)) as [encoded|] eqn:ENCODE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_memory_source_width (rectangle_stride (described_shape (parametric_description package)))
    (rectangle_row (parametric_description package))
    (memory_source_context (rectangle_row (parametric_description package)) (rectangle_bound (parametric_description package))
      (parametric_expression package))
    (memory_parametric_bounds (described_shape (parametric_description package)) (rectangle_row (parametric_description package))
      (rectangle_bound (parametric_description package)) (parametric_expression package)) (parametric_expression package)) as [width_tree|] eqn:LOWER;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_named_parametric_array_candidate (described_shape (parametric_description package)) (parametric_operations package)
    (rectangle_row (parametric_description package)) (rectangle_bound (parametric_description package)) (parametric_expression package)
    (memory_parametric_bounds (described_shape (parametric_description package)) (rectangle_row (parametric_description package))
      (rectangle_bound (parametric_description package)) (parametric_expression package)) live pairs
    (memory_parametric_tiled_loop (map named_operation_instruction (parametric_operations package)) encoded
      (rectangle_stride (described_shape (parametric_description package))) rows columns true)) as [code|] eqn:COMPILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN.
  destruct valid; [inversion RUN; subst target|discriminate].
  eapply memory_parametric_target_sound; [exact ENCODE|exact COMPILE|exact LOWER|].
  eapply checked_named_parametric_tiling_correct; [|exact ROWS|exact COLS| |exact VALID].
  - pose proof (parametric_layout (parametric_syntax package)) as LAYOUT.
    unfold rectangle_layout_valid in LAYOUT; tauto.
  - intros parameters WITHIN.
    specialize (WITHIN O (MemoryNested.A.Interval 1 (rectangle_outer_limit (described_shape (parametric_description package)))) eq_refl).
    unfold MemoryNested.A.contains in WITHIN; cbn [MemoryNested.A.lower MemoryNested.A.upper] in WITHIN; lia.
Qed.
Print Assumptions check_memory_parametric_tiled_region_sound.
