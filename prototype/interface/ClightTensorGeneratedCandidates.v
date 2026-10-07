From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.src Require Import TilingWitness.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryScalarChecker GuardMemoryScalarLoops GuardMemoryAffineReindex
  GuardMemoryRecursiveSource GuardMemoryTensorSource GuardMemoryDynamicTensorBackend
  GuardMemoryPointerBackend GuardMemoryArrayBackend GuardMemoryDynamicTensorLayout
  GuardMemoryTensorSourceRegion GuardMemoryRecursiveDomain GuardMemoryRecursiveRestore
  GuardMemorySourceParameters GuardMemoryScalarPointerBounds.
From GuardInterface Require Import GuardMemoryTiledPreparedPipeline ClightTensorCandidates
  ClightTensorRegionPackage ClightTensorRegionPreservation ClightTensorSourceCandidates ClightTensorCompleteCandidates
  ClightTensorBackendGuard.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Both cases carry the actual proposed/generated Loop. Witnesses are data;
    the caller does not provide a semantic callback or a fixed tiling target. *)
Inductive tensor_generated_candidate :=
| TensorGeneratedMapped (candidate : L.stmt) (steps : list memory_affine_reindex)
| TensorGeneratedTiled (candidate : L.stmt) (witnesses : list statement_tiling_witness).

Definition tensor_generated_loop proposal := match proposal with
  | TensorGeneratedMapped candidate _ | TensorGeneratedTiled candidate _ => candidate end.

Definition check_tensor_generated axes cap scalars instructions dimensions pointer logical_array layout live pool proposal :=
  let candidate := tensor_generated_loop proposal in
  let check := match proposal with
    | TensorGeneratedMapped _ steps => checked_memory_scalar_candidate axes cap scalars instructions layout [logical_array] candidate steps
    | TensorGeneratedTiled _ witnesses => checked_memory_scalar_generated_tiling axes cap scalars instructions layout [logical_array] candidate witnesses end in
  check_compile_tensor_candidate dimensions pointer logical_array layout
    (tensor_encoder_bounds (memory_scalar_static_bounds axes cap scalars)) live pool candidate check.

Theorem check_tensor_generated_sound axes cap scalars instructions dimensions pointer logical_array layout live pool proposal code :
  mayReturn (check_tensor_generated axes cap scalars instructions dimensions pointer logical_array layout live pool proposal) (Some code) ->
  compile_tensor_buffer_loop dimensions pointer logical_array layout
    (tensor_encoder_bounds (memory_scalar_static_bounds axes cap scalars)) live pool (tensor_generated_loop proposal) = Some code /\
  memory_scalar_candidate_certificate axes cap scalars instructions layout (tensor_generated_loop proposal).
Proof.
  unfold check_tensor_generated; intro CHECK; apply check_compile_tensor_candidate_sound in CHECK as [COMPILE VALID].
  split; [exact COMPILE|].
  destruct proposal; cbn in *.
  - apply checked_memory_scalar_candidate_correct with (arrays:=[logical_array]) (steps:=steps); exact VALID.
  - apply checked_memory_scalar_generated_tiling_correct with (arrays:=[logical_array]) (witnesses:=witnesses); exact VALID.
Qed.

Definition check_tensor_generated_region source (package : tensor_region_package source) live pool proposal :=
  let d := tensor_description package in let nest := tensor_nest package in
  check_tensor_generated (length (memory_nest_iterators nest)) (tensor_region_cap d) (length (tensor_region_scalars d))
    [tensor_source_instruction (tensor_operation package)] (tensor_region_dimensions d) (tensor_region_pointer d)
    (tensor_region_array d) (memory_nest_bounds nest++tensor_region_scalars d) live pool proposal.

Section ORIGINAL.
Variables dimensions : list tensor_dimension_source.
Variable nest : memory_source_nest.
Variable scalars : list ident.
Variables pointer logical_array : ident.
Variable operation : tensor_source_operation dimensions (memory_nest_iterators nest++scalars) pointer logical_array (memory_nest_leaf nest).
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable counts : list nat.
Variables scalar_values sizes : list Z.
Variable temps : temp_env.
Variables memory final : mem.
Variable after : temp_env.
Variable block : Values.block.
Variable base : ptrofs.
Variable cap : Z.
Variable live : list ident.
Variable pool : list (ident*ident).
Let parameters := map Z.of_nat counts++scalar_values.
Let layout := memory_nest_bounds nest++scalars.
Let instructions := [tensor_source_instruction operation].
Hypotheses (SHAPES:memory_nest_shapes nest) (FRESH:memory_nest_fresh nest)
  (UNIQUE:NoDup (memory_nest_iterators nest++scalars)).
Hypothesis PROTECTED : forall identifier, In identifier (memory_nest_iterators nest) ->
  ~In identifier (pointer::tensor_dimension_registers dimensions++scalars).
Hypotheses (LENGTH:length counts=length (memory_nest_iterators nest))
  (COUNTS:Forall (fun count=>count<>O /\ signed_range (Z.of_nat count)) counts)
  (BOUNDS:memory_nest_bindings (memory_nest_bounds nest) (map Z.of_nat counts) temps)
  (INITIAL:memory_nest_initial nest temps)
  (SCALARS:memory_nest_bindings scalars scalar_values temps) (SCALAR_RANGE:Forall signed_range scalar_values)
  (POINTER:temps!pointer=Some (Vptr block base))
  (OBSERVE:tensor_observe_dimensions dimensions temps=Some sizes)
  (GUARD:decision_run (Entry ge locals temps memory) (tensor_backend_guard dimensions) true)
  (BOX:tensor_source_operation_box operation counts scalar_values sizes=true)
  (WITHIN:MemoryNested.A.env_within (memory_scalar_static_bounds (length counts) cap (length scalar_values)) parameters)
  (SOURCE:exec_stmt fe ge locals temps memory (memory_nest_source nest) E0 after final Out_normal).

Theorem tensor_original_generated_restored proposal code :
  mayReturn (check_tensor_generated (length counts) cap (length scalar_values) instructions dimensions pointer logical_array layout live pool proposal) (Some code) ->
  exists restored, exec_stmt fe ge locals temps memory (Ssequence code (memory_recursive_restore nest)) E0 restored final Out_normal /\
    temp_agree live after restored.
Proof.
  intro CHECK; apply check_tensor_generated_sound in CHECK as [COMPILE CERTIFICATE].
  destruct (@tensor_original_source_model dimensions nest scalars pointer logical_array operation fe ge locals counts scalar_values sizes
    temps memory final after block base SHAPES FRESH UNIQUE PROTECTED LENGTH COUNTS BOUNDS INITIAL SCALARS
    POINTER OBSERVE GUARD BOX SOURCE) as [MODEL EXIT].
  destruct (@tensor_checked_candidate_execution fe ge locals dimensions pointer logical_array block base
    (length counts) cap (length scalar_values) instructions layout live pool (tensor_generated_loop proposal) code parameters temps
    (RuntimeState (tensor_pointer_locations logical_array block base sizes) memory)
    (RuntimeState (tensor_pointer_locations logical_array block base sizes) final) memory sizes
    COMPILE CERTIFICATE OBSERVE GUARD
    (@tensor_original_source_parameter_view nest scalars counts scalar_values temps COUNTS BOUNDS SCALARS SCALAR_RANGE)
    WITHIN (@tensor_original_source_parameter_length nest scalars counts scalar_values temps LENGTH SCALARS)
    MODEL eq_refl POINTER) as [candidate_temps [candidate_memory [MEMORY [_ [FRAME RUN]]]]].
  unfold tensor_buffer_view in MEMORY; inversion MEMORY; subst candidate_memory.
  eapply tensor_original_candidate_restore; eassumption.
Qed.
End ORIGINAL.

Theorem tensor_region_generated_execution source (package : tensor_region_package source) fe ge locals temps memory after final live pool proposal code :
  mayReturn (check_tensor_generated_region package live pool proposal) (Some code) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  decision_run (Entry ge locals temps memory) (tensor_region_guard package) true ->
  exists exit, exec_stmt fe ge locals temps memory (tensor_region_branch package code) E0 exit final Out_normal /\ temp_agree live after exit.
Proof.
  intros CHECK SOURCE GUARD; unfold check_tensor_generated_region in CHECK.
  apply (tensor_region_source_execution package) in SOURCE.
  pose proof (@tensor_complete_source_setup (tensor_region_dimensions (tensor_description package)) (tensor_nest package)
    (tensor_region_scalars (tensor_description package)) (tensor_region_pointer (tensor_description package))
    (tensor_region_array (tensor_description package)) (tensor_operation package) fe (tensor_region_cap (tensor_description package))
    (tensor_region_signed_cap package) (tensor_region_shapes package) (tensor_region_fresh package)
    (tensor_region_protected package) (tensor_region_used package) (tensor_region_dimension_reads package)
    (tensor_region_profile (tensor_description package)) (tensor_region_box_tree package) (tensor_region_box_compile package)
    ge locals temps after memory final SOURCE GUARD) as SETUP.
  destruct SETUP as [block [base [sizes FACTS]]].
  destruct FACTS as (LENGTH & COUNTS & BOUNDS & INITIAL & SCALARS & SIGNED & POINTER & OBSERVE & VOLUME & BOX & WITHIN).
  eapply (@tensor_original_generated_restored (tensor_region_dimensions (tensor_description package)) (tensor_nest package)
    (tensor_region_scalars (tensor_description package)) (tensor_region_pointer (tensor_description package))
    (tensor_region_array (tensor_description package)) (tensor_operation package) fe ge locals
    (memory_recursive_counts (memory_nest_bounds (tensor_nest package)) temps)
    (memory_recursive_parameters (tensor_region_scalars (tensor_description package)) temps) sizes temps memory final after block base
    (tensor_region_cap (tensor_description package)) live pool
    (tensor_region_shapes package) (tensor_region_fresh package) (tensor_region_unique package) (tensor_region_protected package)
    LENGTH COUNTS BOUNDS INITIAL SCALARS SIGNED POINTER OBSERVE VOLUME BOX WITHIN SOURCE proposal code).
  rewrite LENGTH; unfold memory_recursive_parameters; rewrite length_map; exact CHECK.
Qed.

Print Assumptions check_tensor_generated_sound.
Print Assumptions tensor_original_generated_restored.
Print Assumptions tensor_region_generated_execution.
