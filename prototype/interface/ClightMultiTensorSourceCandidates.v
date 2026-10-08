From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightNoWrap ClightFiniteRegion ClightStraightLine.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryScalarChecker GuardMemoryScalarLoops GuardMemoryPointerBackend GuardMemoryArrayBackend
  GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend GuardMemoryMultiTensorBackend GuardMemoryMultiTensorSequence
  GuardMemoryMultiTensorFrame GuardMemoryMultiTensorSourceRegion GuardMemoryRecursiveSource
  GuardMemoryRecursiveDomain GuardMemoryRecursiveRestore.
From GuardInterface Require Import ClightTensorBackendGuard ClightTensorCandidates ClightTensorSourceCandidates
  ClightTensorGeneratedCandidates ClightMultiTensorCandidates.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The candidate theorem now starts from the real original Clight nest, rather
    than taking an original Loop execution as an extra semantic callback.
    This is still a conditional local theorem: a factory must encode the entry
    box, layout, and footprint-separation premises with licensed guard reads. *)
Section ORIGINAL.
Variable dimensions : list tensor_dimension_source.
Variable nest : memory_source_nest.
Variables scalars pointers : list ident.
Variable items : list (multi_tensor_source_statement dimensions (memory_nest_iterators nest ++ scalars)).
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable counts : list nat.
Variables scalar_values sizes : list Z.
Variable temps after : temp_env.
Variables memory final : mem.
Variable cap : Z.
Variable live : list ident.
Variable pool : list (ident * ident).
Let parameters := map Z.of_nat counts ++ scalar_values.
Let layout := memory_nest_bounds nest ++ scalars.
Let instructions := map mt_instruction items.
Hypotheses (BODY : flatten_region (memory_nest_leaf nest) = map mt_statement items)
  (SHAPES : memory_nest_shapes nest) (FRESH : memory_nest_fresh nest)
  (UNIQUE : NoDup (memory_nest_iterators nest ++ scalars)).
Hypothesis PROTECTED : forall identifier, In identifier (memory_nest_iterators nest) ->
  ~ In identifier (pointers ++ tensor_dimension_registers dimensions ++ scalars).
Hypotheses (LENGTH : length counts = length (memory_nest_iterators nest))
  (COUNTS : Forall (fun count => count <> O /\ signed_range (Z.of_nat count)) counts)
  (BOUNDS : memory_nest_bindings (memory_nest_bounds nest) (map Z.of_nat counts) temps)
  (INITIAL : memory_nest_initial nest temps)
  (SCALARS : memory_nest_bindings scalars scalar_values temps) (SCALAR_RANGE : Forall signed_range scalar_values)
  (POINTERS : multi_tensor_pointer_check pointers instructions = true)
  (OBSERVE : tensor_observe_dimensions dimensions temps = Some sizes)
  (GUARD : decision_run (Entry ge locals temps memory) (tensor_backend_guard dimensions) true)
  (BOX : multi_tensor_body_box items counts scalar_values sizes = true)
  (WITHIN : MemoryNested.A.env_within (memory_scalar_static_bounds (length counts) cap (length scalar_values)) parameters)
  (SEPARATED : multi_tensor_separated_source (length counts) (length scalar_values) instructions parameters temps sizes)
  (SOURCE : exec_stmt fe ge locals temps memory (memory_nest_source nest) E0 after final Out_normal).

Lemma multi_tensor_original_parameter_view : MemoryNested.A.typed_view layout parameters temps.
Proof.
  apply tensor_source_bindings_view.
  - apply memory_nest_bindings_append; assumption.
  - apply Forall_app; split; [|exact SCALAR_RANGE].
    apply Forall_map,Forall_forall; intros count MEMBER.
    apply Forall_forall with (x := count) in COUNTS; [exact (proj2 COUNTS)|exact MEMBER].
Qed.

Lemma multi_tensor_original_parameter_length : length parameters = length layout.
Proof.
  unfold parameters,layout; rewrite !length_app,length_map.
  pose proof (Forall2_length SCALARS) as SCALAR_LENGTH; rewrite LENGTH,(memory_nest_lengths nest).
  exact (f_equal (fun amount => (length (memory_nest_bounds nest) + amount)%nat) (eq_sym SCALAR_LENGTH)).
Qed.

Theorem multi_tensor_original_generated_execution proposal code :
  mayReturn (check_multi_tensor_generated (length counts) cap (length scalar_values) instructions
    dimensions pointers layout live pool proposal) (Some code) ->
  exists target_temps,
    exec_stmt fe ge locals temps memory code E0 target_temps final Out_normal /\
    temp_agree (layout ++ multi_tensor_buffer_protected dimensions pointers ++ live) temps target_temps /\
    after = memory_nest_exit nest counts temps.
Proof.
  intro CHECK.
  assert (LAYOUT : tensor_layout_flag sizes = true) by
    (exact (@tensor_backend_guard_accepts (Entry ge locals temps memory) dimensions sizes OBSERVE GUARD)).
  destruct (@tensor_observe_dimensions_sound dimensions temps sizes OBSERVE) as [DIMENSIONS _].
  destruct (@multi_tensor_source_region_decode dimensions nest scalars pointers items fe ge locals
    counts scalar_values sizes temps memory after final BODY SHAPES FRESH UNIQUE PROTECTED LENGTH COUNTS BOUNDS INITIAL
    LAYOUT DIMENSIONS SCALARS POINTERS BOX SOURCE) as [MODEL EXIT].
  destruct (@check_multi_tensor_generated_execution (length counts) cap (length scalar_values) instructions
    dimensions pointers layout live pool proposal code parameters temps memory final sizes fe ge locals
    CHECK OBSERVE GUARD multi_tensor_original_parameter_view WITHIN multi_tensor_original_parameter_length SEPARATED MODEL)
    as [target_temps [FRAME [_ RUN]]].
  exists target_temps; split; [exact RUN|split; assumption].
Qed.

(** Restoration reads the unchanged original bound words. It restores every
    source iterator, including live ones, while candidate scratch temporaries
    remain governed by the existing frame and scratch-allocation checks. *)
Theorem multi_tensor_original_generated_restored proposal code :
  mayReturn (check_multi_tensor_generated (length counts) cap (length scalar_values) instructions
    dimensions pointers layout live pool proposal) (Some code) ->
  exists restored,
    exec_stmt fe ge locals temps memory (Ssequence code (memory_recursive_restore nest)) E0 restored final Out_normal /\
    temp_agree live after restored.
Proof.
  intro CHECK; destruct (@multi_tensor_original_generated_execution proposal code CHECK) as [target_temps [RUN [FRAME EXIT]]].
  assert (LIVE : temp_agree (memory_nest_bounds nest ++ live) temps target_temps).
  { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER; apply in_app_or in MEMBER as [BOUND|PUBLIC].
    - apply in_or_app; left; unfold layout; apply in_or_app; left; exact BOUND.
    - apply in_or_app; right; apply in_or_app; right; exact PUBLIC. }
  assert (TARGET_BOUNDS : memory_nest_bindings (memory_nest_bounds nest) (map Z.of_nat counts) target_temps).
  { eapply memory_nest_bindings_frame; [|exact BOUNDS]; eapply temp_agree_weaken; [|exact LIVE].
    intros identifier MEMBER; apply in_or_app; left; exact MEMBER. }
  assert (VALUES : map Z.of_nat counts = memory_recursive_parameters (memory_nest_bounds nest) temps).
  { apply tensor_source_binding_values; [exact BOUNDS|].
    apply Forall_map,Forall_forall; intros count MEMBER.
    apply Forall_forall with (x := count) in COUNTS; [exact (proj2 COUNTS)|exact MEMBER]. }
  rewrite (@memory_recursive_exit_counts nest counts temps VALUES) in EXIT.
  exists (memory_recursive_exit nest target_temps); split.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := target_temps) (m1 := final); [exact RUN|].
    apply memory_recursive_restore_execution; [exact FRESH|].
    intros identifier MEMBER; exact (@tensor_source_binding_domains (memory_nest_bounds nest) (map Z.of_nat counts)
      target_temps TARGET_BOUNDS identifier MEMBER).
  - rewrite EXIT; apply memory_recursive_exit_frame; exact LIVE.
Qed.
End ORIGINAL.

Print Assumptions multi_tensor_original_parameter_view.
Print Assumptions multi_tensor_original_parameter_length.
Print Assumptions multi_tensor_original_generated_execution.
Print Assumptions multi_tensor_original_generated_restored.
