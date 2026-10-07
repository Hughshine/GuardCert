From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightRectangularGuard ClightNoWrap ClightRedundantSet.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryRecursiveDomain GuardMemoryRecursiveRestore
  GuardMemorySourceParameters GuardMemoryTensorSource GuardMemoryTensorSourceRegion GuardMemoryDynamicTensorBackend
  GuardMemoryScalarChecker GuardMemoryScalarPointerBounds GuardMemoryArrayBackend GuardMemoryDynamicTensorLayout.
From GuardInterface Require Import ClightTensorBackendGuard ClightTensorVolumeGuard ClightTensorSourceGuard
  ClightTensorBoxGuard ClightTensorCompleteGuard ClightTensorCandidates ClightTensorSourceCandidates.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma tensor_dimension_registers_tail dimensions identifier :
  In identifier(tensor_dimension_registers(tl dimensions)) -> In identifier(tensor_dimension_registers dimensions).
Proof. destruct dimensions as [|source dimensions]; cbn; [contradiction|destruct source; cbn; auto]. Qed.
Lemma tensor_word_parameter_bindings identifiers entry : Forall(fun identifier=>register_domain identifier entry)identifiers ->
  memory_nest_bindings identifiers(memory_recursive_parameters identifiers(entry_temps entry))(entry_temps entry).
Proof.
  intro WORDS; induction WORDS as [|identifier identifiers [word WORD] WORDS IH]; cbn [memory_recursive_parameters map]; constructor.
  - unfold temp_word; rewrite WORD,Int.repr_signed; reflexivity.
  - exact IH.
Qed.

Section COMPLETE_CANDIDATE.
Variables dimensions : list tensor_dimension_source.
Variable nest : memory_source_nest.
Variable scalars : list ident.
Variables pointer logical_array : ident.
Variable operation : tensor_source_operation dimensions(memory_nest_iterators nest++scalars)pointer logical_array(memory_nest_leaf nest).
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable cap : Z.
Hypothesis CAP : signed_range cap.
Hypotheses (SHAPES:memory_nest_shapes nest)(FRESH:memory_nest_fresh nest)(UNIQUE:NoDup(memory_nest_iterators nest++scalars)).
Hypothesis PROTECTED : forall identifier,In identifier(memory_nest_iterators nest) ->
  ~In identifier(pointer::tensor_dimension_registers dimensions++scalars).
Hypothesis USED : forall identifier,In identifier scalars -> In identifier(tensor_dimension_registers(tl dimensions)) \/
  exists index,nth_error(memory_nest_iterators nest++scalars)index=Some identifier /\
    In index(memory_source_parameter_positions(tensor_source_value operation)).
Hypothesis DIMENSION_READS : forall identifier,In identifier(tensor_dimension_registers dimensions) ->
  In identifier(memory_nest_bounds nest) \/ In identifier(tensor_dimension_registers(tl dimensions)).
Let layout:=tensor_coordinate_layout dimensions nest scalars.
Let accesses:=tensor_operation_accesses operation.
Variable profile : list(Z*Z).
Variable tree : decision_tree.
Hypothesis COMPILE : compile_tensor_box_guard layout profile(memory_nest_bounds nest)scalars dimensions accesses=Some tree.
Variable ge : genv.
Variable locals : env.
Variable temps after : temp_env.
Variables memory final : mem.
Hypothesis SOURCE : exec_stmt fe ge locals temps memory(memory_nest_source nest)E0 after final Out_normal.
Hypothesis GUARD : decision_run(Entry ge locals temps memory)(tensor_complete_tree dimensions nest scalars cap profile tree)true.
Let entry:=Entry ge locals temps memory.
Let counts:=memory_recursive_counts(memory_nest_bounds nest)temps.
Let values:=memory_recursive_parameters scalars temps.
Lemma tensor_complete_protected_tail : forall identifier,In identifier(memory_nest_iterators nest) ->
  ~In identifier(pointer::tensor_dimension_registers(tl dimensions)++scalars).
Proof.
  intros identifier ITERATOR MEMBER; apply(@PROTECTED identifier ITERATOR).
  destruct MEMBER as [POINTER|MEMBER]; [left; exact POINTER|right].
  apply in_app_or in MEMBER as [DIMENSION|SCALAR]; apply in_or_app;
    [left; apply tensor_dimension_registers_tail; exact DIMENSION|right; exact SCALAR].
Qed.
Lemma tensor_complete_source_setup : exists block base sizes,
  length counts=length(memory_nest_iterators nest) /\
  Forall(fun count=>count<>O /\ signed_range(Z.of_nat count))counts /\
  memory_nest_bindings(memory_nest_bounds nest)(map Z.of_nat counts)temps /\
  memory_nest_initial nest temps /\ memory_nest_bindings scalars values temps /\ Forall signed_range values /\
  temps!pointer=Some(Vptr block base) /\ tensor_observe_dimensions dimensions temps=Some sizes /\
  decision_run entry(tensor_backend_guard dimensions)true /\ tensor_source_operation_box operation counts values sizes=true /\
  MemoryNested.A.env_within(memory_scalar_static_bounds(length counts)cap(length values))(map Z.of_nat counts++values).
Proof.
  assert(DEFINED:tensor_original_defined nest fe entry)by(exists after,final; exact SOURCE).
  destruct(@tensor_complete_guard_sound dimensions nest scalars pointer logical_array operation fe cap CAP SHAPES FRESH
    tensor_complete_protected_tail USED DIMENSION_READS profile tree COMPILE entry DEFINED GUARD)
    as [INITIAL [RANGES [sizes [OBSERVE [LAYOUT BOX]]]]].
  destruct(@memory_recursive_parameter_data cap(memory_nest_bounds nest)ge locals temps memory RANGES)
    as [BOUNDS [VALUES [COUNTS _]]].
  assert(POSITIVE:Forall(fun identifier=>0<Int.signed(temp_word identifier temps))(memory_nest_bounds nest)).
  { eapply Forall_impl; [|exact RANGES]; intros identifier [_ RANGE]; exact(proj1 RANGE). }
  destruct(@tensor_source_region_first_capability dimensions nest scalars pointer logical_array operation fe ge locals temps memory after final
    SHAPES FRESH tensor_complete_protected_tail USED POSITIVE INITIAL SOURCE)as [POINTER WORDS].
  destruct POINTER as [block [base POINTER]].
  assert(SCALARS:memory_nest_bindings scalars values temps).
  { apply tensor_word_parameter_bindings with(entry:=entry); apply Forall_forall; intros identifier MEMBER.
    apply WORDS; apply in_or_app; right; exact MEMBER. }
  assert(LENGTH:length counts=length(memory_nest_iterators nest)).
  { unfold counts,memory_recursive_counts,memory_recursive_parameters; rewrite !length_map,memory_nest_lengths; reflexivity. }
  assert(SIGNED:Forall signed_range values)by(apply memory_recursive_scalar_values_range).
  exists block,base,sizes; split; [exact LENGTH|]; split; [exact COUNTS|]; split; [exact BOUNDS|];
    split; [exact INITIAL|]; split; [exact SCALARS|]; split; [exact SIGNED|]; split; [exact POINTER|];
    split; [exact OBSERVE|]; split; [|split; [exact BOX|]].
  - pose proof(@tensor_backend_guard_run entry dimensions sizes OBSERVE)as RUN.
    rewrite(proj2(tensor_volume_check_layout sizes)LAYOUT)in RUN; exact RUN.
  - unfold counts; rewrite VALUES; unfold memory_recursive_counts,memory_recursive_parameters at 1;
      rewrite !length_map; eapply memory_scalar_validator_count_scalar_ranges; eassumption.
Qed.

Theorem tensor_complete_tiled_execution live pool rows columns code :
  CoreAlarmed.Base.mayReturn(check_tensor_tiled(length(memory_nest_iterators nest))cap(length scalars)
    [tensor_source_instruction operation]dimensions pointer logical_array(memory_nest_bounds nest++scalars)live pool rows columns)(Some code) ->
  exists restored,exec_stmt fe ge locals temps memory(Ssequence code(memory_recursive_restore nest))E0 restored final Out_normal /\
    temp_agree live after restored.
Proof.
  intro CHECK; destruct tensor_complete_source_setup as [block [base [sizes FACTS]]].
  destruct FACTS as(LENGTH & COUNTS & BOUNDS & INITIAL & SCALARS & SIGNED & POINTER & OBSERVE & VOLUME & BOX & WITHIN).
  eapply(@tensor_original_tiled_restored dimensions nest scalars pointer logical_array operation fe ge locals counts values sizes
    temps memory final after block base cap live pool SHAPES FRESH UNIQUE PROTECTED LENGTH COUNTS BOUNDS INITIAL
    SCALARS SIGNED POINTER OBSERVE VOLUME BOX WITHIN SOURCE rows columns code).
  rewrite LENGTH; unfold values,memory_recursive_parameters; rewrite length_map; exact CHECK.
Qed.
Theorem tensor_complete_mapped_execution live pool candidate steps code :
  CoreAlarmed.Base.mayReturn(check_tensor_mapped(length(memory_nest_iterators nest))cap(length scalars)
    [tensor_source_instruction operation]dimensions pointer logical_array(memory_nest_bounds nest++scalars)live pool candidate steps)(Some code) ->
  exists restored,exec_stmt fe ge locals temps memory(Ssequence code(memory_recursive_restore nest))E0 restored final Out_normal /\
    temp_agree live after restored.
Proof.
  intro CHECK; destruct tensor_complete_source_setup as [block [base [sizes FACTS]]].
  destruct FACTS as(LENGTH & COUNTS & BOUNDS & INITIAL & SCALARS & SIGNED & POINTER & OBSERVE & VOLUME & BOX & WITHIN).
  eapply(@tensor_original_mapped_restored dimensions nest scalars pointer logical_array operation fe ge locals counts values sizes
    temps memory final after block base cap live pool SHAPES FRESH UNIQUE PROTECTED LENGTH COUNTS BOUNDS INITIAL
    SCALARS SIGNED POINTER OBSERVE VOLUME BOX WITHIN SOURCE candidate steps code).
  rewrite LENGTH; unfold values,memory_recursive_parameters; rewrite length_map; exact CHECK.
Qed.
End COMPLETE_CANDIDATE.
Print Assumptions tensor_word_parameter_bindings.
Print Assumptions tensor_complete_source_setup.
Print Assumptions tensor_complete_tiled_execution.
Print Assumptions tensor_complete_mapped_execution.
