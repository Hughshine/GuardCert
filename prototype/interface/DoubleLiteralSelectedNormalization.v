From Stdlib Require Import List Bool.
From compcert.lib Require Import Integers Floats.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import GuardCompiler ClightGuard ClightSyntaxEquality
  ClightRegionProgress ClightFiniteRegion ClightCountedLoop ClightGlobalScope ClightTempFrame
  ClightTempFootprint ClightTempScope ClightProjectedExecution ClightMemorySteps
  ClightScopedPrivateRegion CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryDoubleValue GuardMemoryDoubleSource
  GuardMemoryDoubleLiteralOperands.
From GuardInterface Require Import ClightScopedSelectedRegion ClightScopedSelectedRegionProof
  OriginalMatmulProgramCompiler.
Import ListNotations.
Set Implicit Arguments.

Lemma cast_to_double_is_float value input_type memory result :
  sem_cast value input_type memory_double_type memory=Some result ->
  exists number, result=Vfloat number.
Proof.
  destruct input_type,value;
    repeat match goal with
    | size : intsize |- _ => destruct size
    | size : floatsize |- _ => destruct size
    | sign : signedness |- _ => destruct sign
    end; cbn; try discriminate; intro CAST; inversion CAST; eauto.
Qed.

Definition select_double_literal_assignment source : option statement :=
  match source with
  | Sassign lhs rhs => if type_eq (typeof lhs) memory_double_type then
      match normalize_double_literal_operands rhs with
      | Some normalized => if expression_eq rhs normalized then None
          else Some (Sassign lhs normalized)
      | None => None end
    else None
  | _ => None end.

Theorem selected_double_literal_assignment_execution source target fe ge locals temps memory
  trace after final outcome :
  select_double_literal_assignment source=Some target ->
  exec_stmt fe ge locals temps memory source trace after final outcome ->
  exec_stmt fe ge locals temps memory target trace after final outcome.
Proof.
  destruct source; cbn [select_double_literal_assignment]; try discriminate.
  destruct (type_eq (typeof e) memory_double_type) as [TYPE|]; [|discriminate].
  destruct (normalize_double_literal_operands e0) as [normalized|] eqn:NORMAL; [|discriminate].
  destruct (expression_eq e0 normalized); [discriminate|].
  intros SELECT RUN; inversion SELECT; subst target; inversion RUN; subst.
  match goal with EVAL : eval_expr _ _ _ _ e0 ?value,
    CAST : sem_cast ?value (typeof e0) (typeof e) _=Some ?converted |- _ =>
    rewrite TYPE in CAST;
    destruct (@cast_to_double_is_float value (typeof e0) memory converted CAST) as [number RESULT];
    subst converted;
    pose proof (@normalized_double_literal_operands_forward ge locals after memory
      e0 normalized value (Vfloat number) NORMAL EVAL CAST) as NORMALIZED
  end.
  eapply exec_Sassign; [eassumption|exact NORMALIZED| |eassumption].
  rewrite TYPE,(@normalized_double_literal_operands_type e0 normalized NORMAL); reflexivity.
Qed.

Definition double_literal_assignment_supported source :=
  match source with Sassign _ _ => true | _ => false end.
Theorem double_literal_assignment_supported_sound source :
  double_literal_assignment_supported source=true -> exists MODEL : region_progress source, True.
Proof.
  destruct source; cbn [double_literal_assignment_supported]; try discriminate; intro SUPPORTED.
  exists (@finite_progress (Sassign e e0) eq_refl ltac:(discriminate)); exact I.
Qed.

Theorem selected_double_literal_assignment_contract live reference source target :
  select_double_literal_assignment source=Some target ->
  ScopedPrivateRegion.projected_region_contract live reference [] source target.
Proof.
  intro SELECT; assert (SHAPE : exists lhs rhs, source=Sassign lhs rhs).
  { destruct source; cbn [select_double_literal_assignment] in SELECT; try discriminate; eauto. }
  destruct SHAPE as [lhs [rhs SHAPE]]; subst source.
  intros temps p locals le tle memory after final GLOBAL LOCAL SCOPE FRAME SOURCE f k.
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv p) locals le memory
    (Sassign lhs rhs) E0 after final Out_normal SOURCE live tle [] ltac:(constructor) SCOPE FRAME)
    as [transported [TRANSPORT FRAME_OUT]].
  exists transported,final; split.
  - apply normal_fragment_steps.
    eapply selected_double_literal_assignment_execution; [exact SELECT|exact TRANSPORT].
  - split; [exact FRAME_OUT|apply memory_equivalent_refl].
Qed.

Definition normalize_selected_double_literals chosen p :=
  match chosen with [] => p | _ =>
    ScopedSelectedRegion.transform_program chosen [] double_literal_assignment_supported
      select_double_literal_assignment p end.
Theorem normalize_selected_double_literals_correct chosen p :
  forward_simulation (Clight.semantics2 p)
    (Clight.semantics2 (normalize_selected_double_literals chosen p)).
Proof.
  destruct chosen as [|label rest]; cbn [normalize_selected_double_literals].
  - apply unchanged_clight_simulation.
  - eapply ScopedSelectedRegionProof.transform_program_correct2 with (live:=program_temps p) (globals:=[]).
    + exact double_literal_assignment_supported_sound.
    + intros name fd MEMBER; destruct fd; [intros identifier IMPOSSIBLE; contradiction|exact I].
    + intros source target SELECT; eapply selected_double_literal_assignment_contract; exact SELECT.
    + apply program_scope_computed.
    + intros identifier MEMBER IMPOSSIBLE; contradiction.
Qed.

Print Assumptions selected_double_literal_assignment_execution.
Print Assumptions selected_double_literal_assignment_contract.
Print Assumptions normalize_selected_double_literals_correct.
