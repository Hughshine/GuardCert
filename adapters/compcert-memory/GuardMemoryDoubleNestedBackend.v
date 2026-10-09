From Stdlib Require Import List ZArith Bool.
From compcert.lib Require Import Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightFramedLoop.
From GuardMemory Require Import GuardMemoryDoubleAssignment GuardMemoryDoublePolyhedral
  GuardMemoryRangedNested GuardMemoryDoubleTensorBackend.
Import ListNotations.
Set Implicit Arguments.
Module DoubleNested := RangedNestedClightFor DoubleAssignmentInstr DoubleAssignmentIRs.Loop.

Section BACKEND.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable layouts : PTree.t (list Z).
Hypothesis STATIC : double_tensor_static ge locals layouts.
Definition double_no_capability (_ : temp_env) := True.
Lemma double_no_capability_frame before after :
  temp_agree [] before after -> double_no_capability before -> double_no_capability after.
Proof. intros; exact I. Qed.
Definition double_tensor_instruction_backend : DoubleNested.instruction_backend fe ge locals
  (double_tensor_view ge layouts) double_no_capability.
Proof.
  refine {|DoubleNested.lower_instruction:=double_lower_instruction layouts|}.
  intros instruction codes values code temps memory source target writes reads CODE OPERANDS RUN VIEW _.
  eapply double_tensor_instruction_execution; eauto.
Defined.

(** Checked data-only lowering. The source parameter environment and public
    temporaries are framed; scratch loop counters are private. *)
Definition compile_double_tensor_loop layout bounds live pool loop :=
  if DoubleNested.N.scratch_check pool (layout++live) then
    DoubleNested.N.compile_nested_raw (double_lower_instruction layouts) layout bounds pool loop
  else None.
Theorem compile_double_tensor_loop_correct layout bounds live pool loop code parameters temps source target memory :
  compile_double_tensor_loop layout bounds live pool loop=Some code ->
  DoubleNested.A.typed_view layout parameters temps -> DoubleNested.A.env_within bounds parameters ->
  DoubleAssignmentIRs.Loop.loop_semantics loop parameters source target ->
  double_tensor_view ge layouts source memory ->
  exists target_temps target_memory, double_tensor_view ge layouts target target_memory /\
    temp_agree (layout++live) temps target_temps /\
    exec_stmt fe ge locals temps memory code E0 target_temps target_memory Out_normal.
Proof.
  unfold compile_double_tensor_loop; intros COMPILE VIEW WITHIN RUN MEMORY.
  destruct (DoubleNested.N.scratch_check pool (layout++live)) eqn:FRESH; [|discriminate].
  destruct (@DoubleNested.compile_nested_correct fe ge locals (double_tensor_view ge layouts) []
    double_no_capability double_no_capability_frame double_tensor_instruction_backend loop
    layout bounds pool code parameters temps source target memory live COMPILE
    (DoubleNested.N.scratch_check_sound pool _ FRESH) WITHIN VIEW RUN MEMORY I
    ltac:(intros identifier MEMBER; contradiction))
    as [target_temps [target_memory [TARGET [FRAME EXEC]]]].
  exists target_temps,target_memory; auto.
Qed.
End BACKEND.

Print Assumptions DoubleNested.compile_operands_ranged.
Print Assumptions DoubleNested.compile_nested_correct.
Print Assumptions double_tensor_instruction_backend.
Print Assumptions compile_double_tensor_loop_correct.
