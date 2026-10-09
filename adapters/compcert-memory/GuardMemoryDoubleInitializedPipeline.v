From Stdlib Require Import List ZArith.
From compcert.common Require Import AST.
From compcert.lib Require Import Maps.
From GuardMemory Require Import GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceLoopModel
  GuardMemoryDoubleInitializedReductionData GuardMemoryDoubleInitializedNestModel
  GuardMemoryDoublePipelineTransport GuardMemoryDoublePolyhedral.
Import ListNotations.
Set Implicit Arguments.

(** Actual checked descriptor data supplies both instructions and names.
    Model extraction and final candidate validation use the same request. *)
Definition double_initialized_pipeline_model (outers : list ident) description :=
  double_pipeline_statement (double_source_initialized_nest_model
    (double_source_instruction_model (initialized_reduction_initial_instruction description))
    (double_source_instruction_model (initialized_reduction_body_instruction description)) (length outers) 0).
Definition double_initialized_pipeline_request outers description : DoubleAssignmentIRs.Loop.t :=
  (double_initialized_pipeline_model outers description, [initialized_reduction_header description],
   map (fun key => (key,tt)) (initialized_reduction_header description::
     map fst (PTree.elements (double_initialized_reduction_layouts description)))).
Theorem double_initialized_pipeline_model_execution outers description parameters before after :
  SL.loop_semantics (double_source_initialized_nest_model
    (double_source_instruction_model (initialized_reduction_initial_instruction description))
    (double_source_instruction_model (initialized_reduction_body_instruction description)) (length outers) 0)
    parameters before after <->
  DoubleAssignmentIRs.Loop.loop_semantics (double_initialized_pipeline_model outers description)
    parameters before after.
Proof. apply double_pipeline_execution. Qed.

Print Assumptions double_initialized_pipeline_model_execution.
