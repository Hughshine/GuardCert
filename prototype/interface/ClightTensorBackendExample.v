From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Ctypes Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Guard Require Import ClightCondition.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryScalarLoops GuardMemoryScalarChecker GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend.
From GuardInterface Require Import ClightTensorBackendGuard ClightTensorCandidates.
Import ListNotations.
Local Open Scope Z_scope.

Definition tensor_demo_dimensions := [TensorDimensionTemp 1%positive;TensorDimensionTemp 2%positive;TensorDimensionConstant 5].
Definition tensor_demo_access := (20%positive,[([1;0;0;0;0],0);([0;1;0;0;0],0);([0;0;1;0;0],0)]).
Definition tensor_demo_rmw := MemoryInstruction tensor_demo_access[tensor_demo_access]
  (AddValue(LoadedValue 0)(ParameterValue 4)).
Definition tensor_demo_codes := map(fun identifier=>Etempvar identifier type_int32s)
  [6%positive;7%positive;8%positive;2%positive;5%positive].
Definition tensor_demo_layout := [1%positive;3%positive;4%positive;2%positive;5%positive].
Definition tensor_demo_pool := [(101%positive,102%positive);(103%positive,104%positive);(105%positive,106%positive)].
Definition tensor_demo_source_loop := memory_scalar_rectangle 0 3 2[tensor_demo_rmw].
Definition tensor_demo_compile pool := compile_tensor_buffer_loop tensor_demo_dimensions 9%positive 20%positive
  tensor_demo_layout(tensor_encoder_bounds(memory_scalar_static_bounds 3 32 2))[6%positive;7%positive;8%positive]pool tensor_demo_source_loop.

Example tensor_demo_vector_rmw_lowered :
  match tensor_lower_instruction 9%positive 20%positive tensor_demo_dimensions tensor_demo_rmw tensor_demo_codes with
  | Some _ => true | None => false end=true.
Proof. vm_compute; reflexivity. Qed.
Example tensor_demo_three_axis_loop_lowered :
  match tensor_demo_compile tensor_demo_pool with Some _=>true|None=>false end=true.
Proof. vm_compute; reflexivity. Qed.
Example tensor_demo_layout_scratch_collision_refused :
  tensor_demo_compile[(2%positive,102%positive);(103%positive,104%positive);(105%positive,106%positive)]=None.
Proof. vm_compute; reflexivity. Qed.
Example tensor_demo_pointer_scratch_collision_refused :
  tensor_demo_compile[(9%positive,102%positive);(103%positive,104%positive);(105%positive,106%positive)]=None.
Proof. vm_compute; reflexivity. Qed.
Example tensor_demo_rank_mismatch_refused :
  tensor_lower_access 20%positive tensor_demo_dimensions(20%positive,[([1;0],0);([0;1],0)])tensor_demo_codes=None.
Proof. vm_compute; reflexivity. Qed.
Example tensor_demo_unknown_array_refused :
  tensor_lower_access 20%positive tensor_demo_dimensions(21%positive,snd tensor_demo_access)tensor_demo_codes=None.
Proof. vm_compute; reflexivity. Qed.
Example tensor_demo_missing_operand_refused :
  tensor_lower_instruction 9%positive 20%positive tensor_demo_dimensions
    (MemoryInstruction tensor_demo_access[tensor_demo_access](AddValue(LoadedValue 2)(ConstantValue 1)))tensor_demo_codes=None.
Proof. vm_compute; reflexivity. Qed.
Example tensor_demo_invalid_tile_refused :
  check_tensor_tiled 3 32 2[tensor_demo_rmw]tensor_demo_dimensions 9%positive 20%positive tensor_demo_layout []tensor_demo_pool 0 2=pure None.
Proof. reflexivity. Qed.

Definition tensor_demo_temps := PTree.set 1%positive(Vint(Int.repr 3))
  (PTree.set 2%positive(Vint(Int.repr 31))(PTree.empty val)).
Example tensor_demo_observed_layout : tensor_observe_dimensions tensor_demo_dimensions tensor_demo_temps=Some[3;31;5].
Proof. vm_compute; reflexivity. Qed.
Example tensor_demo_missing_dimension_refused :
  tensor_observe_dimensions tensor_demo_dimensions(PTree.set 1%positive(Vint(Int.repr 3))(PTree.empty val))=None.
Proof. vm_compute; reflexivity. Qed.
Example tensor_demo_pointer_dimension_refused block base :
  tensor_observe_dimensions[TensorDimensionTemp 2%positive](PTree.set 2%positive(Vptr block base)(PTree.empty val))=None.
Proof. reflexivity. Qed.
Example tensor_demo_modular_constant_observed :
  tensor_observe_dimensions[TensorDimensionConstant 4294967301](PTree.empty val)=Some[5].
Proof. vm_compute; reflexivity. Qed.
Theorem tensor_demo_actual_guard_accepts ge locals memory :
  decision_run(Entry ge locals tensor_demo_temps memory)(tensor_backend_guard tensor_demo_dimensions)true.
Proof. exact(@tensor_backend_guard_run(Entry ge locals tensor_demo_temps memory)tensor_demo_dimensions[3;31;5]tensor_demo_observed_layout). Qed.

Print Assumptions tensor_demo_vector_rmw_lowered.
Print Assumptions tensor_demo_three_axis_loop_lowered.
Print Assumptions tensor_demo_layout_scratch_collision_refused.
Print Assumptions tensor_demo_pointer_scratch_collision_refused.
Print Assumptions tensor_demo_rank_mismatch_refused.
Print Assumptions tensor_demo_unknown_array_refused.
Print Assumptions tensor_demo_missing_operand_refused.
Print Assumptions tensor_demo_invalid_tile_refused.
Print Assumptions tensor_demo_observed_layout.
Print Assumptions tensor_demo_missing_dimension_refused.
Print Assumptions tensor_demo_pointer_dimension_refused.
Print Assumptions tensor_demo_modular_constant_observed.
Print Assumptions tensor_demo_actual_guard_accepts.
