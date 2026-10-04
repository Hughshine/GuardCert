From Stdlib Require Import List ZArith.
From compcert.cfrontend Require Import Clight Ctypes.
From Guard Require Import ClightFrontendLoopProtocol ClightRectangularLoops ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryNaryAffineAccess GuardMemoryNaryCompute
  GuardMemoryAffineSourceExpressions GuardMemoryPointerCompute.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExamples AffineNestGuardPackage.
Import ListNotations.
Local Open Scope Z_scope.

Definition affine_memory_example_address := MemorySourceAdd
  (MemorySourceAdd(MemorySourceScale 16(MemorySourceTemp 1%positive))
    (MemorySourceScale 4(MemorySourceTemp 2%positive)))(MemorySourceTemp 3%positive).
Definition affine_memory_example_access := MemoryNaryAccess 10%positive(RectangleShape 256 1 1 0)
  affine_memory_example_address ([16;4;1;0;0;0;0],0).
Definition affine_memory_example_operation := MemoryNaryCompute affine_memory_example_access [] (ParameterValue 6)
  (Etempvar 9%positive type_int32s).
Definition affine_memory_example_leaf := memory_pointer_compute_statement affine_memory_example_operation.
Definition affine_memory_example_inner_body :=
  Ssequence(Sset 6%positive(memory_source_affine_code affine_example_second))
    (Ssequence(rectangle_reset 3%positive)(frontend_counted_loop 3%positive 6%positive affine_memory_example_leaf)).
Definition affine_memory_example_outer_body :=
  Ssequence(Sset 5%positive(memory_source_affine_code affine_example_first))
    (Ssequence(rectangle_reset 2%positive)(frontend_counted_loop 2%positive 5%positive affine_memory_example_inner_body)).
Definition affine_memory_example_child := AffineSourceAxis 2%positive 5%positive affine_example_first affine_memory_example_inner_body
  (AffineSourceAxis 3%positive 6%positive affine_example_second affine_memory_example_leaf(AffineSourceLeaf affine_memory_example_leaf)).
Definition affine_memory_example_source := frontend_counted_loop 1%positive 4%positive affine_memory_example_outer_body.
Definition affine_memory_example_parameters := [4%positive;7%positive;8%positive;9%positive].
Definition affine_memory_example_parameter_ranges := [(1,4);(-2,3);(0,5);(-256,257)].
Definition affine_memory_example_axes := [(-2,3);(0,4);(0,7)].
Definition affine_memory_example_live := [1%positive;2%positive;3%positive;4%positive;5%positive;6%positive;7%positive;8%positive;9%positive;10%positive].
Definition affine_memory_example_proposal private result := AffineGuardProposal 1%positive 4%positive affine_memory_example_outer_body
  affine_memory_example_child (affine_memory_example_axes++affine_memory_example_parameter_ranges) (-64) 128
  [10%positive] [affine_memory_example_operation] affine_memory_example_parameter_ranges (-2) 3 [(0,4);(0,7)] private result.
Definition affine_memory_example_accept private result := match check_affine_guard_package affine_memory_example_source
  affine_memory_example_parameters affine_memory_example_live(affine_memory_example_proposal private result) with Some _=>true|None=>false end.

Example real_three_level_memory_guard_package_accepted :
  affine_memory_example_accept [101%positive;104%positive;102%positive;105%positive;103%positive;106%positive] 107%positive=true.
Proof. vm_compute; reflexivity. Qed.
Example public_result_scratch_refused :
  affine_memory_example_accept [101%positive;104%positive;102%positive;105%positive;103%positive;106%positive] 9%positive=false.
Proof. vm_compute; reflexivity. Qed.
Example colliding_private_controls_refused :
  affine_memory_example_accept [101%positive;104%positive;102%positive;105%positive;103%positive;103%positive] 107%positive=false.
Proof. vm_compute; reflexivity. Qed.
Example unallocated_private_controls_refused : affine_memory_example_accept [] 107%positive=false.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions real_three_level_memory_guard_package_accepted.
Print Assumptions public_result_scratch_refused.
Print Assumptions colliding_private_controls_refused.
Print Assumptions unallocated_private_controls_refused.
