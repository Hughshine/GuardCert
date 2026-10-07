From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightCondition ClightPureExpr ClightRedundantSet ClightRectangularGuard
  ClightRectangularStore ClightFrontendLoopProtocol ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryPointerAccess
  GuardMemoryFlatArrayBackend GuardMemoryAffineSourceExpressions GuardMemoryRecursiveSource
  GuardMemoryRecursiveGuard GuardMemorySourceValueInterface GuardMemorySourceParameters
  GuardMemoryDynamicTensorBackend GuardMemoryTensorSource GuardMemoryTensorSourceRegion GuardMemoryScalarLoops.
From GuardInterface Require Import ClightTensorSourceGuard ClightTensorBackendGuard.
Import ListNotations.
Local Open Scope Z_scope.

(** The source index is written independently of the descriptor constructor:
    ((i * ld) + j) * 5 + k.  The target encoder uses a suffix-volume sum. *)
Definition tensor_source_demo_dimensions :=
  [TensorDimensionTemp 1%positive;TensorDimensionTemp 2%positive;TensorDimensionConstant 5].
Definition tensor_source_demo_layout := [6%positive;7%positive;8%positive;2%positive;5%positive].
Definition tensor_source_demo_coordinates :=
  [MemorySourceTemp 6%positive;MemorySourceTemp 7%positive;MemorySourceTemp 8%positive].
Definition tensor_source_demo_index := Ebinop Oadd
  (Ebinop Omul
    (Ebinop Oadd(Ebinop Omul(Etempvar 6%positive type_int32s)(Etempvar 2%positive type_int32s)type_int32s)
      (Etempvar 7%positive type_int32s)type_int32s)
    (Econst_int(Int.repr 5)type_int32s)type_int32s)
  (Etempvar 8%positive type_int32s)type_int32s.
Definition tensor_source_demo_cell := memory_pointer_lvalue 9%positive tensor_source_demo_index.
Definition tensor_source_demo_rhs := Ebinop Oadd tensor_source_demo_cell(Etempvar 5%positive type_int32s)type_int32s.
Definition tensor_source_demo_code := Sassign tensor_source_demo_cell tensor_source_demo_rhs.
Definition tensor_source_demo_access : tensor_source_access tensor_source_demo_dimensions tensor_source_demo_layout.
Proof.
  refine(@TensorSourceAccess tensor_source_demo_dimensions tensor_source_demo_layout tensor_source_demo_coordinates
    [([1;0;0;0;0],0);([0;1;0;0;0],0);([0;0;1;0;0],0)]tensor_source_demo_index _ _).
  - repeat constructor; reflexivity.
  - reflexivity.
Defined.
Definition tensor_source_demo_value := AddValue(LoadedValue 0)(ParameterValue 4).
Definition tensor_source_demo_operation : tensor_source_operation tensor_source_demo_dimensions tensor_source_demo_layout
    9%positive 20%positive tensor_source_demo_code.
Proof.
  refine(@TensorSourceOperation tensor_source_demo_dimensions tensor_source_demo_layout 9%positive 20%positive
    tensor_source_demo_code tensor_source_demo_access[tensor_source_demo_access]tensor_source_demo_value tensor_source_demo_rhs _ _ _);
    reflexivity.
Defined.
Definition tensor_source_demo_check code :=
  @check_tensor_source_operation tensor_source_demo_dimensions tensor_source_demo_layout 9%positive 20%positive code
    tensor_source_demo_access[tensor_source_demo_access]tensor_source_demo_value.
Definition tensor_source_demo_recognized code := match tensor_source_demo_check code with Some _=>true|None=>false end.
Definition tensor_source_demo_described coordinates := match
  describe_tensor_source_access tensor_source_demo_dimensions tensor_source_demo_layout coordinates with Some _=>true|None=>false end.
Definition tensor_source_demo_loop := memory_scalar_rectangle 0 3 2[tensor_source_instruction tensor_source_demo_operation].

Example tensor_source_demo_horner_recognized : tensor_source_demo_recognized tensor_source_demo_code=true.
Proof. vm_compute; reflexivity. Qed.
Example tensor_source_demo_changed_rhs_refused :
  tensor_source_demo_recognized(Sassign tensor_source_demo_cell(Etempvar 5%positive type_int32s))=false.
Proof. vm_compute; reflexivity. Qed.
Example tensor_source_demo_wrong_rank_refused :
  @describe_tensor_source_access tensor_source_demo_dimensions tensor_source_demo_layout
    [MemorySourceTemp 6%positive;MemorySourceTemp 7%positive]=None.
Proof. vm_compute; reflexivity. Qed.
Example tensor_source_demo_unknown_coordinate_refused :
  @describe_tensor_source_access tensor_source_demo_dimensions tensor_source_demo_layout
    [MemorySourceTemp 6%positive;MemorySourceTemp 7%positive;MemorySourceTemp 99%positive]=None.
Proof. vm_compute; reflexivity. Qed.
Example tensor_source_demo_unused_read_refused :
  @check_tensor_source_operation tensor_source_demo_dimensions tensor_source_demo_layout 9%positive 20%positive
    (Sassign tensor_source_demo_cell(Etempvar 5%positive type_int32s))tensor_source_demo_access[tensor_source_demo_access]
    (ParameterValue 4)=None.
Proof. vm_compute; reflexivity. Qed.
Example tensor_source_demo_box_accepted : tensor_source_operation_box tensor_source_demo_operation[3%nat;2%nat;5%nat][31;7][3;31;5]=true.
Proof. vm_compute; reflexivity. Qed.
Example tensor_source_demo_wide_columns_refused : tensor_source_operation_box tensor_source_demo_operation[3%nat;32%nat;5%nat][31;7][3;31;5]=false.
Proof. vm_compute; reflexivity. Qed.
Example tensor_source_demo_negative_coefficient_accepted :
  tensor_coordinate_box_check[(0,3);(0,2);(0,5)][3;31;5]
    [([-1;0;0],2);([0;1;0],0);([0;0;1],0)]=true.
Proof. vm_compute; reflexivity. Qed.
Example tensor_source_demo_negative_coordinate_refused :
  tensor_coordinate_box_check[(0,3);(0,2);(0,5)][3;31;5]
    [([-1;0;0],1);([0;1;0],0);([0;0;1],0)]=false.
Proof. vm_compute; reflexivity. Qed.

(** Bounds in this adapter are real source temporaries.  A frontend literal
    bound requires the existing constant-bound transport adapter separately. *)
Definition tensor_source_demo_inner := MemorySourceAxis 8%positive 4%positive tensor_source_demo_code(MemorySourceLeaf tensor_source_demo_code).
Definition tensor_source_demo_middle := MemorySourceAxis 7%positive 3%positive
  (Ssequence(rectangle_reset 8%positive)(memory_nest_source tensor_source_demo_inner))tensor_source_demo_inner.
Definition tensor_source_demo_nest := MemorySourceAxis 6%positive 1%positive
  (Ssequence(rectangle_reset 7%positive)(memory_nest_source tensor_source_demo_middle))tensor_source_demo_middle.
Example tensor_source_demo_nest_shapes : memory_nest_shapes tensor_source_demo_nest.
Proof. repeat split; reflexivity. Qed.
Definition tensor_source_demo_guard := tensor_source_layout_guard tensor_source_demo_dimensions tensor_source_demo_nest 32.
Definition tensor_source_demo_empty_temps := PTree.set 6%positive(Vint Int.zero)
  (PTree.set 1%positive(Vint Int.zero)(PTree.empty val)).

Example tensor_source_demo_empty_has_no_stride : tensor_source_demo_empty_temps!2%positive=None /\ tensor_source_demo_empty_temps!5%positive=None.
Proof. split; reflexivity. Qed.
Theorem tensor_source_demo_empty_guard_falls_back ge locals memory :
  decision_run(Entry ge locals tensor_source_demo_empty_temps memory)tensor_source_demo_guard false.
Proof.
  unfold tensor_source_demo_guard,tensor_source_layout_guard.
  apply decision_bind_run with(b:=true).
  - apply register_tree_run; exists Int.zero; reflexivity.
  - change(decision_run(Entry ge locals tensor_source_demo_empty_temps memory)
      (decision_bind(register_range_tree 1%positive 32)
        (memory_recursive_bounds_tree 32[3%positive;4%positive](tensor_backend_guard tensor_source_demo_dimensions))(Decision false))false).
    apply decision_bind_run with(b:=false).
    + apply register_range_tree_run; exists Int.zero; reflexivity.
    + constructor.
Qed.

Print Assumptions tensor_source_demo_horner_recognized.
Print Assumptions tensor_source_demo_changed_rhs_refused.
Print Assumptions tensor_source_demo_wrong_rank_refused.
Print Assumptions tensor_source_demo_unknown_coordinate_refused.
Print Assumptions tensor_source_demo_unused_read_refused.
Print Assumptions tensor_source_demo_box_accepted.
Print Assumptions tensor_source_demo_wide_columns_refused.
Print Assumptions tensor_source_demo_negative_coefficient_accepted.
Print Assumptions tensor_source_demo_negative_coordinate_refused.
Print Assumptions tensor_source_demo_nest_shapes.
Print Assumptions tensor_source_demo_empty_has_no_stride.
Print Assumptions tensor_source_demo_empty_guard_falls_back.
