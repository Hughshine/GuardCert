From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values.
From Guard Require Import ClightCondition ClightPureExpr ClightNoWrap ClightRedundantSet.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryRecursiveSource GuardMemoryRecursiveGuard GuardMemoryTensorBoxExpressions
  GuardMemoryWindowParameterGuard GuardMemoryIntervalBox.
From GuardInterface Require Import ClightTensorBoxGuard ClightTensorCompleteGuard ClightTensorSourceExample ClightTensorSourceGuard.
Import ListNotations.
Local Open Scope Z_scope.

Definition tensor_box_demo_scalars := [2%positive;5%positive].
Definition tensor_box_demo_layout := tensor_coordinate_layout tensor_source_demo_dimensions tensor_source_demo_nest tensor_box_demo_scalars.
Definition tensor_box_demo_profile := [(1,33);(1,33);(1,6);(1,1000);(Int.min_signed,Int.max_signed+1);(1,33);(1,1000)].
Definition tensor_box_demo_accesses := tensor_operation_accesses tensor_source_demo_operation.
Definition tensor_box_demo_compile accesses := compile_tensor_box_guard tensor_box_demo_layout tensor_box_demo_profile
  (memory_nest_bounds tensor_source_demo_nest)tensor_box_demo_scalars tensor_source_demo_dimensions accesses.
Definition tensor_box_demo_tree := match tensor_box_demo_compile tensor_box_demo_accesses with Some tree=>tree|None=>Decision false end.
Definition tensor_box_demo_full_guard := tensor_complete_tree tensor_source_demo_dimensions tensor_source_demo_nest
  tensor_box_demo_scalars 32 tensor_box_demo_profile tensor_box_demo_tree.
Definition tensor_box_demo_parameters columns components stride alpha := [3;columns;components;stride;alpha;3;stride].
Definition tensor_box_demo_semantic_flag accesses columns components stride alpha :=
  let parameters:=tensor_box_demo_parameters columns components stride alpha in
  forallb(fun pair=>(fst(fst pair)<=? snd pair)&&(snd pair<?snd(fst pair)))
    (combine tensor_box_demo_profile parameters)&&
  match tensor_box_entry_test tensor_box_demo_layout(memory_nest_bounds tensor_source_demo_nest)tensor_box_demo_scalars
    tensor_source_demo_dimensions accesses with Some test=>L.eval_test parameters test|None=>false end.
Example tensor_box_demo_compiled : tensor_box_demo_compile tensor_box_demo_accesses=Some tensor_box_demo_tree.
Proof. vm_compute; reflexivity. Qed.
Example tensor_box_demo_intermediate_overflow_refused : tensor_box_demo_compile
  [[([2147483647;0;0;0;0],0);([0;1;0;0;0],0);([0;0;1;0;0],0)]]=None.
Proof. vm_compute; reflexivity. Qed.
Example tensor_box_demo_unknown_dimension_refused : compile_tensor_box_guard tensor_box_demo_layout tensor_box_demo_profile
  [1%positive;3%positive;4%positive]tensor_box_demo_scalars
  [GuardMemoryDynamicTensorBackend.TensorDimensionTemp 99%positive]tensor_box_demo_accesses=None.
Proof. vm_compute; reflexivity. Qed.
Example tensor_box_demo_negative_coefficients_compiled : match tensor_box_demo_compile
  [[([-1;0;0;0;0],2);([0;1;0;0;0],0);([0;0;1;0;0],0)]]with Some _=>true|None=>false end=true.
Proof. vm_compute; reflexivity. Qed.

Definition tensor_box_demo_temps columns components stride := PTree.set 6%positive(Vint Int.zero)
  (PTree.set 1%positive(Vint(Int.repr 3))(PTree.set 3%positive(Vint(Int.repr columns))
    (PTree.set 4%positive(Vint(Int.repr components))(PTree.set 2%positive(Vint(Int.repr stride))
      (PTree.set 5%positive(Vint(Int.repr 7))(PTree.empty val)))))).

Lemma tensor_box_demo_actual_coordinate_guard ge locals memory columns components stride
    (COLUMNS:0<Int.signed(Int.repr columns))(COMPONENTS:0<Int.signed(Int.repr components)) :
  decision_run(Entry ge locals(tensor_box_demo_temps columns components stride)memory)
    (tensor_box_checked_tree tensor_box_demo_profile tensor_box_demo_layout tensor_box_demo_tree)
    (tensor_box_checked_flag tensor_box_demo_profile tensor_box_demo_layout
      [1%positive;3%positive;4%positive]tensor_box_demo_scalars tensor_source_demo_dimensions tensor_box_demo_accesses
      (Entry ge locals(tensor_box_demo_temps columns components stride)memory)).
Proof.
  apply tensor_box_checked_exact with(axes:=[1%positive;3%positive;4%positive])(scalars:=tensor_box_demo_scalars)
    (dimensions:=tensor_source_demo_dimensions)(accesses:=tensor_box_demo_accesses);
    [exact tensor_box_demo_compiled| | |reflexivity].
  - repeat constructor; unfold register_domain,tensor_box_demo_temps; eexists; reflexivity.
  - change(Forall(fun identifier=>0<tensor_box_word_valuation(tensor_box_demo_temps columns components stride)identifier)
      [1%positive;3%positive;4%positive]).
    constructor; [vm_compute; reflexivity|constructor; [exact COLUMNS|constructor; [exact COMPONENTS|constructor]]].
Qed.

Example tensor_box_demo_coordinate_flag ge locals memory : tensor_box_checked_flag tensor_box_demo_profile tensor_box_demo_layout
  [1%positive;3%positive;4%positive]tensor_box_demo_scalars tensor_source_demo_dimensions tensor_box_demo_accesses
  (Entry ge locals(tensor_box_demo_temps 2 5 31)memory)=true.
Proof. vm_compute; reflexivity. Qed.
Theorem tensor_box_demo_actual_coordinate_accepts ge locals memory :
  decision_run(Entry ge locals(tensor_box_demo_temps 2 5 31)memory)
    (tensor_box_checked_tree tensor_box_demo_profile tensor_box_demo_layout tensor_box_demo_tree)true.
Proof. rewrite <-(@tensor_box_demo_coordinate_flag ge locals memory); apply tensor_box_demo_actual_coordinate_guard; vm_compute; reflexivity. Qed.
Theorem tensor_box_demo_actual_wide_columns_refuses ge locals memory :
  decision_run(Entry ge locals(tensor_box_demo_temps 32 5 31)memory)
    (tensor_box_checked_tree tensor_box_demo_profile tensor_box_demo_layout tensor_box_demo_tree)false.
Proof. pose proof(@tensor_box_demo_actual_coordinate_guard ge locals memory 32 5 31 ltac:(vm_compute; reflexivity)ltac:(vm_compute; reflexivity))as RUN; vm_compute in RUN; exact RUN. Qed.
Theorem tensor_box_demo_actual_components_refuses ge locals memory :
  decision_run(Entry ge locals(tensor_box_demo_temps 2 6 31)memory)
    (tensor_box_checked_tree tensor_box_demo_profile tensor_box_demo_layout tensor_box_demo_tree)false.
Proof. pose proof(@tensor_box_demo_actual_coordinate_guard ge locals memory 2 6 31 ltac:(vm_compute; reflexivity)ltac:(vm_compute; reflexivity))as RUN; vm_compute in RUN; exact RUN. Qed.
Theorem tensor_box_demo_actual_profile_refuses ge locals memory :
  decision_run(Entry ge locals(tensor_box_demo_temps 2 5 1001)memory)
    (tensor_box_checked_tree tensor_box_demo_profile tensor_box_demo_layout tensor_box_demo_tree)false.
Proof. pose proof(@tensor_box_demo_actual_coordinate_guard ge locals memory 2 5 1001 ltac:(vm_compute; reflexivity)ltac:(vm_compute; reflexivity))as RUN; vm_compute in RUN; exact RUN. Qed.
Theorem tensor_box_demo_empty_full_guard_refuses ge locals memory :
  decision_run(Entry ge locals tensor_source_demo_empty_temps memory)tensor_box_demo_full_guard false.
Proof.
  unfold tensor_box_demo_full_guard,tensor_complete_tree; apply decision_bind_run with(b:=false);
    [apply tensor_source_demo_empty_guard_falls_back|constructor].
Qed.
Print Assumptions tensor_box_demo_compiled.
Print Assumptions tensor_box_demo_intermediate_overflow_refused.
Print Assumptions tensor_box_demo_unknown_dimension_refused.
Print Assumptions tensor_box_demo_negative_coefficients_compiled.
Print Assumptions tensor_box_demo_actual_coordinate_accepts.
Print Assumptions tensor_box_demo_actual_wide_columns_refuses.
Print Assumptions tensor_box_demo_actual_components_refuses.
Print Assumptions tensor_box_demo_actual_profile_refuses.
Print Assumptions tensor_box_demo_empty_full_guard_refuses.
