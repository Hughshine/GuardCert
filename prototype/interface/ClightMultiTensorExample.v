From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightStraightLine ClightFiniteRegion.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryPointerAccess
  GuardMemoryAffineSourceExpressions GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend
  GuardMemoryTensorSource GuardMemoryMultiTensorBackend GuardMemoryMultiTensorSource
  GuardMemoryMultiTensorSequence GuardMemoryNaryLoops GuardMemoryScalarLoops.
Import ListNotations.
Local Open Scope Z_scope.

(** Two actual source assignments, with an intra-point flow dependence:
    a[q] = b[q] + alpha; b[q] = a[q] + alpha.
    Both the Horner index and source AST are independent checker inputs. *)
Definition multi_tensor_demo_dimensions :=
  [TensorDimensionTemp 1%positive;TensorDimensionTemp 2%positive;TensorDimensionConstant 5].
Definition multi_tensor_demo_source_layout := [6%positive;7%positive;8%positive;2%positive;5%positive].
Definition multi_tensor_demo_layout := [1%positive;3%positive;4%positive;2%positive;5%positive].
Definition multi_tensor_demo_coordinates :=
  [MemorySourceTemp 6%positive;MemorySourceTemp 7%positive;MemorySourceTemp 8%positive].
Definition multi_tensor_demo_pointers := [9%positive;10%positive].
Definition multi_tensor_demo_live := [6%positive;7%positive;8%positive].
Definition multi_tensor_demo_pool :=
  [(101%positive,102%positive);(103%positive,104%positive);(105%positive,106%positive);
   (107%positive,108%positive);(109%positive,110%positive);(111%positive,112%positive)].
Definition multi_tensor_demo_index := Ebinop Oadd
  (Ebinop Omul
    (Ebinop Oadd(Ebinop Omul(Etempvar 6%positive type_int32s)(Etempvar 2%positive type_int32s)type_int32s)
      (Etempvar 7%positive type_int32s)type_int32s)
    (Econst_int(Int.repr 5)type_int32s)type_int32s)
  (Etempvar 8%positive type_int32s)type_int32s.
Definition multi_tensor_demo_store write read :=
  Sassign(memory_pointer_lvalue write multi_tensor_demo_index)
    (Ebinop Oadd(memory_pointer_lvalue read multi_tensor_demo_index)(Etempvar 5%positive type_int32s)type_int32s).
Definition multi_tensor_demo_body := Ssequence
  (multi_tensor_demo_store 9%positive 10%positive)(multi_tensor_demo_store 10%positive 9%positive).
Definition multi_tensor_demo_value := AddValue(LoadedValue 0)(ParameterValue 4).

Definition multi_tensor_demo_step write read code :=
  match describe_tensor_source_access multi_tensor_demo_dimensions multi_tensor_demo_source_layout
      multi_tensor_demo_coordinates with
  | Some access=>@check_multi_tensor_source_statement multi_tensor_demo_dimensions multi_tensor_demo_source_layout
      code(write,access)[(read,access)]multi_tensor_demo_value
  | None=>None end.
Definition multi_tensor_demo_describe body :=
  match flatten_region body with
  | [first;second]=>
    match multi_tensor_demo_step 9%positive 10%positive first,multi_tensor_demo_step 10%positive 9%positive second with
    | Some one,Some two=>Some[one;two] | _,_=>None end
  | _=>None end.
Definition multi_tensor_demo_instructions body :=
  match multi_tensor_demo_describe body with Some items=>Some(map mt_instruction items)|None=>None end.
Definition multi_tensor_demo_source instructions := memory_scalar_rectangle 0 3 2 instructions.

Lemma multi_tensor_demo_step_exact write read code item :
  multi_tensor_demo_step write read code=Some item -> mt_statement item=code.
Proof.
  unfold multi_tensor_demo_step; destruct(describe_tensor_source_access _ _ _)as [access|]; [|discriminate].
  unfold check_multi_tensor_source_statement; destruct(@check_multi_tensor_source_operation _ _ code _ _ _)as [operation|];
    intro RUN; inversion RUN; reflexivity.
Qed.
Theorem multi_tensor_demo_describe_sound body items :
  multi_tensor_demo_describe body=Some items -> flatten_region body=map mt_statement items.
Proof.
  unfold multi_tensor_demo_describe.
  destruct(flatten_region body)as [|first rest]eqn:BODY; [discriminate|].
  destruct rest as [|second rest]; [discriminate|]; destruct rest; [|discriminate].
  destruct(multi_tensor_demo_step 9%positive 10%positive first)as [one|]eqn:ONE; [|discriminate].
  destruct(multi_tensor_demo_step 10%positive 9%positive second)as [two|]eqn:TWO; [|discriminate].
  intro RUN; inversion RUN; subst items; cbn [map].
  rewrite(multi_tensor_demo_step_exact _ _ _ _ ONE),(multi_tensor_demo_step_exact _ _ _ _ TWO); reflexivity.
Qed.

(** The recognized body decodes its two stores in order, including the second
    read in the memory produced by the first store. No separation premise is
    used by source decoding. The candidate checker needs a separate condition. *)
Theorem multi_tensor_demo_body_execution body items fe ge locals valuation sizes temps memory after final :
  multi_tensor_demo_describe body=Some items ->
  tensor_layout_flag sizes=true -> tensor_dimension_view multi_tensor_demo_dimensions sizes temps ->
  (forall id,In id multi_tensor_demo_source_layout -> temps!id=Some(Vint(Int.repr(valuation id)))) ->
  Forall(fun item=>mt_available item(map valuation multi_tensor_demo_source_layout)sizes)items ->
  exec_stmt fe ge locals temps memory body E0 after final Out_normal ->
  memory_nary_sequence_point(map mt_instruction items)(map valuation multi_tensor_demo_source_layout)
    (RuntimeState(multi_tensor_locations temps sizes)memory)(RuntimeState(multi_tensor_locations temps sizes)final) /\ after=temps.
Proof.
  intro CHECK; exact(@multi_tensor_body_source_decode multi_tensor_demo_dimensions multi_tensor_demo_source_layout
    body items fe ge locals valuation sizes temps memory after final(multi_tensor_demo_describe_sound _ _ CHECK)).
Qed.

Definition multi_tensor_demo_recognized body := match multi_tensor_demo_describe body with Some _=>true|None=>false end.
Example multi_tensor_demo_sequence_recognized : multi_tensor_demo_recognized multi_tensor_demo_body=true.
Proof. vm_compute; reflexivity. Qed.
Example multi_tensor_demo_reversed_source_refused :
  multi_tensor_demo_recognized(Ssequence(multi_tensor_demo_store 10%positive 9%positive)(multi_tensor_demo_store 9%positive 10%positive))=false.
Proof. vm_compute; reflexivity. Qed.
Example multi_tensor_demo_changed_rhs_refused :
  multi_tensor_demo_recognized(Ssequence
    (Sassign(memory_pointer_lvalue 9%positive multi_tensor_demo_index)(Etempvar 5%positive type_int32s))
    (multi_tensor_demo_store 10%positive 9%positive))=false.
Proof. vm_compute; reflexivity. Qed.
Example multi_tensor_demo_missing_statement_refused :
  multi_tensor_demo_recognized(multi_tensor_demo_store 9%positive 10%positive)=false.
Proof. vm_compute; reflexivity. Qed.
Example multi_tensor_demo_administrative_skips_recognized :
  multi_tensor_demo_recognized(Ssequence Sskip(Ssequence multi_tensor_demo_body Sskip))=true.
Proof. vm_compute; reflexivity. Qed.
Example multi_tensor_demo_pointer_mismatch_refused :
  multi_tensor_demo_recognized(Ssequence(multi_tensor_demo_store 9%positive 11%positive)
    (multi_tensor_demo_store 10%positive 9%positive))=false.
Proof. vm_compute; reflexivity. Qed.
Example multi_tensor_demo_data_instruction_count :
  match multi_tensor_demo_instructions multi_tensor_demo_body with Some instructions=>length instructions|None=>0%nat end=2%nat.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions multi_tensor_demo_step_exact.
Print Assumptions multi_tensor_demo_describe_sound.
Print Assumptions multi_tensor_demo_body_execution.
Print Assumptions multi_tensor_demo_sequence_recognized.
Print Assumptions multi_tensor_demo_reversed_source_refused.
Print Assumptions multi_tensor_demo_changed_rhs_refused.
Print Assumptions multi_tensor_demo_missing_statement_refused.
Print Assumptions multi_tensor_demo_administrative_skips_recognized.
Print Assumptions multi_tensor_demo_pointer_mismatch_refused.
Print Assumptions multi_tensor_demo_data_instruction_count.
