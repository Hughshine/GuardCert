From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightPureExpr ClightRectangularStore ClightCountedLoop CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDynamicTensorLayout
  GuardMemoryBufferOffsets GuardMemoryPointerAccess GuardMemoryArrayBackend.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition tensor_operand ge locals temps memory code value :=
  typeof code=type_int32s /\ pure_scalar code /\
  eval_expr ge locals temps memory code(Vint(Int.repr value)).
Lemma tensor_operands_pure ge locals temps memory codes values :
  Forall2(tensor_operand ge locals temps memory)codes values -> Forall pure_scalar codes.
Proof.
  intro WORDS; induction WORDS.
  - constructor.
  - constructor; [exact(proj1(proj2 H))|exact IHWORDS].
Qed.
Definition tensor_product first second := Ebinop Omul first second type_int32s.
Lemma tensor_product_evaluation ge locals temps memory first second x y :
  typeof first=type_int32s -> typeof second=type_int32s ->
  eval_expr ge locals temps memory first(Vint(Int.repr x)) ->
  eval_expr ge locals temps memory second(Vint(Int.repr y)) ->
  eval_expr ge locals temps memory(tensor_product first second)(Vint(Int.repr(x*y))).
Proof.
  intros FIRST SECOND X Y; eapply eval_Ebinop; [exact X|exact Y|].
  rewrite FIRST,SECOND; change(Some(Vint(Int.mul(Int.repr x)(Int.repr y)))=
    Some(Vint(Int.repr(x*y)))); rewrite rect_integer_multiply; reflexivity.
Qed.

Fixpoint tensor_volume_expression dimensions :=
  match dimensions with
  | [] => rect_constant 1
  | dimension::rest => tensor_product dimension(tensor_volume_expression rest) end.
Fixpoint tensor_index_expression dimensions coordinates : option expr :=
  match dimensions,coordinates with
  | [],[] => Some(rect_constant 0)
  | _::rest,coordinate::tail =>
      match tensor_index_expression rest tail with
      | Some suffix => Some(operand_sum(tensor_product coordinate(tensor_volume_expression rest))suffix)
      | None => None end
  | _,_ => None end.

Lemma tensor_volume_expression_type dimensions : typeof(tensor_volume_expression dimensions)=type_int32s.
Proof. destruct dimensions; reflexivity. Qed.
Lemma tensor_volume_expression_pure dimensions :
  Forall pure_scalar dimensions -> pure_scalar(tensor_volume_expression dimensions).
Proof.
  intro PURE; induction PURE; cbn [tensor_volume_expression tensor_product]; repeat constructor; assumption.
Qed.
Theorem tensor_volume_expression_evaluation ge locals temps memory codes dimensions :
  Forall2(tensor_operand ge locals temps memory)codes dimensions ->
  eval_expr ge locals temps memory(tensor_volume_expression codes)(Vint(Int.repr(tensor_volume dimensions))).
Proof.
  intro WORDS; induction WORDS as [|code dimension codes dimensions [TYPE [PURE EVAL]] REST IH];
    cbn [tensor_volume_expression tensor_volume].
  - apply rect_constant_evaluation.
  - apply tensor_product_evaluation; [exact TYPE|apply tensor_volume_expression_type|exact EVAL|exact IH].
Qed.
Lemma tensor_index_expression_type dimensions coordinates code :
  tensor_index_expression dimensions coordinates=Some code -> typeof code=type_int32s.
Proof.
  destruct dimensions,coordinates; cbn; try discriminate.
  - intro SAME; inversion SAME; reflexivity.
  - destruct(tensor_index_expression dimensions coordinates); intro SAME; inversion SAME; reflexivity.
Qed.
Lemma tensor_index_expression_pure dimensions coordinates code :
  Forall pure_scalar dimensions -> Forall pure_scalar coordinates ->
  tensor_index_expression dimensions coordinates=Some code -> pure_scalar code.
Proof.
  revert coordinates code; induction dimensions as [|dimension rest IH]; intros [|coordinate tail] code DS CS CODE;
    cbn in CODE; try discriminate.
  - inversion CODE; constructor.
  - inversion DS; inversion CS; subst.
    destruct(tensor_index_expression rest tail) as [suffix|] eqn:SUFFIX; [|discriminate].
    inversion CODE; subst code; unfold operand_sum,tensor_product; constructor.
    + constructor; [assumption|apply tensor_volume_expression_pure; assumption].
    + eapply IH; eassumption.
Qed.

Theorem tensor_index_expression_evaluation ge locals temps memory dimension_codes coordinate_codes dimensions coordinates code offset :
  Forall2(tensor_operand ge locals temps memory)dimension_codes dimensions ->
  Forall2(tensor_operand ge locals temps memory)coordinate_codes coordinates ->
  tensor_index_expression dimension_codes coordinate_codes=Some code ->
  tensor_index dimensions coordinates=Some offset ->
  eval_expr ge locals temps memory code(Vint(Int.repr offset)).
Proof.
  intro DS; revert coordinate_codes coordinates code offset; induction DS as
    [|dimension_code dimension dimension_codes dimensions DIM DS IH];
    intros coordinate_codes coordinates code offset CS CODE INDEX.
  - inversion CS; subst; cbn in INDEX,CODE; try discriminate.
    inversion INDEX; inversion CODE; subst; constructor.
  - inversion CS as [|coordinate_code coordinate tail coordinates' COORD REST]; subst; cbn in INDEX,CODE; try discriminate.
    destruct((0 <=? coordinate)&&(coordinate <? dimension)); [|discriminate].
    destruct(tensor_index dimensions coordinates') as [suffix|] eqn:SUFFIX; [|discriminate].
    destruct(tensor_index_expression dimension_codes tail) as [suffix_code|] eqn:SUFFIX_CODE; [|discriminate].
    inversion INDEX; inversion CODE; subst code offset.
    apply operand_sum_evaluation.
    + reflexivity.
    + eapply tensor_index_expression_type; exact SUFFIX_CODE.
    + apply tensor_product_evaluation; [exact(proj1 COORD)|apply tensor_volume_expression_type|exact(proj2(proj2 COORD))|].
      apply tensor_volume_expression_evaluation; exact DS.
    + eapply IH; eassumption.
Qed.

Lemma tensor_pointer_location_at array block base dimensions coordinates offset :
  tensor_index dimensions coordinates=Some offset ->
  tensor_pointer_locations array block base dimensions {|arr_id:=array;arr_index:=coordinates|}=
    Some(MemoryLocation Mint32 block(memory_pointer_buffer_offset base offset)).
Proof.
  intro INDEX; unfold tensor_pointer_locations; cbn [arr_id arr_index]; rewrite Pos.eqb_refl,INDEX; reflexivity.
Qed.

Theorem tensor_pointer_lvalue_evaluation ge locals temps memory pointer block base
    dimension_codes coordinate_codes dimensions coordinates code offset :
  temps ! pointer=Some(Vptr block base) ->
  Forall2(tensor_operand ge locals temps memory)dimension_codes dimensions ->
  Forall2(tensor_operand ge locals temps memory)coordinate_codes coordinates ->
  tensor_index_expression dimension_codes coordinate_codes=Some code ->
  tensor_index dimensions coordinates=Some offset -> tensor_layout_flag dimensions=true ->
  eval_lvalue ge locals temps memory(memory_pointer_lvalue pointer code)
    block(Ptrofs.add base(Ptrofs.repr(4*offset)))Full.
Proof.
  intros POINTER DS CS CODE INDEX LAYOUT; eapply memory_pointer_lvalue_evaluation; [exact POINTER| | |].
  - eapply tensor_index_expression_type; exact CODE.
  - exact(@tensor_index_expression_evaluation ge locals temps memory
      dimension_codes coordinate_codes dimensions coordinates code offset DS CS CODE INDEX).
  - pose proof(@tensor_index_bounds dimensions coordinates offset INDEX).
    pose proof(@tensor_layout_flag_sound dimensions LAYOUT); unfold signed_range;
      pose proof Int.min_signed_neg; lia.
Qed.

Theorem tensor_pointer_lvalue_inverse ge locals temps memory pointer
    dimension_codes coordinate_codes dimensions coordinates code offset block address field :
  Forall2(tensor_operand ge locals temps memory)dimension_codes dimensions ->
  Forall2(tensor_operand ge locals temps memory)coordinate_codes coordinates ->
  tensor_index_expression dimension_codes coordinate_codes=Some code ->
  tensor_index dimensions coordinates=Some offset -> tensor_layout_flag dimensions=true ->
  eval_lvalue ge locals temps memory(memory_pointer_lvalue pointer code)block address field ->
  exists base,temps ! pointer=Some(Vptr block base) /\
    address=Ptrofs.add base(Ptrofs.repr(4*offset)) /\ field=Full.
Proof.
  intros DS CS CODE INDEX LAYOUT RUN; eapply memory_pointer_lvalue_inverse.
  - eapply tensor_index_expression_type; exact CODE.
  - eapply tensor_index_expression_pure; [| |exact CODE].
    + eapply tensor_operands_pure; exact DS.
    + eapply tensor_operands_pure; exact CS.
  - exact(@tensor_index_expression_evaluation ge locals temps memory
      dimension_codes coordinate_codes dimensions coordinates code offset DS CS CODE INDEX).
  - pose proof(@tensor_index_bounds dimensions coordinates offset INDEX).
    pose proof(@tensor_layout_flag_sound dimensions LAYOUT); unfold signed_range;
      pose proof Int.min_signed_neg; lia.
  - exact RUN.
Qed.

Theorem tensor_pointer_load_evaluation ge locals temps memory pointer block base
    dimension_codes coordinate_codes dimensions coordinates code offset value :
  temps ! pointer=Some(Vptr block base) ->
  Forall2(tensor_operand ge locals temps memory)dimension_codes dimensions ->
  Forall2(tensor_operand ge locals temps memory)coordinate_codes coordinates ->
  tensor_index_expression dimension_codes coordinate_codes=Some code ->
  tensor_index dimensions coordinates=Some offset -> tensor_layout_flag dimensions=true ->
  Mem.load Mint32 memory block(memory_pointer_buffer_offset base offset)=Some value ->
  eval_expr ge locals temps memory(memory_pointer_lvalue pointer code)value.
Proof.
  intros POINTER DS CS CODE INDEX LAYOUT LOAD; eapply eval_Elvalue.
  - exact(@tensor_pointer_lvalue_evaluation ge locals temps memory pointer block base
      dimension_codes coordinate_codes dimensions coordinates code offset POINTER DS CS CODE INDEX LAYOUT).
  - apply deref_loc_value with(chunk:=Mint32); [reflexivity|].
    cbn [Mem.loadv]; rewrite memory_pointer_buffer_address.
    pose proof(@memory_pointer_load_end memory block base offset value LOAD)as END.
    destruct(zle(memory_pointer_buffer_offset base offset+size_chunk Mint32)Ptrofs.modulus); [exact LOAD|lia].
Qed.

Theorem tensor_pointer_store_execution fe ge locals temps memory pointer block base
    dimension_codes coordinate_codes dimensions coordinates code offset value_code value final :
  temps ! pointer=Some(Vptr block base) ->
  Forall2(tensor_operand ge locals temps memory)dimension_codes dimensions ->
  Forall2(tensor_operand ge locals temps memory)coordinate_codes coordinates ->
  tensor_index_expression dimension_codes coordinate_codes=Some code ->
  tensor_index dimensions coordinates=Some offset -> tensor_layout_flag dimensions=true ->
  typeof value_code=type_int32s -> eval_expr ge locals temps memory value_code(Vint value) ->
  Mem.store Mint32 memory block(memory_pointer_buffer_offset base offset)(Vint value)=Some final ->
  exec_stmt fe ge locals temps memory(Sassign(memory_pointer_lvalue pointer code)value_code)E0 temps final Out_normal.
Proof.
  intros POINTER DS CS CODE INDEX LAYOUT TYPE VALUE STORE.
  eapply exec_Sassign with(loc:=block)(ofs:=Ptrofs.add base(Ptrofs.repr(4*offset)))(bf:=Full)
    (v:=Vint value)(v2:=Vint value).
  - exact(@tensor_pointer_lvalue_evaluation ge locals temps memory pointer block base
      dimension_codes coordinate_codes dimensions coordinates code offset POINTER DS CS CODE INDEX LAYOUT).
  - exact VALUE.
  - rewrite TYPE; reflexivity.
  - apply assign_loc_value with(chunk:=Mint32); [reflexivity|].
    cbn [Mem.storev]; rewrite memory_pointer_buffer_address.
    pose proof(@memory_pointer_store_end memory final block base offset(Vint value)STORE)as END.
    destruct(zle(memory_pointer_buffer_offset base offset+size_chunk Mint32)Ptrofs.modulus); [exact STORE|lia].
Qed.

Print Assumptions tensor_product_evaluation.
Print Assumptions tensor_volume_expression_evaluation.
Print Assumptions tensor_index_expression_evaluation.
Print Assumptions tensor_pointer_location_at.
Print Assumptions tensor_pointer_lvalue_evaluation.
Print Assumptions tensor_pointer_lvalue_inverse.
Print Assumptions tensor_pointer_load_evaluation.
Print Assumptions tensor_pointer_store_execution.
