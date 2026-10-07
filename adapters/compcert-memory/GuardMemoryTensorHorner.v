From Stdlib Require Import List Bool ZArith Lia Ring.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightPureExpr ClightRectangularStore ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryArrayBackend GuardMemoryPointerAccess
  GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorAccess GuardMemoryAffineSourceExpressions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Keep the source's Horner AST: ((i*ld)+j)*components+k.  The first
    dimension bounds i but is not read by the address expression. *)
Fixpoint tensor_horner_accumulate accumulator dimensions coordinates : option expr :=
  match dimensions,coordinates with
  | [],[] => Some accumulator
  | dimension::rest,coordinate::tail =>
      tensor_horner_accumulate(operand_sum(tensor_product accumulator dimension)coordinate)rest tail
  | _,_ => None end.
Definition tensor_horner_expression dimensions coordinates : option expr :=
  match dimensions,coordinates with
  | [],[] => Some(rect_constant 0)
  | _::rest,coordinate::tail => tensor_horner_accumulate coordinate rest tail
  | _,_ => None end.

Lemma tensor_horner_accumulate_type accumulator dimensions coordinates code :
  typeof accumulator=type_int32s -> tensor_horner_accumulate accumulator dimensions coordinates=Some code ->
  typeof code=type_int32s.
Proof.
  revert accumulator coordinates code; induction dimensions; intros accumulator [|coordinate tail] code TYPE CODE;
    cbn in CODE; try discriminate.
  - inversion CODE; subst; exact TYPE.
  - eapply IHdimensions with(accumulator:=operand_sum(tensor_product accumulator a)coordinate)(coordinates:=tail);
      [reflexivity|exact CODE].
Qed.
Lemma tensor_horner_expression_type dimensions coordinates code :
  Forall(fun coordinate=>typeof coordinate=type_int32s)coordinates ->
  tensor_horner_expression dimensions coordinates=Some code -> typeof code=type_int32s.
Proof.
  destruct dimensions,coordinates; cbn; try discriminate.
  - intros _ CODE; inversion CODE; subst; reflexivity.
  - intros TYPES CODE; inversion TYPES; subst; eapply tensor_horner_accumulate_type;
      [|exact CODE]; eassumption.
Qed.
Lemma tensor_horner_accumulate_pure accumulator dimensions coordinates code :
  pure_scalar accumulator -> Forall pure_scalar dimensions -> Forall pure_scalar coordinates ->
  tensor_horner_accumulate accumulator dimensions coordinates=Some code -> pure_scalar code.
Proof.
  revert accumulator coordinates code; induction dimensions; intros accumulator [|coordinate tail] code PURE DS CS CODE;
    cbn in CODE; try discriminate.
  - inversion CODE; subst; exact PURE.
  - inversion DS; inversion CS; subst;
      eapply IHdimensions with(accumulator:=operand_sum(tensor_product accumulator a)coordinate)(coordinates:=tail);
      [|eassumption|eassumption|exact CODE].
    unfold operand_sum,tensor_product; repeat constructor; assumption.
Qed.
Lemma tensor_horner_expression_pure dimensions coordinates code :
  Forall pure_scalar dimensions -> Forall pure_scalar coordinates ->
  tensor_horner_expression dimensions coordinates=Some code -> pure_scalar code.
Proof.
  destruct dimensions,coordinates; cbn; try discriminate.
  - intros _ _ CODE; inversion CODE; subst; constructor.
  - intros DS CS CODE; inversion DS; inversion CS; subst;
      eapply tensor_horner_accumulate_pure; [| | |exact CODE]; assumption.
Qed.

Lemma tensor_horner_accumulate_evaluation ge locals temps memory dimension_codes dimensions :
  Forall2(tensor_operand ge locals temps memory)dimension_codes dimensions ->
  forall coordinate_codes coordinates accumulator value code offset,
  Forall2(tensor_operand ge locals temps memory)coordinate_codes coordinates ->
  typeof accumulator=type_int32s -> eval_expr ge locals temps memory accumulator(Vint(Int.repr value)) ->
  tensor_horner_accumulate accumulator dimension_codes coordinate_codes=Some code ->
  tensor_index dimensions coordinates=Some offset ->
  eval_expr ge locals temps memory code(Vint(Int.repr(value*tensor_volume dimensions+offset))).
Proof.
  intro DS; induction DS as [|dimension_code dimension dimension_codes dimensions [DT [DP DE]] DS IH];
    intros coordinate_codes coordinates accumulator value code offset CS TYPE EVAL CODE INDEX.
  - inversion CS; subst; cbn in CODE,INDEX; try discriminate.
    inversion CODE; inversion INDEX; subst; cbn [tensor_volume]; replace(value*1+0)with value by ring; exact EVAL.
  - inversion CS as [|coordinate_code coordinate tail coordinates' [CT [CP CE]] CS']; subst;
      cbn in CODE,INDEX; try discriminate.
    destruct((0 <=? coordinate)&&(coordinate <? dimension)); [|discriminate].
    destruct(tensor_index dimensions coordinates')as [suffix|]eqn:SUFFIX; [|discriminate].
    inversion INDEX; subst offset; cbn [tensor_volume].
    replace(value*(dimension*tensor_volume dimensions)+(coordinate*tensor_volume dimensions+suffix))
      with((value*dimension+coordinate)*tensor_volume dimensions+suffix)by ring.
    eapply IH with(accumulator:=operand_sum(tensor_product accumulator dimension_code)coordinate_code);
      [exact CS'|reflexivity| |exact CODE|exact SUFFIX].
    apply operand_sum_evaluation; [reflexivity|exact CT| |exact CE].
    apply tensor_product_evaluation; assumption.
Qed.
Theorem tensor_horner_expression_evaluation ge locals temps memory dimension_codes coordinate_codes dimensions coordinates code offset :
  Forall2(tensor_operand ge locals temps memory)dimension_codes dimensions ->
  Forall2(tensor_operand ge locals temps memory)coordinate_codes coordinates ->
  tensor_horner_expression dimension_codes coordinate_codes=Some code -> tensor_index dimensions coordinates=Some offset ->
  eval_expr ge locals temps memory code(Vint(Int.repr offset)).
Proof.
  intros DS CS; destruct DS as [|dimension_code dimension dimension_codes dimensions DIM DS];
    inversion CS as [|coordinate_code coordinate tail coordinates' COORD CS']; subst; cbn; try discriminate.
  - intros CODE INDEX; inversion CODE; inversion INDEX; subst; constructor.
  - intros CODE INDEX; destruct((0 <=? coordinate)&&(coordinate <? dimension)); [|discriminate].
    destruct(tensor_index dimensions coordinates')as [suffix|]eqn:SUFFIX; [|discriminate].
    inversion INDEX; subst offset; eapply tensor_horner_accumulate_evaluation;
      [exact DS|exact CS'|exact(proj1 COORD)|exact(proj2(proj2 COORD))|exact CODE|exact SUFFIX].
Qed.

Theorem tensor_horner_lvalue_inverse ge locals temps memory pointer dimension_codes coordinate_codes dimensions coordinates
    code offset block address field :
  Forall2(tensor_operand ge locals temps memory)dimension_codes dimensions ->
  Forall2(tensor_operand ge locals temps memory)coordinate_codes coordinates ->
  tensor_horner_expression dimension_codes coordinate_codes=Some code -> tensor_index dimensions coordinates=Some offset ->
  tensor_layout_flag dimensions=true ->
  eval_lvalue ge locals temps memory(memory_pointer_lvalue pointer code)block address field ->
  exists base,temps!pointer=Some(Vptr block base) /\ address=Ptrofs.add base(Ptrofs.repr(4*offset)) /\ field=Full.
Proof.
  intros DS CS CODE INDEX LAYOUT RUN; eapply memory_pointer_lvalue_inverse.
  - eapply tensor_horner_expression_type; [|exact CODE].
    clear DS CODE INDEX LAYOUT RUN; induction CS.
    + constructor.
    + constructor; [exact(proj1 H)|exact IHCS].
  - eapply tensor_horner_expression_pure; [eapply tensor_operands_pure; exact DS|eapply tensor_operands_pure; exact CS|exact CODE].
  - exact(@tensor_horner_expression_evaluation ge locals temps memory _ _ _ _ code offset DS CS CODE INDEX).
  - pose proof(@tensor_index_bounds dimensions coordinates offset INDEX); pose proof(@tensor_layout_flag_sound dimensions LAYOUT).
    unfold signed_range; pose proof Int.min_signed_neg; lia.
  - exact RUN.
Qed.

Lemma tensor_horner_accumulate_words ge locals temps memory dimensions :
  forall coordinates accumulator code word,
  typeof accumulator=type_int32s -> Forall(fun code=>typeof code=type_int32s)dimensions ->
  Forall(fun code=>typeof code=type_int32s)coordinates ->
  tensor_horner_accumulate accumulator dimensions coordinates=Some code ->
  eval_expr ge locals temps memory code(Vint word) ->
  (exists value,eval_expr ge locals temps memory accumulator(Vint value)) /\
  Forall(fun code=>exists value,eval_expr ge locals temps memory code(Vint value))dimensions /\
  Forall(fun code=>exists value,eval_expr ge locals temps memory code(Vint value))coordinates.
Proof.
  induction dimensions as [|dimension dimensions IH]; intros [|coordinate coordinates] accumulator code word TYPE DS CS CODE RUN;
    cbn in CODE; try discriminate.
  - inversion CODE; subst; split; [exists word; exact RUN|split; constructor].
  - inversion DS as [|same rest DT DTS]; inversion CS as [|same' tail CT CTS]; subst.
    destruct(IH coordinates(operand_sum(tensor_product accumulator dimension)coordinate)code word
      eq_refl DTS CTS CODE RUN)as [[value VALUE][DW CW]].
    apply scalar_binary_inv in VALUE as [product [coord [PRODUCT [COORD SUM]]]].
    rewrite CT in SUM.
    change(sem_binary_operation ge Oadd product type_int32s coord type_int32s memory=Some(Vint value))in SUM.
    destruct(@memory_source_binary_words ge Oadd product coord memory value ltac:(auto)SUM)as [a [b [-> ->]]].
    apply scalar_binary_inv in PRODUCT as [acc [dim [ACC [DIM MUL]]]].
    rewrite TYPE,DT in MUL.
    destruct(@memory_source_binary_words ge Omul acc dim memory a ltac:(auto)MUL)as [x [y [-> ->]]].
    split; [exists x; exact ACC|split; constructor; eauto].
Qed.
Theorem tensor_horner_expression_words ge locals temps memory dimensions coordinates code word :
  Forall(fun code=>typeof code=type_int32s)dimensions -> Forall(fun code=>typeof code=type_int32s)coordinates ->
  tensor_horner_expression dimensions coordinates=Some code -> eval_expr ge locals temps memory code(Vint word) ->
  Forall(fun code=>exists value,eval_expr ge locals temps memory code(Vint value))(tl dimensions) /\
  Forall(fun code=>exists value,eval_expr ge locals temps memory code(Vint value))coordinates.
Proof.
  destruct dimensions as [|dimension dimensions],coordinates as [|coordinate coordinates];
    intros DS CS CODE RUN; cbn in CODE; try discriminate.
  - split; constructor.
  - inversion DS as [|same rest DT DTS]; inversion CS as [|same' tail CT CTS]; subst.
    destruct(@tensor_horner_accumulate_words ge locals temps memory dimensions coordinates coordinate code word CT DTS CTS CODE RUN)
      as [HEAD [DW CW]]; split; [exact DW|constructor; assumption].
Qed.

Print Assumptions tensor_horner_expression_type.
Print Assumptions tensor_horner_expression_pure.
Print Assumptions tensor_horner_expression_evaluation.
Print Assumptions tensor_horner_lvalue_inverse.
Print Assumptions tensor_horner_expression_words.
