From Stdlib Require Import List ZArith.
From compcert.lib Require Import Integers Floats.
From compcert.common Require Import Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightPureExpr ClightSyntaxEquality CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryDoubleValue GuardMemoryObservationDeterminism.
Import ListNotations.
Set Implicit Arguments.

Lemma double_binary_operation_exact cenv operation first second memory :
  sem_binary_operation cenv (double_c_operation operation)
    first memory_double_type second memory_double_type memory =
  double_compute operation first second.
Proof. destruct operation, first, second; reflexivity. Qed.

Lemma double_cast_exact memory input value :
  sem_cast input memory_double_type memory_double_type memory = Some value ->
  exists number, input = Vfloat number /\ value = Vfloat number.
Proof. destruct input; cbn; try discriminate; intro CAST; inversion CAST; subst; eauto. Qed.

Lemma double_receipts_types ge locals temps memory loads values :
  Forall2 (fun input value => typeof input = memory_double_type /\
    eval_expr ge locals temps memory input value) loads values ->
  Forall (fun input => typeof input = memory_double_type) loads.
Proof. intro RECEIPTS; induction RECEIPTS; constructor; [exact (proj1 H)|exact IHRECEIPTS]. Qed.

Lemma double_receipt_exists ge locals temps memory loads values index code :
  Forall2 (fun input value => typeof input = memory_double_type /\
    eval_expr ge locals temps memory input value) loads values ->
  nth_error loads index = Some code -> exists value,
  nth_error values index = Some value /\ eval_expr ge locals temps memory code value.
Proof.
  intro RECEIPTS; revert index code; induction RECEIPTS; intros index code CODE.
  - destruct index; discriminate CODE.
  - destruct index; cbn in CODE.
    + inversion CODE; subst; exists y; split; [reflexivity|exact (proj2 H)].
    + eapply IHRECEIPTS; exact CODE.
Qed.

Theorem double_value_source_decode ge locals temps memory loads values expression code value :
  Forall2 (fun input value => typeof input = memory_double_type /\
    eval_expr ge locals temps memory input value) loads values ->
  double_value_code loads expression = Some code ->
  eval_expr ge locals temps memory code value ->
  evaluate_double_value values expression = Some value.
Proof.
  intros RECEIPTS; pose proof (double_receipts_types RECEIPTS) as TYPES.
  revert code value; induction expression; intros code value CODE RUN;
    cbn [double_value_code] in CODE; cbn [evaluate_double_value].
  - inversion CODE; subst code; inversion RUN; subst; try reflexivity.
    match goal with H : eval_lvalue _ _ _ _ (Econst_float _ _) _ _ _ |- _ => inversion H end.
  - destruct (@double_receipt_exists ge locals temps memory loads values n code RECEIPTS CODE) as [actual [VALUE EVAL]].
    pose proof (memory_expression_unique EVAL RUN) as SAME; subst value; exact VALUE.
  - destruct (double_value_code loads expression1) as [first|] eqn:FIRST; try discriminate.
    destruct (double_value_code loads expression2) as [second|] eqn:SECOND; try discriminate.
    inversion CODE; subst code; apply scalar_binary_inv in RUN as [a [b [A [B OP]]]].
    rewrite (IHexpression1 _ _ eq_refl A), (IHexpression2 _ _ eq_refl B).
    rewrite (@double_value_code_type loads expression1 first TYPES FIRST),
      (@double_value_code_type loads expression2 second TYPES SECOND) in OP.
    rewrite double_binary_operation_exact in OP; exact OP.
  - destruct (double_value_code loads expression) as [child|] eqn:CHILD; try discriminate.
    inversion CODE; subst code; inversion RUN; subst.
    + match goal with EVAL : eval_expr _ _ _ _ child ?input,
      OP : sem_unary_operation Oneg ?input _ _ = _ |- _ =>
        rewrite (IHexpression _ _ eq_refl EVAL);
        rewrite (@double_value_code_type loads expression child TYPES CHILD) in OP;
        destruct input; cbn in OP; try discriminate; exact OP end.
    + match goal with H : eval_lvalue _ _ _ _ (Eunop _ _ _) _ _ _ |- _ => inversion H end.
Qed.

Fixpoint double_load_index code loads : option nat :=
  match loads with
  | [] => None
  | input :: rest => if expression_eq code input then Some 0%nat
      else match double_load_index code rest with Some n => Some (S n) | None => None end
  end.
Lemma double_load_index_correct code loads index :
  double_load_index code loads = Some index -> nth_error loads index = Some code.
Proof.
  revert index; induction loads as [|input rest IH]; intros index FOUND; cbn in FOUND; try discriminate.
  destruct (expression_eq code input) as [SAME|]; [subst; inversion FOUND; reflexivity|].
  destruct (double_load_index code rest) as [position|] eqn:POSITION; try discriminate.
  inversion FOUND; subst; cbn; eapply IH; reflexivity.
Qed.
Definition decode_double_operation operation : option double_operation :=
  match operation with Oadd => Some DoubleAdd | Osub => Some DoubleSub |
    Omul => Some DoubleMul | Odiv => Some DoubleDiv | _ => None end.
Lemma decode_double_operation_correct operation decoded :
  decode_double_operation operation = Some decoded -> double_c_operation decoded = operation.
Proof. destruct operation; cbn; try discriminate; intro RESULT; inversion RESULT; reflexivity. Qed.

Fixpoint decode_double_expression loads code : option double_value_expression :=
  if type_eq (typeof code) memory_double_type then
    match double_load_index code loads with
    | Some index => Some (DoubleRead index)
    | None => match code with
      | Econst_float value _ => Some (DoubleBits (Int64.unsigned (Float.to_bits value)))
      | Ebinop operation first second _ =>
          match decode_double_operation operation,
            decode_double_expression loads first, decode_double_expression loads second with
          | Some op, Some a, Some b => Some (DoubleBinary op a b) | _, _, _ => None end
      | Eunop Oneg child _ => match decode_double_expression loads child with
          | Some decoded => Some (DoubleNegate decoded) | None => None end
      | _ => None end
    end
  else None.

Theorem decode_double_expression_code loads code expression :
  decode_double_expression loads code = Some expression ->
  double_value_code loads expression = Some code.
Proof.
  revert expression; induction code as
    [i ty|f ty|f ty|i ty|id ty|id ty|code IHcode ty|code IHcode ty|
     op code IHcode ty|op code1 IHcode1 code2 IHcode2 ty|code IHcode ty|
     code IHcode field ty|other_ty ty|other_ty ty]; intros expression DECODE; cbn [decode_double_expression] in DECODE;
    destruct (type_eq (typeof _) memory_double_type) as [TYPE|] in DECODE; try discriminate;
    destruct (double_load_index _ loads) as [index|] eqn:LOAD in DECODE;
    try (inversion DECODE; subst expression; cbn [double_value_code]; eapply double_load_index_correct; exact LOAD);
    try discriminate.
  - inversion DECODE; subst; cbn [double_value_code]; rewrite Int64.repr_unsigned, Float.of_to_bits.
    cbn in TYPE; subst; reflexivity.
  - destruct op; try discriminate; destruct (decode_double_expression loads code) as [child|] eqn:CHILD; try discriminate.
    inversion DECODE; subst; cbn [double_value_code]; rewrite (IHcode _ eq_refl); cbn in TYPE; subst; reflexivity.
  - destruct (decode_double_operation op) as [operation|] eqn:OP; try discriminate.
    destruct (decode_double_expression loads code1) as [first|] eqn:FIRST; try discriminate.
    destruct (decode_double_expression loads code2) as [second|] eqn:SECOND; try discriminate.
    inversion DECODE; subst; cbn [double_value_code]; rewrite (IHcode1 _ eq_refl), (IHcode2 _ eq_refl).
    rewrite (@decode_double_operation_correct op operation OP); cbn in TYPE; subst; reflexivity.
Qed.

Corollary decoded_double_source_execution ge locals temps memory loads values code expression value :
  Forall2 (fun input value => typeof input = memory_double_type /\
    eval_expr ge locals temps memory input value) loads values ->
  decode_double_expression loads code = Some expression ->
  (eval_expr ge locals temps memory code value <-> evaluate_double_value values expression = Some value).
Proof.
  intros RECEIPTS DECODE; pose proof (@decode_double_expression_code loads code expression DECODE) as CODE.
  split; [eapply double_value_source_decode; eauto|eapply double_value_code_execution; eauto].
Qed.

Print Assumptions double_value_source_decode.
Print Assumptions decode_double_expression_code.
Print Assumptions decoded_double_source_execution.
