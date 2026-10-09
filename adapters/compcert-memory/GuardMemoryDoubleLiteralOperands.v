From Stdlib Require Import List Bool.
From compcert.lib Require Import Integers Floats.
From compcert.common Require Import Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightPureExpr.
From GuardMemory Require Import GuardMemoryDoubleValue GuardMemoryDoubleSource
  GuardMemoryDoubleLocations GuardMemoryLongControl GuardMemoryDoubleAssignmentLiteral.
Set Implicit Arguments.

(** C promotes a literal operand before a floating operation. This conversion
    preserves each actual operation; integer arithmetic is never folded into
    floating arithmetic and the expression tree is never reassociated. *)
Definition double_promoting_types first second :=
  match first, second with
  | Tfloat F64 _, Tfloat F64 _
  | Tfloat F64 _, Tint I32 Signed _ | Tint I32 Signed _, Tfloat F64 _
  | Tfloat F64 _, Tlong Signed _ | Tlong Signed _, Tfloat F64 _ => true
  | _, _ => false end.

Definition promoted_double_binary operation first first_type second second_type memory :=
  match sem_cast first first_type memory_double_type memory,
        sem_cast second second_type memory_double_type memory with
  | Some a, Some b => double_compute operation a b | _, _ => None end.
Lemma double_promoting_binary_exact cenv operation first first_type second second_type memory :
  double_promoting_types first_type second_type=true ->
  sem_binary_operation cenv (double_c_operation operation)
    first first_type second second_type memory =
  promoted_double_binary operation first first_type second second_type memory.
Proof.
  destruct first_type,second_type; cbn [double_promoting_types]; try discriminate;
    repeat match goal with
    | size : intsize |- _ => destruct size
    | size : floatsize |- _ => destruct size
    | sign : signedness |- _ => destruct sign
    end; try discriminate; intro ACCEPT;
    destruct operation,first,second; reflexivity.
Qed.

Fixpoint normalize_double_literal_operands code : option expr :=
  match code with
  | Econst_int number ty => if type_eq ty memory_signed_int_type
      then Some (Econst_float (Float.of_int number) memory_double_type) else None
  | Econst_long number ty => if type_eq ty memory_long_type
      then Some (Econst_float (Float.of_long number) memory_double_type) else None
  | Ebinop operation first second ty =>
      if type_eq ty memory_double_type then
        if double_promoting_types (typeof first) (typeof second) then
          match decode_double_operation operation,
                normalize_double_literal_operands first, normalize_double_literal_operands second with
          | Some op, Some a, Some b => Some (Ebinop (double_c_operation op) a b memory_double_type)
          | _, _, _ => None end
        else None else None
  | Eunop Oneg child ty => if type_eq ty memory_double_type then
      if type_eq (typeof child) memory_double_type then
        match normalize_double_literal_operands child with
        | Some normalized => Some (Eunop Oneg normalized memory_double_type) | None => None end
      else None else None
  | _ => if type_eq (typeof code) memory_double_type then Some code else None
  end.

Lemma normalized_double_literal_operands_type code normalized :
  normalize_double_literal_operands code=Some normalized -> typeof normalized=memory_double_type.
Proof.
  destruct code; cbn [normalize_double_literal_operands];
    repeat match goal with
    | |- context [if ?test then _ else _] => destruct test
    | |- context [match ?value with _ => _ end] => destruct value
    end; try discriminate; intro NORMAL; inversion NORMAL; subst;
    cbn in *; auto.
Qed.

Theorem normalized_double_literal_operands_forward ge locals temps memory code normalized value result :
  normalize_double_literal_operands code=Some normalized ->
  eval_expr ge locals temps memory code value ->
  sem_cast value (typeof code) memory_double_type memory=Some result ->
  eval_expr ge locals temps memory normalized result.
Proof.
  revert normalized value result; induction code as
    [i ty|f ty|f ty|i ty|id ty|id ty|code IHcode ty|code IHcode ty|
     op code IHcode ty|op code1 IHcode1 code2 IHcode2 ty|code IHcode ty|
     code IHcode field ty|other_ty ty|other_ty ty]; intros normalized value result NORMAL RUN CAST;
    cbn [normalize_double_literal_operands typeof] in NORMAL;
    try solve [destruct (type_eq ty memory_double_type) as [TYPE|]; [|discriminate];
      inversion NORMAL; subst normalized; cbn [typeof] in CAST; rewrite TYPE in CAST;
      destruct (@double_cast_exact memory value result CAST) as [number [VALUE RESULT]];
      subst value result; exact RUN].
  - destruct (type_eq ty memory_signed_int_type); [subst ty|discriminate].
    inversion NORMAL; subst normalized.
    pose proof (@double_assignment_literal_cast ge locals temps memory
      (Econst_int i memory_signed_int_type) (Float.of_int i) value ltac:(cbn; destruct (type_eq _ _); congruence) RUN) as EXACT.
    rewrite EXACT in CAST; inversion CAST; subst; constructor.
  - destruct (type_eq ty memory_long_type); [subst ty|discriminate].
    inversion NORMAL; subst normalized.
    pose proof (@double_assignment_literal_cast ge locals temps memory
      (Econst_long i memory_long_type) (Float.of_long i) value ltac:(cbn; destruct (type_eq _ _); congruence) RUN) as EXACT.
    rewrite EXACT in CAST; inversion CAST; subst; constructor.
  - destruct op; try solve [destruct (type_eq ty memory_double_type) as [TYPE|]; [|discriminate];
      inversion NORMAL; subst normalized; rewrite TYPE in CAST;
      destruct (@double_cast_exact memory value result CAST) as [number [VALUE RESULT]];
      subst value result; exact RUN].
    destruct (type_eq ty memory_double_type); [subst ty|discriminate].
    destruct (type_eq (typeof code) memory_double_type) as [CHILD_TYPE|]; [|discriminate].
    destruct (normalize_double_literal_operands code) as [child|] eqn:CHILD; [|discriminate].
    inversion NORMAL; subst normalized.
    inversion RUN; subst.
    + rewrite CHILD_TYPE in H4.
      destruct v1; cbn in H4; try discriminate.
      inversion H4; subst value; cbn in CAST; inversion CAST; subst result.
      econstructor.
      * eapply IHcode; [reflexivity|exact H3|rewrite CHILD_TYPE; reflexivity].
      * rewrite (@normalized_double_literal_operands_type code child CHILD); reflexivity.
    + match goal with H : eval_lvalue _ _ _ _ (Eunop _ _ _) _ _ _ |- _ => inversion H end.
  - destruct (type_eq ty memory_double_type); [subst ty|discriminate].
    destruct (double_promoting_types (typeof code1) (typeof code2)) eqn:TYPES; [|discriminate].
    destruct (decode_double_operation op) as [operation|] eqn:OP; [|discriminate].
    destruct (normalize_double_literal_operands code1) as [first|] eqn:FIRST; [|discriminate].
    destruct (normalize_double_literal_operands code2) as [second|] eqn:SECOND; [|discriminate].
    inversion NORMAL; subst normalized; apply scalar_binary_inv in RUN as [a [b [A [B BINARY]]]].
    rewrite <- (@decode_double_operation_correct op operation OP) in BINARY.
    rewrite (@double_promoting_binary_exact (genv_cenv ge) operation a (typeof code1) b (typeof code2) memory TYPES) in BINARY.
    unfold promoted_double_binary in BINARY.
    destruct (sem_cast a (typeof code1) memory_double_type memory) as [av|] eqn:AV; [|discriminate].
    destruct (sem_cast b (typeof code2) memory_double_type memory) as [bv|] eqn:BV; [|discriminate].
    destruct av,bv; cbn [double_compute] in BINARY; try discriminate.
    destruct operation; inversion BINARY; subst value; cbn in CAST; inversion CAST; subst result;
      (eapply eval_Ebinop;
       [eapply IHcode1; [reflexivity|exact A|exact AV]
       |eapply IHcode2; [reflexivity|exact B|exact BV]
       |rewrite (@normalized_double_literal_operands_type code1 first FIRST),
         (@normalized_double_literal_operands_type code2 second SECOND); reflexivity]).
Qed.

Print Assumptions double_promoting_binary_exact.
Print Assumptions normalized_double_literal_operands_type.
Print Assumptions normalized_double_literal_operands_forward.
