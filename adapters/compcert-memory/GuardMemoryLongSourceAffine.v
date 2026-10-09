From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From polcert.lib Require Import Linalg.
From Guard Require Import ClightSyntaxEquality.
From GuardMemory Require Import GuardMemoryLongControl GuardMemoryDoubleLocations
  GuardMemoryDoubleAffineLong GuardMemoryAffineSourceExpressions GuardMemoryNaryAffineExpressions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Preserve the source's I64 expression tree and its signed I32 literal
    operands. Mathematical coefficients reuse the existing affine encoder.
    Modular repr correspondence is distinct from a no-wrap certificate. *)
Inductive long_source_constant :=
| LongSourceI32 (value : int)
| LongSourceI64 (value : int64).
Inductive long_source_operation := LongSourceAdd | LongSourceSub | LongSourceMul.
Inductive long_source_sum := LongSourceSum | LongSourceDifference.
Inductive long_source_affine :=
| LongSourceTemp (identifier : ident)
| LongSourceLiteral (value : int64)
| LongSourceCastI32 (value : int)
| LongSourceBinary (operation : long_source_sum) (first second : long_source_affine)
| LongSourceConstantBinary (operation : long_source_operation) (on_left : bool)
    (constant : long_source_constant) (child : long_source_affine).
Definition long_source_constant_code constant := match constant with
| LongSourceI32 value => Econst_int value memory_signed_int_type
| LongSourceI64 value => Econst_long value memory_long_type end.
Definition long_source_constant_value constant := match constant with
| LongSourceI32 value => Vint value | LongSourceI64 value => Vlong value end.
Definition long_source_constant_math constant := match constant with
| LongSourceI32 value => Int.signed value | LongSourceI64 value => Int64.signed value end.
Definition long_source_operation_code operation := match operation with
| LongSourceAdd => Oadd | LongSourceSub => Osub | LongSourceMul => Omul end.
Definition long_source_operation_math operation first second := match operation with
| LongSourceAdd => first+second | LongSourceSub => first-second | LongSourceMul => first*second end.
Definition long_source_constant_binary_code operation (on_left : bool) constant child :=
  if on_left then Ebinop (long_source_operation_code operation) (long_source_constant_code constant) child memory_long_type
  else Ebinop (long_source_operation_code operation) child (long_source_constant_code constant) memory_long_type.
Fixpoint long_source_affine_code expression := match expression with
| LongSourceTemp identifier => Etempvar identifier memory_long_type
| LongSourceLiteral value => Econst_long value memory_long_type
| LongSourceCastI32 value => Ecast (Econst_int value memory_signed_int_type) memory_long_type
| LongSourceBinary operation first second => Ebinop
    (match operation with LongSourceSum => Oadd | LongSourceDifference => Osub end)
    (long_source_affine_code first) (long_source_affine_code second) memory_long_type
| LongSourceConstantBinary operation on_left constant child =>
    long_source_constant_binary_code operation on_left constant (long_source_affine_code child) end.
Definition long_source_constant_binary_math operation on_left constant child :=
  let literal := MemorySourceConstant (long_source_constant_math constant) in
  match operation,on_left with
  | LongSourceAdd,true => MemorySourceAdd literal child
  | LongSourceAdd,false => MemorySourceAdd child literal
  | LongSourceSub,true => MemorySourceSub literal child
  | LongSourceSub,false => MemorySourceSub child literal
  | LongSourceMul,true => MemorySourceScaleLeft (long_source_constant_math constant) child
  | LongSourceMul,false => MemorySourceScale (long_source_constant_math constant) child end.
Fixpoint long_source_affine_math expression := match expression with
| LongSourceTemp identifier => MemorySourceTemp identifier
| LongSourceLiteral value => MemorySourceConstant (Int64.signed value)
| LongSourceCastI32 value => MemorySourceConstant (Int.signed value)
| LongSourceBinary operation first second => match operation with
    | LongSourceSum => MemorySourceAdd (long_source_affine_math first) (long_source_affine_math second)
    | LongSourceDifference => MemorySourceSub (long_source_affine_math first) (long_source_affine_math second) end
| LongSourceConstantBinary operation on_left constant child =>
    long_source_constant_binary_math operation on_left constant (long_source_affine_math child) end.
Lemma long_source_affine_type expression : typeof (long_source_affine_code expression)=memory_long_type.
Proof. destruct expression; cbn; try reflexivity; destruct on_left; reflexivity. Qed.
Lemma long_source_repr_sub first second :
  Int64.sub (Int64.repr first) (Int64.repr second)=Int64.repr (first-second).
Proof.
  unfold Int64.sub; apply Int64.eqm_samerepr,Int64.eqm_sub;
    apply Int64.eqm_sym,Int64.eqm_unsigned_repr.
Qed.
Lemma long_source_constant_execution ge locals temps memory constant :
  eval_expr ge locals temps memory (long_source_constant_code constant) (long_source_constant_value constant).
Proof. destruct constant; constructor. Qed.
Lemma long_source_constant_binary_sem ge memory operation (on_left : bool) constant value :
  (if on_left then sem_binary_operation ge (long_source_operation_code operation)
      (long_source_constant_value constant) (typeof (long_source_constant_code constant))
      (Vlong (Int64.repr value)) memory_long_type memory
   else sem_binary_operation ge (long_source_operation_code operation)
      (Vlong (Int64.repr value)) memory_long_type
      (long_source_constant_value constant) (typeof (long_source_constant_code constant)) memory)=
  Some (Vlong (Int64.repr (if on_left then long_source_operation_math operation (long_source_constant_math constant) value
    else long_source_operation_math operation value (long_source_constant_math constant)))).
Proof.
  destruct constant as [word|word].
  - destruct on_left,operation; cbv beta iota zeta delta [long_source_operation_code long_source_constant_value long_source_constant_code
      long_source_constant_math long_source_operation_math typeof sem_binary_operation sem_add sem_sub sem_mul
      classify_add classify_sub typeconv sem_binarith classify_binarith binarith_type sem_cast classify_cast cast_int_long
      memory_signed_int_type memory_long_type remove_attributes change_attributes Archi.ptr64];
      rewrite ?memory_long_repr_add,?long_source_repr_sub,?double_long_repr_mul; reflexivity.
  - destruct on_left,operation; cbv beta iota zeta delta [long_source_operation_code long_source_constant_value long_source_constant_code
      long_source_constant_math long_source_operation_math typeof sem_binary_operation sem_add sem_sub sem_mul
      classify_add classify_sub typeconv sem_binarith classify_binarith binarith_type sem_cast classify_cast cast_int_long
      memory_signed_int_type memory_long_type remove_attributes change_attributes Archi.ptr64];
      rewrite <- (Int64.repr_signed word) at 1;
      rewrite ?memory_long_repr_add,?long_source_repr_sub,?double_long_repr_mul; reflexivity.
Qed.
Lemma long_source_constant_binary_execution ge locals temps memory operation on_left constant child value :
  typeof child=memory_long_type -> eval_expr ge locals temps memory child (Vlong (Int64.repr value)) ->
  eval_expr ge locals temps memory (long_source_constant_binary_code operation on_left constant child)
    (Vlong (Int64.repr (if on_left then long_source_operation_math operation (long_source_constant_math constant) value
      else long_source_operation_math operation value (long_source_constant_math constant)))).
Proof.
  intros TYPE CHILD; unfold long_source_constant_binary_code; destruct on_left.
  - eapply eval_Ebinop; [apply long_source_constant_execution|exact CHILD|].
    rewrite TYPE; exact (@long_source_constant_binary_sem ge memory operation true constant value).
  - eapply eval_Ebinop; [exact CHILD|apply long_source_constant_execution|].
    rewrite TYPE; exact (@long_source_constant_binary_sem ge memory operation false constant value).
Qed.
Lemma long_source_constant_binary_math_value valuation operation on_left constant child :
  memory_source_affine_math valuation (long_source_constant_binary_math operation on_left constant child)=
    if on_left then long_source_operation_math operation (long_source_constant_math constant) (memory_source_affine_math valuation child)
    else long_source_operation_math operation (memory_source_affine_math valuation child) (long_source_constant_math constant).
Proof. destruct operation,on_left; reflexivity. Qed.
Lemma long_source_constant_binary_reads operation on_left constant child :
  memory_source_affine_reads (long_source_constant_binary_math operation on_left constant child)=memory_source_affine_reads child.
Proof. destruct operation,on_left; cbn; rewrite ?app_nil_r; reflexivity. Qed.
Theorem long_source_affine_execution expression valuation ge locals temps memory :
  (forall identifier, In identifier (memory_source_affine_reads (long_source_affine_math expression)) ->
    temps ! identifier=Some (Vlong (Int64.repr (valuation identifier)))) ->
  eval_expr ge locals temps memory (long_source_affine_code expression)
    (Vlong (Int64.repr (memory_source_affine_math valuation (long_source_affine_math expression)))).
Proof.
  induction expression; intro WORDS;
    cbn [long_source_affine_code long_source_affine_math memory_source_affine_math].
  - constructor; apply WORDS; cbn; auto.
  - rewrite Int64.repr_signed; constructor.
  - eapply eval_Ecast; [constructor|reflexivity].
  - destruct operation; cbn [memory_source_affine_math].
    + apply double_long_add_execution; [apply long_source_affine_type|apply long_source_affine_type| |].
      * apply IHexpression1; intros id MEMBER; apply WORDS,in_or_app; auto.
      * apply IHexpression2; intros id MEMBER; apply WORDS,in_or_app; auto.
    + eapply eval_Ebinop.
      * apply IHexpression1; intros id MEMBER; apply WORDS,in_or_app; auto.
      * apply IHexpression2; intros id MEMBER; apply WORDS,in_or_app; auto.
      * rewrite !long_source_affine_type;
          change (Some (Vlong (Int64.sub
            (Int64.repr (memory_source_affine_math valuation (long_source_affine_math expression1)))
            (Int64.repr (memory_source_affine_math valuation (long_source_affine_math expression2))))) =
            Some (Vlong (Int64.repr
              (memory_source_affine_math valuation (long_source_affine_math expression1)-
               memory_source_affine_math valuation (long_source_affine_math expression2)))));
          rewrite long_source_repr_sub; reflexivity.
  - rewrite long_source_constant_binary_math_value; apply long_source_constant_binary_execution;
      [apply long_source_affine_type|].
    apply IHexpression; intros id MEMBER; apply WORDS.
    cbn [long_source_affine_math]; rewrite long_source_constant_binary_reads; exact MEMBER.
Qed.

Definition propose_long_source_constant code := match code with
| Econst_int value _ => Some (LongSourceI32 value)
| Econst_long value _ => Some (LongSourceI64 value)
| _ => None end.
Definition propose_long_source_operation operation := match operation with
| Oadd => Some LongSourceAdd | Osub => Some LongSourceSub | Omul => Some LongSourceMul | _ => None end.
Fixpoint propose_long_source_affine code : option long_source_affine := match code with
| Etempvar identifier _ => Some (LongSourceTemp identifier)
| Econst_long value _ => Some (LongSourceLiteral value)
| Ecast (Econst_int value _) _ => Some (LongSourceCastI32 value)
| Ebinop operation first second _ =>
    match propose_long_source_operation operation with
    | Some op =>
      match propose_long_source_constant first,propose_long_source_affine second with
      | Some constant,Some child => Some (LongSourceConstantBinary op true constant child)
      | _,_ => match propose_long_source_affine first,propose_long_source_constant second with
        | Some child,Some constant => Some (LongSourceConstantBinary op false constant child)
        | _,_ => match op,propose_long_source_affine first,propose_long_source_affine second with
          | LongSourceAdd,Some a,Some b => Some (LongSourceBinary LongSourceSum a b)
          | LongSourceSub,Some a,Some b => Some (LongSourceBinary LongSourceDifference a b)
          | _,_,_ => None end end end
    | None => None end
| _ => None end.
Definition describe_long_source_affine source := match propose_long_source_affine source with
| Some expression => if expression_eq source (long_source_affine_code expression) then Some expression else None
| None => None end.
Lemma describe_long_source_affine_exact source expression :
  describe_long_source_affine source=Some expression -> source=long_source_affine_code expression.
Proof.
  unfold describe_long_source_affine; destruct (propose_long_source_affine source) as [proposed|]; try discriminate.
  destruct (expression_eq source (long_source_affine_code proposed)) as [EXACT|]; try discriminate.
  intro RESULT; inversion RESULT; subst proposed; exact EXACT.
Qed.
Definition decode_long_source_index layout source : option constraint :=
  match describe_long_source_affine source with
  | Some expression => memory_encode_nary_index layout (long_source_affine_math expression)
  | None => None end.
Theorem decoded_long_source_index_execution layout source term valuation ge locals temps memory :
  decode_long_source_index layout source=Some term ->
  (forall identifier, In identifier layout -> temps ! identifier=Some (Vlong (Int64.repr (valuation identifier)))) ->
  typeof source=memory_long_type /\ eval_expr ge locals temps memory source
    (Vlong (Int64.repr (memory_nary_index_value term (map valuation layout)))).
Proof.
  unfold decode_long_source_index; destruct (describe_long_source_affine source) as [expression|] eqn:DESCRIBE;
    try discriminate; intros ENCODE WORDS.
  rewrite (@describe_long_source_affine_exact source expression DESCRIBE); split; [apply long_source_affine_type|].
  rewrite <- (@memory_encode_nary_index_value (long_source_affine_math expression) layout term valuation ENCODE).
  apply long_source_affine_execution; intros identifier MEMBER; apply WORDS.
  eapply memory_encode_nary_index_reads; eassumption.
Qed.
Fixpoint decode_long_source_indices layout codes := match codes with
| [] => Some []
| code::rest => match decode_long_source_index layout code,decode_long_source_indices layout rest with
    | Some row,Some rows => Some (row::rows) | _,_ => None end end.
Theorem decoded_long_source_indices_execution layout codes rows valuation ge locals temps memory :
  decode_long_source_indices layout codes=Some rows ->
  (forall identifier, In identifier layout -> temps ! identifier=Some (Vlong (Int64.repr (valuation identifier)))) ->
  Forall2 (fun code value => typeof code=memory_long_type /\
    eval_expr ge locals temps memory code (Vlong (Int64.repr value))) codes (affine_product rows (map valuation layout)).
Proof.
  intro ENCODE; revert rows ENCODE; induction codes as [|code rest IH]; intros rows ENCODE WORDS;
    cbn [decode_long_source_indices] in ENCODE.
  - inversion ENCODE; constructor.
  - destruct (decode_long_source_index layout code) as [row|] eqn:ROW; try discriminate.
    destruct (decode_long_source_indices layout rest) as [tail|] eqn:TAIL; try discriminate.
    inversion ENCODE; subst rows; cbn [affine_product map]; constructor.
    + apply decoded_long_source_index_execution; assumption.
    + apply IH; [reflexivity|exact WORDS].
Qed.

Print Assumptions long_source_affine_execution.
Print Assumptions describe_long_source_affine_exact.
Print Assumptions decoded_long_source_index_execution.
Print Assumptions decoded_long_source_indices_execution.
