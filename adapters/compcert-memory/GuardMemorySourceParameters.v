From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight Ctypes Cop.
From Guard Require Import ClightPureExpr ClightRectangularStore ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryFlatArrayBackend GuardMemorySourceValueInterface
  GuardMemoryNarySourceValues GuardMemoryPointerCompute GuardMemoryAffineSourceExpressions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_source_parameter_positions value : list nat :=
  match value with
  | ParameterValue index => [index]
  | AddValue first second | SubValue first second | MulValue first second =>
      memory_source_parameter_positions first++memory_source_parameter_positions second
  | _ => []
  end.
Definition memory_source_parameters_check required value :=
  forallb (fun index => existsb (Nat.eqb index) (memory_source_parameter_positions value)) required.
Lemma memory_source_parameters_check_sound required value : memory_source_parameters_check required value = true ->
  forall index, In index required -> In index (memory_source_parameter_positions value).
Proof.
  unfold memory_source_parameters_check; intros CHECK index MEMBER.
  apply forallb_forall with (x := index) in CHECK; [|exact MEMBER].
  apply existsb_exists in CHECK as [other [IN SAME]]; apply Nat.eqb_eq in SAME; subst; exact IN.
Qed.

Section PARAMETER_READS.
Variable ge : genv.
Variable locals : env.
Variable temps : temp_env.
Variable memory : mem.
Variable codes reads : list expr.
Hypothesis CODE_TYPES : Forall (fun code => typeof code = type_int32s) codes.
Hypothesis READ_TYPES : Forall (fun code => typeof code = type_int32s) reads.
Theorem memory_source_parameter_inverse value : forall code result,
  compile_flat_value codes reads value = Some code -> eval_expr ge locals temps memory code (Vint result) ->
  forall index, In index (memory_source_parameter_positions value) ->
  exists operand word, nth_error codes index = Some operand /\ eval_expr ge locals temps memory operand (Vint word).
Proof.
  induction value; intros code result COMPILE RUN index MEMBER;
    cbn [memory_source_parameter_positions] in MEMBER; try contradiction.
  { cbn in MEMBER; destruct MEMBER as [<-|[]].
    exists code,result; split; [exact COMPILE|exact RUN]. }
  all: cbn [compile_flat_value] in COMPILE;
    destruct (compile_flat_value codes reads value1) as [first|] eqn:FIRST; [|discriminate];
    destruct (compile_flat_value codes reads value2) as [second|] eqn:SECOND; [|discriminate];
    inversion COMPILE; subst code;
    apply scalar_binary_inv in RUN as [a [b [A [B OP]]]];
    rewrite (@memory_source_flat_type codes reads value1 first CODE_TYPES READ_TYPES FIRST),
      (@memory_source_flat_type codes reads value2 second CODE_TYPES READ_TYPES SECOND) in OP;
    match type of OP with sem_binary_operation _ ?operation _ _ _ _ _ = _ =>
      destruct (@memory_source_binary_words ge operation a b memory result ltac:(auto) OP) as [x [y [-> ->]]] end;
    apply in_app_or in MEMBER as [MEMBER|MEMBER];
    [eapply IHvalue1|eapply IHvalue2]; eauto.
Qed.
End PARAMETER_READS.

Lemma memory_tempvar_word_inverse ge locals temps memory identifier word :
  eval_expr ge locals temps memory (Etempvar identifier type_int32s) (Vint word) ->
  temps ! identifier = Some (Vint word).
Proof.
  intro RUN; inversion RUN; subst; [assumption|].
  match goal with LVALUE : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inversion LVALUE end.
Qed.
Theorem memory_source_used_register_typed ge locals temps memory layout reads value code result identifier index :
  Forall (fun read => typeof read = type_int32s) reads ->
  nth_error layout index = Some identifier -> In index (memory_source_parameter_positions value) ->
  compile_flat_value (memory_pointer_register_codes layout) reads value = Some code ->
  eval_expr ge locals temps memory code (Vint result) -> exists word, temps ! identifier = Some (Vint word).
Proof.
  intros TYPES LOOKUP USED COMPILE RUN.
  destruct (@memory_source_parameter_inverse ge locals temps memory (memory_pointer_register_codes layout) reads
    (memory_pointer_register_types layout) TYPES value code result COMPILE RUN index USED)
    as [operand [word [OPERAND EVAL]]].
  unfold memory_pointer_register_codes in OPERAND; rewrite nth_error_map,LOOKUP in OPERAND; cbn in OPERAND;
    inversion OPERAND; subst operand.
  exists word; eapply memory_tempvar_word_inverse; exact EVAL.
Qed.
Print Assumptions memory_source_parameter_inverse.
Print Assumptions memory_source_used_register_typed.
