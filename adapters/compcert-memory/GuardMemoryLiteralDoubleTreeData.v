From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleSourceInstruction
  GuardMemoryDoubleSourceTreeData GuardMemoryLongSourceAffine GuardMemoryAffineLongEndpoint
  GuardMemoryLongControl GuardMemoryLongRangeSource GuardMemoryLongExpressionCapture
  GuardMemoryFixedDoubleTreeData GuardMemorySignedLongBoundControl.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** These names index mathematical parameters only. They introduce neither
    program globals nor additional memory reads. Equal fixed upper values share
    one parameter slot in the existing checked candidate pipeline. *)
Definition literal_double_parameter_name value : ident := match value with
  | Z0 => xH | Zpos positive => xO positive | Zneg positive => xI positive end.
Definition literal_double_parameter_value (name : ident) := match name with
  | xH => 0 | xO positive => Zpos positive | xI positive => Zneg positive end.
Lemma literal_double_parameter_roundtrip value :
  literal_double_parameter_value (literal_double_parameter_name value)=value.
Proof. destruct value; reflexivity. Qed.

Definition decode_literal_double_bound source := match source with
  | Econst_int word typ=>if type_eq typ memory_signed_int_type then Some ([],Int.signed word) else None
  | _=>decode_long_source_index [] source end.

Inductive literal_double_source_tree :=
| LiteralDoubleSkip
| LiteralDoublePoint (body : statement) (instruction : double_source_instruction)
| LiteralDoubleSequence (first second : literal_double_source_tree)
| LiteralDoubleRange (raw : bool) (iterator : ident) (start : int)
    (bound : expr) (upper : Z) (child : literal_double_source_tree).

Fixpoint literal_double_tree_skeleton tree := match tree with
  | LiteralDoubleSkip => DoubleTreeSkip
  | LiteralDoublePoint body instruction => DoubleTreePoint body instruction
  | LiteralDoubleSequence first second => DoubleTreeSequence
      (literal_double_tree_skeleton first) (literal_double_tree_skeleton second)
  | LiteralDoubleRange raw iterator start _ upper child => DoubleTreeRange raw iterator start
      (DoubleTreeBound (literal_double_parameter_name upper) None) (literal_double_tree_skeleton child)
  end.
Fixpoint literal_double_source_tree_code tree := match tree with
  | LiteralDoubleSkip => Sskip
  | LiteralDoublePoint body _ => body
  | LiteralDoubleSequence first second => Ssequence
      (literal_double_source_tree_code first) (literal_double_source_tree_code second)
  | LiteralDoubleRange raw iterator start bound _ child =>
      if raw then long_raw_from_loop iterator (double_tree_initial start) bound
        (literal_double_source_tree_code child)
      else memory_long_from_loop iterator (double_tree_initial start)
        (Ebinop Cop.Olt (Etempvar iterator memory_long_type) bound memory_signed_int_type)
        (literal_double_source_tree_code child)
  end.
Fixpoint literal_double_source_tree_checked p controls tree : Prop := match tree with
  | LiteralDoubleSkip => True
  | LiteralDoublePoint body instruction => checked_double_source_instruction p controls body=Some instruction
  | LiteralDoubleSequence first second => literal_double_source_tree_checked p controls first /\
      literal_double_source_tree_checked p controls second
  | LiteralDoubleRange _ iterator _ bound upper child =>
      ~ In iterator controls /\ decode_literal_double_bound bound=Some ([],upper) /\
      Int.min_signed<=upper<=Int.max_signed /\
      literal_double_source_tree_checked p (controls++[iterator]) child
  end.

Lemma literal_double_bound_execution source upper ge locals temps memory :
  decode_long_source_index [] source=Some ([],upper) ->
  typeof source=memory_long_type /\ eval_expr ge locals temps memory source (Vlong (Int64.repr upper)).
Proof.
  intro DECODE.
  pose proof (@decoded_affine_long_endpoint_execution [] source ([],upper) (fun _ => 0)
    ge locals temps memory DECODE ltac:(intros id MEMBER; contradiction)) as EXEC.
  change (typeof source=memory_long_type /\ eval_expr ge locals temps memory source (Vlong (Int64.repr (0+upper)))) in EXEC.
  rewrite Z.add_0_l in EXEC; exact EXEC.
Qed.
Lemma literal_double_skeleton_bound upper :
  double_tree_bound_value literal_double_parameter_value (DoubleTreeBound (literal_double_parameter_name upper) None)=upper.
Proof. unfold double_tree_bound_value; cbn; rewrite literal_double_parameter_roundtrip; lia. Qed.
Lemma literal_double_bound_type source upper :
  decode_literal_double_bound source=Some ([],upper) -> signed_long_bound_type source.
Proof.
  destruct source; cbn [decode_literal_double_bound];
    try (intro DECODE; left; eapply fixed_double_bound_type; exact DECODE).
  destruct (type_eq t memory_signed_int_type) as [TYPE|]; [|discriminate].
  intro DECODE; right; exact TYPE.
Qed.
Theorem literal_double_bound_test_execution source upper ge locals temps memory iterator value :
  decode_literal_double_bound source=Some ([],upper) ->
  Int64.min_signed<=value<=Int64.max_signed -> Int64.min_signed<=upper<=Int64.max_signed ->
  temps ! iterator=Some (Vlong (Int64.repr value)) ->
  eval_expr ge locals temps memory
    (Ebinop Cop.Olt (Etempvar iterator memory_long_type) source memory_signed_int_type)
    (Val.of_bool (value <? upper)).
Proof.
  assert (LONG : forall source, decode_long_source_index [] source=Some ([],upper) ->
    Int64.min_signed<=value<=Int64.max_signed -> Int64.min_signed<=upper<=Int64.max_signed ->
    temps ! iterator=Some (Vlong (Int64.repr value)) ->
    eval_expr ge locals temps memory
      (Ebinop Cop.Olt (Etempvar iterator memory_long_type) source memory_signed_int_type)
      (Val.of_bool (value <? upper))).
  { intros bound DECODE RANGE UPPER WORD; eapply memory_long_test_execution;
      [reflexivity|eapply fixed_double_bound_type; exact DECODE|exact RANGE|exact UPPER|constructor; exact WORD|].
    exact (proj2 (@fixed_double_bound_execution bound upper ge locals temps memory DECODE)). }
  destruct source; cbn [decode_literal_double_bound]; try (apply LONG).
  destruct (type_eq t memory_signed_int_type) as [TYPE|]; [|discriminate].
  intros DECODE RANGE UPPER WORD; inversion DECODE; subst upper.
  eapply eval_Ebinop; [constructor; exact WORD|constructor|].
  cbn [typeof]; rewrite TYPE.
  change (sem_binary_operation (genv_cenv ge) Cop.Olt (Vlong (Int64.repr value)) memory_long_type
    (Vlong (Int64.repr (Int.signed i))) memory_long_type memory=
    Some (Val.of_bool (value <? Int.signed i))).
  apply memory_long_lt_exact; assumption.
Qed.
Theorem literal_double_source_writes_avoid p controls tree :
  literal_double_source_tree_checked p controls tree ->
  forall key, In key controls -> ~ In key (double_source_tree_writes (literal_double_tree_skeleton tree)).
Proof.
  revert controls; induction tree; intros controls CHECK key MEMBER;
    cbn [literal_double_tree_skeleton double_source_tree_writes]; try tauto.
  - destruct CHECK as [LEFT RIGHT]; intro WRITE; apply in_app_or in WRITE as [WRITE|WRITE];
      [eapply IHtree1|eapply IHtree2]; eauto.
  - destruct CHECK as [FRESH [DECODE [RANGE CHILD]]]; intros [SAME|WRITE].
    + subst key; contradiction.
    + eapply IHtree; [exact CHILD|apply in_or_app; left; exact MEMBER|exact WRITE].
Qed.

Print Assumptions literal_double_parameter_roundtrip.
Print Assumptions literal_double_bound_execution.
Print Assumptions literal_double_skeleton_bound.
Print Assumptions literal_double_bound_type.
Print Assumptions literal_double_bound_test_execution.
Print Assumptions literal_double_source_writes_avoid.
