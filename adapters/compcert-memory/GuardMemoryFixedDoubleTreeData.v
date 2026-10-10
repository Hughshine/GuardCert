From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Cop Clight ClightBigstep.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleSourceInstruction
  GuardMemoryDoubleSourceTreeData GuardMemoryLongSourceAffine GuardMemoryAffineLongEndpoint
  GuardMemoryLongControl GuardMemoryLongRangeSource GuardMemoryLongExpressionCapture.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** These names index mathematical parameters only. They introduce neither
    program globals nor additional memory reads. Equal fixed upper values share
    one parameter slot in the existing checked candidate pipeline. *)
Definition fixed_double_parameter_name value : ident := match value with
  | Z0 => xH | Zpos positive => xO positive | Zneg positive => xI positive end.
Definition fixed_double_parameter_value (name : ident) := match name with
  | xH => 0 | xO positive => Zpos positive | xI positive => Zneg positive end.
Lemma fixed_double_parameter_roundtrip value :
  fixed_double_parameter_value (fixed_double_parameter_name value)=value.
Proof. destruct value; reflexivity. Qed.

Inductive fixed_double_source_tree :=
| FixedDoubleSkip
| FixedDoublePoint (body : statement) (instruction : double_source_instruction)
| FixedDoubleSequence (first second : fixed_double_source_tree)
| FixedDoubleRange (raw : bool) (iterator : ident) (start : int)
    (bound : expr) (upper : Z) (child : fixed_double_source_tree).

Fixpoint fixed_double_tree_skeleton tree := match tree with
  | FixedDoubleSkip => DoubleTreeSkip
  | FixedDoublePoint body instruction => DoubleTreePoint body instruction
  | FixedDoubleSequence first second => DoubleTreeSequence
      (fixed_double_tree_skeleton first) (fixed_double_tree_skeleton second)
  | FixedDoubleRange raw iterator start _ upper child => DoubleTreeRange raw iterator start
      (DoubleTreeBound (fixed_double_parameter_name upper) None) (fixed_double_tree_skeleton child)
  end.
Fixpoint fixed_double_source_tree_code tree := match tree with
  | FixedDoubleSkip => Sskip
  | FixedDoublePoint body _ => body
  | FixedDoubleSequence first second => Ssequence
      (fixed_double_source_tree_code first) (fixed_double_source_tree_code second)
  | FixedDoubleRange raw iterator start bound _ child =>
      if raw then long_raw_from_loop iterator (double_tree_initial start) bound
        (fixed_double_source_tree_code child)
      else memory_long_from_loop iterator (double_tree_initial start)
        (Ebinop Cop.Olt (Etempvar iterator memory_long_type) bound memory_signed_int_type)
        (fixed_double_source_tree_code child)
  end.
Fixpoint fixed_double_source_tree_checked p controls tree : Prop := match tree with
  | FixedDoubleSkip => True
  | FixedDoublePoint body instruction => checked_double_source_instruction p controls body=Some instruction
  | FixedDoubleSequence first second => fixed_double_source_tree_checked p controls first /\
      fixed_double_source_tree_checked p controls second
  | FixedDoubleRange _ iterator _ bound upper child =>
      ~ In iterator controls /\ decode_long_source_index [] bound=Some ([],upper) /\
      Int.min_signed<=upper<=Int.max_signed /\
      fixed_double_source_tree_checked p (controls++[iterator]) child
  end.

Lemma fixed_double_bound_execution source upper ge locals temps memory :
  decode_long_source_index [] source=Some ([],upper) ->
  typeof source=memory_long_type /\ eval_expr ge locals temps memory source (Vlong (Int64.repr upper)).
Proof.
  intro DECODE.
  pose proof (@decoded_affine_long_endpoint_execution [] source ([],upper) (fun _ => 0)
    ge locals temps memory DECODE ltac:(intros id MEMBER; contradiction)) as EXEC.
  change (typeof source=memory_long_type /\ eval_expr ge locals temps memory source (Vlong (Int64.repr (0+upper)))) in EXEC.
  rewrite Z.add_0_l in EXEC; exact EXEC.
Qed.
Lemma fixed_double_skeleton_bound upper :
  double_tree_bound_value fixed_double_parameter_value (DoubleTreeBound (fixed_double_parameter_name upper) None)=upper.
Proof. unfold double_tree_bound_value; cbn; rewrite fixed_double_parameter_roundtrip; lia. Qed.
Lemma fixed_double_bound_type source upper :
  decode_long_source_index [] source=Some ([],upper) -> typeof source=memory_long_type.
Proof.
  unfold decode_long_source_index.
  destruct (describe_long_source_affine source) as [expression|] eqn:DESCRIBE; [|discriminate].
  intro DECODE; rewrite (@describe_long_source_affine_exact source expression DESCRIBE).
  apply long_source_affine_type.
Qed.
Theorem fixed_double_source_writes_avoid p controls tree :
  fixed_double_source_tree_checked p controls tree ->
  forall key, In key controls -> ~ In key (double_source_tree_writes (fixed_double_tree_skeleton tree)).
Proof.
  revert controls; induction tree; intros controls CHECK key MEMBER;
    cbn [fixed_double_tree_skeleton double_source_tree_writes]; try tauto.
  - destruct CHECK as [LEFT RIGHT]; intro WRITE; apply in_app_or in WRITE as [WRITE|WRITE];
      [eapply IHtree1|eapply IHtree2]; eauto.
  - destruct CHECK as [FRESH [DECODE [RANGE CHILD]]]; intros [SAME|WRITE].
    + subst key; contradiction.
    + eapply IHtree; [exact CHILD|apply in_or_app; left; exact MEMBER|exact WRITE].
Qed.

Print Assumptions fixed_double_parameter_roundtrip.
Print Assumptions fixed_double_bound_execution.
Print Assumptions fixed_double_skeleton_bound.
Print Assumptions fixed_double_bound_type.
Print Assumptions fixed_double_source_writes_avoid.
