From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST Memory.
From Guard Require Import ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleSourceTreeData
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceLoopModel GuardMemoryDoubleRectangularNestModel
  GuardMemoryLongRangeSource.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** All nodes use one original header vector. Position lookup is used only
    with a membership certificate; missing headers are not semantic inputs. *)
Fixpoint double_tree_header_position (headers : list ident) header : nat :=
  match headers with
  | [] => O
  | current::rest => if peq header current then O else S (double_tree_header_position rest header)
  end.
Lemma double_tree_header_position_value headers header : In header headers ->
  forall valuation : ident -> Z,
    nth (double_tree_header_position headers header) (map valuation headers) 0=valuation header.
Proof.
  induction headers as [|current rest IH]; intros MEMBER valuation; [contradiction|].
  cbn [double_tree_header_position map]; destruct (peq header current) as [SAME|DIFFERENT].
  - subst; reflexivity.
  - cbn; apply IH; destruct MEMBER as [SAME|MEMBER]; [congruence|exact MEMBER].
Qed.
Lemma double_tree_header_position_range headers header : In header headers ->
  (double_tree_header_position headers header < length headers)%nat.
Proof.
  induction headers as [|current rest IH]; intro MEMBER; [contradiction|].
  cbn [double_tree_header_position length]; destruct (peq header current) as [SAME|DIFFERENT]; [lia|].
  assert (REST : In header rest) by (destruct MEMBER as [SAME|MEMBER]; [congruence|exact MEMBER]).
  specialize (IH REST); lia.
Qed.
Definition double_tree_bound_model headers dimensions bound :=
  let parameter := SL.Var (dimensions+double_tree_header_position headers (tree_bound_header bound))%nat in
  match tree_bound_offset bound with
  | None => parameter
  | Some offset => SL.Sum parameter (SL.Constant (- Int.signed offset))
  end.
Theorem double_tree_bound_model_value headers bound prefix valuation :
  In (tree_bound_header bound) headers ->
  SL.eval_expr (rev prefix++map valuation headers) (double_tree_bound_model headers (length prefix) bound)=
    double_tree_bound_value valuation bound.
Proof.
  intro MEMBER.
  assert (PARAMETER : nth (length prefix+double_tree_header_position headers (tree_bound_header bound))%nat
    (rev prefix++map valuation headers) 0=valuation (tree_bound_header bound)).
  { rewrite <- (length_rev prefix),double_rectangular_nth_after_append.
    apply double_tree_header_position_value; exact MEMBER. }
  unfold double_tree_bound_model,double_tree_bound_value.
  destruct (tree_bound_offset bound); cbn [SL.eval_expr]; rewrite PARAMETER; lia.
Qed.

Fixpoint double_source_tree_model headers dimensions tree := match tree with
  | DoubleTreeSkip => SL.Seq SL.SNil
  | DoubleTreePoint _ instruction => SL.Instr (double_source_instruction_model instruction)
      (double_source_arguments dimensions)
  | DoubleTreeSequence first second => SL.Seq
      (SL.SCons (double_source_tree_model headers dimensions first)
        (SL.SCons (double_source_tree_model headers dimensions second) SL.SNil))
  | DoubleTreeRange _ _ start bound child => SL.Loop (SL.Constant (Int.signed start))
      (double_tree_bound_model headers dimensions bound)
      (double_source_tree_model headers (S dimensions) child)
  end.

(** A memory relation for the entire tree. Leaves at different depths retain
    their own control prefixes; assignments use actual IEEE/Mem semantics. *)
Fixpoint double_source_tree_memory tree valuation prefix locations (before after : mem) : Prop :=
  match tree with
  | DoubleTreeSkip => after=before
  | DoubleTreePoint _ instruction => double_source_model_point (double_source_instruction_model instruction) prefix
      (RuntimeState locations before) (RuntimeState locations after)
  | DoubleTreeSequence first second => exists middle,
      double_source_tree_memory first valuation prefix locations before middle /\
      double_source_tree_memory second valuation prefix locations middle after
  | DoubleTreeRange _ _ start bound child => counted_iterations
      (fun value => double_source_tree_memory child valuation (prefix++[value]) locations)
      (memory_long_range_count (Int.signed start) (double_tree_bound_value valuation bound))
      (Int.signed start) before after
  end.

Print Assumptions double_tree_header_position_value.
Print Assumptions double_tree_header_position_range.
Print Assumptions double_tree_bound_model_value.
