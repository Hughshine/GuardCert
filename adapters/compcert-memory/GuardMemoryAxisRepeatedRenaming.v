From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightNoWrap ClightCountedLoop.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryAffineRenaming
  GuardMemoryNaryAffineExpressions GuardMemoryRecursiveSource GuardMemoryAffineAxisRenaming
  GuardMemoryAxisPointerFootprint.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_axis_bindings_member identifiers values temps identifier :
  memory_nest_bindings identifiers values temps -> In identifier identifiers ->
  exists value, temps ! identifier = Some (Vint (Int.repr value)).
Proof.
  intro WORDS; induction WORDS as [|first value identifiers values WORD WORDS IH]; intro MEMBER;
    [contradiction|].
  cbn in MEMBER; destruct MEMBER as [<-|MEMBER]; [exists value; exact WORD|apply IH; exact MEMBER].
Qed.

Theorem memory_affine_axis_repeated_renamed_evaluation expression term layout counters coordinates
  ge locals temps memory :
  memory_encode_nary_index layout expression = Some term ->
  NoDup layout -> length layout = length counters ->
  memory_nest_bindings counters coordinates temps -> Forall signed_range coordinates ->
  eval_expr ge locals temps memory
    (memory_source_affine_code (memory_source_affine_rename (memory_affine_axis_rename layout counters) expression))
    (Vint (Int.repr (memory_nary_index_value term coordinates))).
Proof.
  intros ENCODE SOURCE_UNIQUE LENGTH WORDS RANGES.
  set (valuation := fun identifier => Int.signed (temp_word identifier temps)).
  assert (COORDINATES : map valuation counters = coordinates).
  { unfold valuation; exact (memory_axis_pointer_parameters WORDS RANGES). }
  assert (LAYOUT : map (fun identifier => valuation (memory_affine_axis_rename layout counters identifier)) layout = coordinates).
  { rewrite <-map_map,memory_affine_axis_rename_layout by assumption; exact COORDINATES. }
  pose proof (@memory_encode_nary_index_value expression layout term
    (fun identifier => valuation (memory_affine_axis_rename layout counters identifier)) ENCODE) as MATH.
  assert (VALUE : memory_source_affine_math
    (fun identifier => valuation (memory_affine_axis_rename layout counters identifier)) expression =
    memory_nary_index_value term coordinates).
  { etransitivity; [exact MATH|]. f_equal; exact LAYOUT. }
  rewrite <-VALUE; apply memory_source_affine_rename_evaluation.
  intros identifier MEMBER.
  assert (MAPPED : In (memory_affine_axis_rename layout counters identifier)
    (map (memory_affine_axis_rename layout counters) layout)).
  { apply in_map; eapply memory_encode_nary_index_reads; eassumption. }
  rewrite memory_affine_axis_rename_layout in MAPPED by assumption.
  destruct (@memory_axis_bindings_member counters coordinates temps _ WORDS MAPPED) as [value WORD].
  unfold valuation,temp_word; rewrite WORD,Int.repr_signed; reflexivity.
Qed.
Print Assumptions memory_affine_axis_repeated_renamed_evaluation.
