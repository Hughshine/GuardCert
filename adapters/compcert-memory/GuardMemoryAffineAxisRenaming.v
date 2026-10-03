From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceLoop
  GuardMemoryAffineRenaming GuardMemoryNaryAffineExpressions GuardMemoryRecursiveSource GuardMemoryRecursiveBody.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_axis_rename layout counters identifier :=
  match memory_source_position identifier layout with
  | Some position => nth position counters identifier
  | None => identifier
  end.

Lemma memory_source_position_nth layout : NoDup layout -> forall position identifier,
  nth_error layout position = Some identifier ->
  memory_source_position identifier layout = Some position.
Proof.
  intro UNIQUE; induction UNIQUE as [|first rest FRESH UNIQUE IH]; intros [|position] identifier LOOKUP;
    cbn in LOOKUP; try discriminate.
  - inversion LOOKUP; subst identifier; cbn; destruct (peq first first); congruence.
  - cbn; destruct (peq identifier first) as [SAME|DIFFERENT].
    + subst; exfalso; apply FRESH; eapply nth_error_In; exact LOOKUP.
    + rewrite (IH position identifier LOOKUP); reflexivity.
Qed.

Lemma memory_affine_axis_rename_layout layout counters :
  NoDup layout -> length layout = length counters ->
  map (memory_affine_axis_rename layout counters) layout = counters.
Proof.
  intros UNIQUE LENGTH; apply nth_error_ext; intro position.
  rewrite nth_error_map.
  destruct (nth_error layout position) as [identifier|] eqn:LOOKUP.
  - cbn; unfold memory_affine_axis_rename.
    rewrite (@memory_source_position_nth layout UNIQUE position identifier LOOKUP).
    symmetry; apply nth_error_nth'; rewrite <-LENGTH.
    apply nth_error_Some; rewrite LOOKUP; discriminate.
  - cbn; symmetry; apply nth_error_None.
    rewrite <-LENGTH; apply nth_error_None; exact LOOKUP.
Qed.

Theorem memory_affine_axis_renamed_evaluation expression term layout counters coordinates
  ge locals temps memory :
  memory_encode_nary_index layout expression = Some term ->
  NoDup layout -> NoDup counters -> length layout = length counters ->
  memory_nest_bindings counters coordinates temps ->
  eval_expr ge locals temps memory
    (memory_source_affine_code (memory_source_affine_rename (memory_affine_axis_rename layout counters) expression))
    (Vint (Int.repr (memory_nary_index_value term coordinates))).
Proof.
  intros ENCODE SOURCE_UNIQUE COUNTER_UNIQUE LENGTH WORDS.
  destruct (memory_nest_bindings_valuation COUNTER_UNIQUE WORDS) as [valuation [COORDINATES VALUES]].
  assert (LAYOUT : map (fun identifier => valuation (memory_affine_axis_rename layout counters identifier)) layout = coordinates).
  { rewrite <-map_map,memory_affine_axis_rename_layout by assumption; exact COORDINATES. }
  pose proof (@memory_encode_nary_index_value expression layout term
    (fun identifier => valuation (memory_affine_axis_rename layout counters identifier)) ENCODE) as MATH.
  assert (VALUE : memory_source_affine_math
    (fun identifier => valuation (memory_affine_axis_rename layout counters identifier)) expression =
    memory_nary_index_value term coordinates).
  { etransitivity; [exact MATH|]. f_equal; exact LAYOUT. }
  rewrite <-VALUE.
  apply memory_source_affine_rename_evaluation.
  intros identifier MEMBER; apply VALUES.
  assert (MAPPED : In (memory_affine_axis_rename layout counters identifier)
    (map (memory_affine_axis_rename layout counters) layout)).
  { apply in_map; eapply memory_encode_nary_index_reads; eassumption. }
  rewrite memory_affine_axis_rename_layout in MAPPED by assumption; exact MAPPED.
Qed.
Print Assumptions memory_affine_axis_rename_layout.
Print Assumptions memory_affine_axis_renamed_evaluation.
