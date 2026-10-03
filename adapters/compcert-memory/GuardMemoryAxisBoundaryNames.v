From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values.
From Guard Require Import ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRecursiveSource.
From GuardMemory Require Import GuardMemoryAxisBoundaryMath.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_axis_boundary_names (mask : list bool) (counters : list ident) zero :=
  match mask,counters with
  | side::rest,counter::tail => (if side then counter else zero)::memory_axis_boundary_names rest tail zero
  | _,_ => [] end.

Lemma memory_axis_boundary_names_length mask counters zero :
  length mask = length counters -> length (memory_axis_boundary_names mask counters zero) = length counters.
Proof.
  revert counters; induction mask; intros [|counter counters] LENGTH; cbn in *; try discriminate; auto.
Qed.

Lemma memory_axis_boundary_names_member mask counters zero identifier :
  In identifier (memory_axis_boundary_names mask counters zero) -> In identifier counters \/ identifier = zero.
Proof.
  revert counters; induction mask as [|side mask IH]; intros [|counter counters] MEMBER; cbn in MEMBER; try contradiction.
  destruct MEMBER as [SAME|MEMBER].
  - destruct side; subst; [left; cbn; auto|right; reflexivity].
  - destruct (IH counters MEMBER) as [IN|SAME]; [left; cbn; auto|right; exact SAME].
Qed.

Lemma memory_axis_boundary_names_bindings counters coordinates temps mask zero :
  memory_nest_bindings counters coordinates temps ->
  length mask = length coordinates -> temps ! zero = Some (Vint Int.zero) ->
  memory_nest_bindings (memory_axis_boundary_names mask counters zero) (memory_axis_boundary_pick mask coordinates) temps.
Proof.
  intro WORDS; revert mask; induction WORDS as [|counter coordinate counters coordinates WORD WORDS IH];
    intros [|side mask] LENGTH ZERO; cbn in LENGTH; try discriminate; cbn; constructor.
  - destruct side; [exact WORD|exact ZERO].
  - apply IH; [lia|exact ZERO].
Qed.

Lemma memory_axis_rectangle_coordinates_signed counts coordinates :
  Forall signed_range counts ->
  Forall2 (fun coordinate count => 0 <= coordinate < count) coordinates counts ->
  Forall signed_range coordinates.
Proof.
  intros COUNTS COORDINATES; induction COORDINATES as [|coordinate count coordinates counts RANGE TAIL IH]; constructor.
  - inversion COUNTS; subst; unfold signed_range in *.
    change Int.min_signed with (-2147483648) in *; lia.
  - apply IH; inversion COUNTS; assumption.
Qed.
Print Assumptions memory_axis_boundary_names_bindings.
Print Assumptions memory_axis_rectangle_coordinates_signed.
