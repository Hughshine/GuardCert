From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryLongHeaderLicense
  GuardMemoryDoubleRectangularNestData.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A later header is licensed by the source only after every preceding axis
    is known to enter its body. Empty/refused paths do not license such reads. *)
Definition double_rectangular_positive_prefix ge locals memory (axes : double_rectangular_axes) depth :=
  forall axis, In axis (firstn depth axes) -> exists bound_block word,
    double_global_binding ge locals (snd axis) bound_block /\
    Mem.load Mint64 memory bound_block 0=Some (Vlong word) /\ 0<Int64.signed word.
Theorem double_rectangular_next_header_license depth :
  forall axes iterator header bound_block body fe ge locals temps memory after final,
  (exists target rhs, body=Sassign target rhs) ->
  nth_error axes depth=Some (iterator,header) ->
  double_global_binding ge locals header bound_block ->
  double_rectangular_positive_prefix ge locals memory axes depth ->
  exec_stmt fe ge locals temps memory (double_rectangular_nest_code axes body) E0 after final Out_normal ->
  exists word, Mem.load Mint64 memory bound_block 0=Some (Vlong word).
Proof.
  induction depth as [|depth IH]; intros [|[outer outer_header] axes] iterator header bound_block body fe ge locals
    temps memory after final ASSIGNMENT INDEX BINDING PREFIX SOURCE; cbn [nth_error] in INDEX; try discriminate.
  - inversion INDEX; subst outer outer_header.
    cbn [double_rectangular_nest_code] in SOURCE.
    destruct (@memory_global_long_initialized_license fe ge locals temps memory iterator header bound_block
      (double_rectangular_nest_code axes body) after final BINDING
      (@double_rectangular_nest_normal axes body ASSIGNMENT) SOURCE) as [word [LOAD _]].
    exists word; exact LOAD.
  - destruct (@PREFIX (outer,outer_header) ltac:(cbn [firstn]; left; reflexivity))
      as [outer_block [word [OUTER_BINDING [LOAD POSITIVE]]]].
    cbn [double_rectangular_nest_code] in SOURCE.
    destruct (@memory_global_long_initialized_license fe ge locals temps memory outer outer_header outer_block
      (double_rectangular_nest_code axes body) after final OUTER_BINDING
      (@double_rectangular_nest_normal axes body ASSIGNMENT) SOURCE) as [actual [ACTUAL CHILD]].
    rewrite LOAD in ACTUAL; inversion ACTUAL; subst actual.
    destruct (CHILD POSITIVE) as [body_temps [body_memory CHILD_SOURCE]].
    eapply IH; [exact ASSIGNMENT|exact INDEX|exact BINDING| |exact CHILD_SOURCE].
    intros axis MEMBER; apply PREFIX; cbn [firstn]; right; exact MEMBER.
Qed.

Print Assumptions double_rectangular_next_header_license.
