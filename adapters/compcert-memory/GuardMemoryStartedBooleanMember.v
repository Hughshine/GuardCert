From Stdlib Require Import List Bool ZArith.
From GuardMemory Require Import GuardMemoryStartedBooleanRectangle GuardMemoryStartedBooleanWrapper GuardMemoryStartedFootprint.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Lemma memory_boolean_started_all_member test counts start :
  counts <> [] -> start <= hd 0 counts -> Forall (fun count => 0 <= count) counts ->
  memory_boolean_started_all_result test counts start = true <->
  forall coordinates, memory_started_axis_coordinates start counts coordinates -> test coordinates = true.
Proof.
  destruct counts as [|upper counts]; intros NONEMPTY ORDER RANGES; [contradiction|].
  inversion RANGES; subst.
  apply memory_boolean_started_rectangle_member; assumption.
Qed.
Print Assumptions memory_boolean_started_all_member.
