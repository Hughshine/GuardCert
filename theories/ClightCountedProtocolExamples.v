From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Cop Clight ClightBigstep.
From Guard Require Import SilentRegionProtocol ClightCondition ClightCountedLoop
  ClightCountedProtocol.
Import ListNotations.
Set Implicit Arguments.

(** A zero-trip source does not evaluate its body. In particular, this lemma
    does not require the body's lvalues to denote valid memory locations. *)
Section ZERO_TRIP.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable fn : function.
Variable outside : cont.
Variable iterator bound : ident.
Hypothesis DISTINCT : iterator <> bound.
Variable body : statement.
Hypothesis BODY : memory_body body = true.
Variable le : temp_env.
Variable m : mem.
Variable lower upper : Z.
Hypothesis BOUND : le ! bound = Some (Vint (Int.repr upper)).
Hypothesis LOWER_RANGE : signed_range lower.
Hypothesis UPPER_RANGE : signed_range upper.
Hypothesis EMPTY : (upper <= lower)%Z.

Let P := @counted_region_protocol fe ge locals fn outside iterator bound DISTINCT body BODY.
Let initial := counter_temps iterator le lower.

Lemma zero_trip_path : cursor_path P (@lp_start iterator bound initial m) 3
  (@lp_done iterator bound initial m).
Proof.
  eapply cursor_path_cons; [apply lp_step_start |].
  eapply cursor_path_cons; [apply lp_step_false |].
  - pose proof (@counter_condition_run ge locals le m iterator bound lower upper
      DISTINCT BOUND LOWER_RANGE UPPER_RANGE) as TEST.
    assert ((lower <? upper)%Z = false) as FALSE by (apply Z.ltb_ge; exact EMPTY).
    rewrite FALSE in TEST; exact TEST.
  - eapply cursor_path_cons; [apply lp_step_break | constructor].
Qed.

Theorem zero_trip_source_execution :
  exec_stmt fe ge locals initial m (counted_loop iterator bound body)
    E0 initial m Out_normal.
Proof.
  exact (proj1 (@counted_region_completed fe ge locals fn outside iterator bound DISTINCT
    body BODY (initial, m) 3 (@lp_done iterator bound initial m) (initial, m)
    zero_trip_path eq_refl)).
Qed.
End ZERO_TRIP.

Definition protocol_example_temps (lower upper : Z) : temp_env :=
  counter_temps 1%positive
    (PTree.set 2%positive (Vint (Int.repr upper)) (PTree.empty val)) lower.

Example distance_crosses_zero :
  counter_remaining 1%positive 2%positive (protocol_example_temps (-2) 1) = 3%nat.
Proof. vm_compute; reflexivity. Qed.

Example distance_at_signed_maximum :
  counter_remaining 1%positive 2%positive
    (protocol_example_temps (Int.max_signed - 1) Int.max_signed) = 1%nat.
Proof. vm_compute; reflexivity. Qed.

Example increment_reaches_signed_maximum :
  (increment_temps 1%positive
    (protocol_example_temps (Int.max_signed - 1) Int.max_signed)) ! 1%positive =
  Some (Vint (Int.repr Int.max_signed)).
Proof. vm_compute; reflexivity. Qed.

Example counter_mutation_is_outside_first_protocol :
  memory_body (counter_increment 1%positive) = false.
Proof. reflexivity. Qed.

Print Assumptions zero_trip_source_execution.
