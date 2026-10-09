From Guard Require Import PolCertFloorMembership PolCertFloorClight.
From GuardMemory Require Import GuardMemoryDoubleAssignment GuardMemoryDoublePolyhedral.

(** The native candidate producer consumes these extracted, verified predicate
    constructors. Existing candidate validation and range-checked lowering
    retain authority over installation. *)
Module DoubleFloorMembership :=
  PolCertFloorMembershipFor DoubleAssignmentInstr DoubleAssignmentIRs.Loop.
Module DoubleFloorClight :=
  PolCertFloorClightFor DoubleAssignmentInstr DoubleAssignmentIRs.Loop.

Print Assumptions DoubleFloorMembership.lower_membership_correct.
Print Assumptions DoubleFloorMembership.upper_membership_correct.
Print Assumptions DoubleFloorClight.lower_bound_exact.
Print Assumptions DoubleFloorClight.upper_bound_exact.
Print Assumptions DoubleFloorClight.lower_bound_pure.
Print Assumptions DoubleFloorClight.upper_bound_pure.
