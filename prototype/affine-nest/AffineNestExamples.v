From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import Values.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightRectangularLoops ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit.
Import ListNotations.
Local Open Scope Z_scope.
Definition affine_example_source first_expression second_expression setup_id reset :=
  frontend_counted_loop 1%positive 4%positive
    (Ssequence (Sset setup_id (memory_source_affine_code first_expression))
      (Ssequence reset
        (frontend_counted_loop 2%positive 5%positive
          (Ssequence (Sset 6%positive (memory_source_affine_code second_expression))
            (Ssequence (rectangle_reset 3%positive)
              (frontend_counted_loop 3%positive 6%positive Sskip)))))).
Definition affine_example_first := MemorySourceAdd (MemorySourceTemp 1%positive) (MemorySourceTemp 7%positive).
Definition affine_example_second := MemorySourceAdd (MemorySourceTemp 2%positive) (MemorySourceTemp 8%positive).
Definition affine_example_source_ok := affine_example_source affine_example_first affine_example_second 5%positive (rectangle_reset 2%positive).
Definition affine_example_accept source := match describe_affine_nest source [4%positive;7%positive;8%positive] with Some _=>true|None=>false end.
Example three_affine_levels_recognized : affine_example_accept affine_example_source_ok=true.
Proof. vm_compute; reflexivity. Qed.
Example forward_coordinate_dependency_refused :
  affine_example_accept (affine_example_source (MemorySourceAdd (MemorySourceTemp 3%positive) (MemorySourceTemp 7%positive))
    affine_example_second 5%positive (rectangle_reset 2%positive))=false.
Proof. vm_compute; reflexivity. Qed.
Example mismatched_bound_assignment_refused :
  affine_example_accept (affine_example_source affine_example_first affine_example_second 8%positive (rectangle_reset 2%positive))=false.
Proof. vm_compute; reflexivity. Qed.
Example mutated_parameter_registration_refused :
  (match describe_affine_nest affine_example_source_ok [4%positive;5%positive;7%positive;8%positive] with Some _=>true|None=>false end)=false.
Proof. vm_compute; reflexivity. Qed.

Definition affine_example_nest := propose_affine_source_nest 16 affine_example_source_ok.
Definition affine_example_temps := PTree.set 4%positive (Vint(Int.repr 3))
  (PTree.set 7%positive (Vint(Int.repr 2)) (PTree.set 8%positive (Vint Int.one)
    (PTree.set 9%positive (Vint(Int.repr 123)) (PTree.empty val)))).
Example three_level_exit_values :
  map (fun id => (affine_exit_temps affine_example_nest affine_example_temps)!id)
    [1%positive;2%positive;3%positive;4%positive;5%positive;6%positive;9%positive]
  = map (fun value => Some(Vint(Int.repr value))) [3;4;4;3;4;4;123].
Proof. vm_compute; reflexivity. Qed.
Print Assumptions three_affine_levels_recognized.
Print Assumptions forward_coordinate_dependency_refused.
Print Assumptions mismatched_bound_assignment_refused.
Print Assumptions mutated_parameter_registration_refused.
Print Assumptions three_level_exit_values.
