From Stdlib Require Import List ZArith.
From compcert.common Require Import AST.
From polcert.src Require Import PolyBase.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemoryLoopTrace GuardMemoryNaryCompute
  GuardMemoryWindowSingleFootprint GuardMemoryMultiPointerIdentifiers GuardMemoryFootprintRestriction.
From GuardAffineNest Require Import AffineNestSyntax AffineNestLoopEncoding AffineNestLeafLoop AffineNestLeafDecode
  AffineNestRealDecode AffineNestGuardPackage AffineNestLeafModel.
Import ListNotations.
Set Implicit Arguments.

Lemma affine_leaf_sequence_single pointer dimensions parameters instructions :
  Forall(window_instruction_single pointer) instructions ->
  window_list_single pointer(affine_leaf_sequence dimensions parameters instructions).
Proof. intro SINGLE; induction SINGLE; cbn; [exact I|split; assumption]. Qed.

Theorem affine_lower_nest_single pointer nest : forall prefix parameters lower leaf code,
  window_loop_single pointer leaf -> affine_lower_nest nest prefix parameters lower leaf=Some code ->
  window_loop_single pointer code.
Proof.
  induction nest as [source|iterator bound expression body nest IHnest]; intros prefix parameters lower leaf code SINGLE LOWER.
  - cbn [affine_lower_nest] in LOWER; inversion LOWER; subst; exact SINGLE.
  - destruct(@affine_lower_nest_axis iterator bound expression body nest prefix parameters lower leaf code LOWER)
      as [upper [child [UPPER [CHILD CODE]]]]; subst code.
    cbn [window_loop_single]; eapply IHnest; eassumption.
Qed.

Theorem affine_package_single_covered source parameters live proposal
  (package:affine_guard_package source parameters live proposal) pointer lower code values :
  affine_proposed_pointers proposal=[pointer] ->
  affine_checked_nest_loop(affine_proposal_nest proposal) parameters [](affine_proposed_operations proposal) lower=Some code ->
  memory_loop_cells_covered(fun cell=>Pos.eqb(arr_id cell) pointer) code values.
Proof.
  intros SINGLE LOWER; apply(proj1(window_single_trace_covered pointer)).
  unfold affine_checked_nest_loop in LOWER; eapply affine_lower_nest_single; [|exact LOWER].
  unfold affine_checked_leaf_code; cbn [window_loop_single]; apply affine_leaf_sequence_single.
  pose proof(affine_leaf_covered(affine_package_leaf package)) as OWNED; rewrite SINGLE in OWNED.
  apply Forall_map; eapply Forall_impl; [|exact OWNED]; intros operation COVERED; apply window_operation_single; exact COVERED.
Qed.
Print Assumptions affine_package_single_covered.
