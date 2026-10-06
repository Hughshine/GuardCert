From Stdlib Require Import List ZArith.
From polcert.lib Require Import ImpureAlarmConfig.
From polcert.src Require Import TilingWitness.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryExtractedTiling GuardMemoryParametricChecker GuardMemoryParametricInstructionChecker.
Import CoreAlarmed ListNotations.
Set Implicit Arguments.

(** Domain-library obligation C_opt. A supplied witness must connect the
    extracted, actual source and candidate point sets, including quotient
    coordinates. The inherited checker also validates dependence preservation.
    This wrapper does not generate or trust a replacement source domain. *)
Definition checked_parametric_model_tiling base source arrays row context bounds expression candidate witnesses :=
  let vars := map (fun array => (array,tt)) (context++arrays) in
  checked_memory_extracted_tiling_loops
    (memory_parametric_assumed_loop base row context bounds expression source,context,vars)
    (memory_parametric_assumed_loop base row context bounds expression candidate,context,vars) witnesses.
Theorem checked_parametric_model_tiling_correct base source arrays row context bounds expression candidate witnesses :
  mayReturn (checked_parametric_model_tiling base source arrays row context bounds expression candidate witnesses) true ->
  memory_parametric_model_candidate_certificate base source row context bounds expression candidate.
Proof.
  intros CHECK parameters before after LENGTH WITHIN WIDTH NONALIAS SOURCE.
  apply memory_parametric_assumed_execution with (base:=base) (row:=row) (context:=context)
    (bounds:=bounds) (expression:=expression); [exact WITHIN|exact WIDTH|].
  pose proof (@validated_memory_extracted_tiling_loops_at
    (memory_parametric_assumed_loop base row context bounds expression source)
    (memory_parametric_assumed_loop base row context bounds expression candidate) context
    (map (fun array => (array,tt)) (context++arrays)) witnesses
    (rev parameters) before after ltac:(rewrite rev_length; exact LENGTH) NONALIAS CHECK) as VALID.
  rewrite rev_involutive in VALID; apply VALID; apply memory_parametric_assumed_execution; assumption.
Qed.
Print Assumptions checked_parametric_model_tiling_correct.
