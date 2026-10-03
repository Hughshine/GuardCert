From Stdlib Require Import List Bool.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition.
From GuardMemory Require Import GuardMemoryProjectedCondition.
From Guard Require Import StatefulGuard StatefulGuardComposition.
From GuardMemory Require Import GuardMemoryStatefulLanguage.
Set Implicit Arguments.

Definition memory_stateful_clight_sequence
  (fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop)
  (live : list ident) : stateful_test_sequence (memory_stateful_clight_language fe live).
Proof.
  refine (@StatefulTestSequence clight_entry (memory_stateful_clight_language fe live) Ssequence _).
  intros first second state middle final accepted rest [middle_temps [FIRST ->]] SECOND.
  destruct accepted.
  - destruct (SECOND eq_refl) as [final_temps [LAST ->]].
    exists final_temps; split; [|reflexivity].
    eapply (@memory_projected_check_sequence fe state live first second true rest middle_temps final_temps);
      [exact FIRST|intro; exact LAST].
  - exists middle_temps; split; [|reflexivity].
    eapply (@memory_projected_check_sequence fe state live first second false rest middle_temps middle_temps);
      [exact FIRST|discriminate].
Defined.
Print Assumptions memory_stateful_clight_sequence.
