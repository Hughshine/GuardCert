From Stdlib Require Import List Bool.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame.
From Guard Require Import StatefulGuard.
From GuardMemory Require Import GuardMemoryStatefulLanguage.
Set Implicit Arguments.

Definition memory_stateful_entry_language
  (fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop)
  (ge : genv) (live : list ident) : stateful_language clight_entry.
Proof.
  refine {| stateful_command := statement; stateful_test := statement;
    stateful_observation := memory_stateful_observation;
    stateful_command_run := fun code s observed => entry_ge s = ge /\ memory_stateful_command_run fe live code s observed;
    stateful_test_run := memory_stateful_test_run fe live;
    stateful_conditional := stateful_conditional (memory_stateful_clight_language fe live) |}.
  intros check yes no s observed accepted checked TEST [GLOBAL RUN].
  split.
  - destruct TEST as [after [CHECK ->]]; exact GLOBAL.
  - eapply (@stateful_conditional_intro clight_entry (memory_stateful_clight_language fe live)); eassumption.
Defined.
Definition memory_stateful_entry_encoding fe ge live domain presumption check
  (ENCODE : forall s, domain s -> exists accepted after,
    GuardMemoryProjectedCondition.memory_projected_check_execution fe s live check accepted after /\
    (accepted = true -> presumption (Entry (entry_ge s) (entry_env s) after (entry_memory s)))) :
  projected_guard_encoding (memory_stateful_entry_language fe ge live) domain presumption (memory_stateful_public_frame live).
Proof.
  refine (@ProjectedGuardEncoding clight_entry (memory_stateful_entry_language fe ge live) domain presumption
    (memory_stateful_public_frame live) check _).
  intros s DOMAIN; destruct (ENCODE s DOMAIN) as [accepted [after [CHECK PROPERTY]]].
  exists accepted,(Entry (entry_ge s) (entry_env s) after (entry_memory s)); split.
  - exists after; auto.
  - split; [repeat split; try reflexivity; exact (proj2 CHECK)|exact PROPERTY].
Defined.
Print Assumptions memory_stateful_entry_encoding.
