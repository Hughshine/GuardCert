From Stdlib Require Import List Bool.
From compcert.common Require Import AST Events Memory Values.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightTempFrame CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryProjectedCondition GuardMemorySequentialCondition.
From Guard Require Import StatefulGuard.
Import ListNotations.
Set Implicit Arguments.

Definition memory_stateful_observation := (temp_env * mem)%type.
Definition memory_stateful_command_run fe live code s (observed : memory_stateful_observation) :=
  exists after final,
    exec_stmt fe (entry_ge s) (entry_env s) (entry_temps s) (entry_memory s) code E0 after final Out_normal /\
    temp_agree live (fst observed) after /\ memory_equivalent (snd observed) final.
Definition memory_stateful_test_run fe live check s accepted checked :=
  exists after, memory_projected_check_execution fe s live check accepted after /\
    checked = Entry (entry_ge s) (entry_env s) after (entry_memory s).
Definition memory_stateful_clight_language (fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop) (live : list ident) : stateful_language clight_entry.
Proof.
  refine {| stateful_command := statement; stateful_test := statement;
    stateful_observation := memory_stateful_observation;
    stateful_command_run := memory_stateful_command_run fe live;
    stateful_test_run := memory_stateful_test_run fe live;
    stateful_conditional := memory_sequential_guarded_statement |}.
  intros check yes no s observed accepted checked [middle [[CHECK FRAME] ->]]
    [after [final [RUN [AFTER EQUAL]]]].
  exists after,final; split; [|exact (conj AFTER EQUAL)].
  destruct s as [ge locals temps memory]; cbn in *.
  eapply memory_sequential_guarded_projected_execution; eassumption.
Defined.
Definition memory_stateful_public_frame live before after :=
  entry_ge after = entry_ge before /\ entry_env after = entry_env before /\
  entry_memory after = entry_memory before /\ temp_agree live (entry_temps before) (entry_temps after).
Definition memory_stateful_projected_encoding fe live domain presumption check
  (ENCODE : forall s, domain s -> exists accepted after,
    memory_projected_check_execution fe s live check accepted after /\
    (accepted = true -> presumption (Entry (entry_ge s) (entry_env s) after (entry_memory s)))) :
  projected_guard_encoding (memory_stateful_clight_language fe live) domain presumption (memory_stateful_public_frame live).
Proof.
  refine (@ProjectedGuardEncoding clight_entry (memory_stateful_clight_language fe live) domain presumption
    (memory_stateful_public_frame live) check _).
  intros s DOMAIN; destruct (ENCODE s DOMAIN) as [accepted [after [CHECK PROPERTY]]].
  exists accepted,(Entry (entry_ge s) (entry_env s) after (entry_memory s)); split.
  - exists after; auto.
  - split; [repeat split; try reflexivity; exact (proj2 CHECK)|exact PROPERTY].
Defined.
Print Assumptions memory_stateful_clight_language.
Print Assumptions memory_stateful_projected_encoding.
