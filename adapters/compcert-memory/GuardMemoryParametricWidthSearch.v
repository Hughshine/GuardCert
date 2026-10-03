From Stdlib Require Import List ZArith.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryParametricRegion GuardMemoryParametricRegionRestriction.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_parametric_describer := forall source : statement, option (memory_parametric_region_package source).
Definition memory_parametric_candidate_service := memory_parametric_describer -> statement -> CoreAlarmed.Base.imp (option statement).
Fixpoint check_memory_parametric_widths (service : memory_parametric_candidate_service)
  (describe : memory_parametric_describer) widths source : CoreAlarmed.Base.imp (option statement) :=
  match widths with
  | [] => pure None
  | width::rest =>
      BIND selected <- service (describe_memory_parametric_width width describe) source -;
      match selected with
      | Some target => pure (Some target)
      | None => check_memory_parametric_widths service describe rest source
      end
  end.
Theorem check_memory_parametric_widths_sound (service : memory_parametric_candidate_service)
  live describe widths source target :
  (forall describe source target, mayReturn (service describe source) (Some target) -> projected_region_contract live source target) ->
  mayReturn (check_memory_parametric_widths service describe widths source) (Some target) -> projected_region_contract live source target.
Proof.
  intro SOUND; induction widths as [|width rest IH]; cbn; intro RUN.
  - apply mayReturn_pure in RUN; discriminate.
  - bind_imp_destruct RUN selected CHECK; destruct selected as [chosen|].
    + apply mayReturn_pure in RUN; inversion RUN; subst chosen; eapply SOUND; exact CHECK.
    + apply IH; exact RUN.
Qed.
Definition check_memory_parametric_with_widths (service : memory_parametric_candidate_service)
  (describe : memory_parametric_describer) widths source :=
  BIND selected <- service describe source -;
  match selected with
  | Some target => pure (Some target)
  | None => check_memory_parametric_widths service describe widths source
  end.
Theorem check_memory_parametric_with_widths_sound (service : memory_parametric_candidate_service)
  live describe widths source target :
  (forall describe source target, mayReturn (service describe source) (Some target) -> projected_region_contract live source target) ->
  mayReturn (check_memory_parametric_with_widths service describe widths source) (Some target) -> projected_region_contract live source target.
Proof.
  intros SOUND RUN; unfold check_memory_parametric_with_widths in RUN.
  bind_imp_destruct RUN selected CHECK; destruct selected as [chosen|].
  - apply mayReturn_pure in RUN; inversion RUN; subst chosen; eapply SOUND; exact CHECK.
  - eapply check_memory_parametric_widths_sound; eassumption.
Qed.
Print Assumptions check_memory_parametric_widths_sound.
Print Assumptions check_memory_parametric_with_widths_sound.
