From Stdlib Require Import List ZArith.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryScalarPointerSyntax.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_scalar_pointer_describer := forall source : statement, option (memory_scalar_pointer_region_package source).
Definition memory_scalar_pointer_candidate_service := memory_scalar_pointer_describer -> statement -> CoreAlarmed.Base.imp (option statement).
Fixpoint check_memory_scalar_pointer_caps (service : memory_scalar_pointer_candidate_service) caps source : CoreAlarmed.Base.imp (option statement) :=
  match caps with
  | [] => pure None
  | cap::rest => BIND selected <- service (describe_memory_scalar_pointer_region_with_cap cap) source -;
      match selected with Some target => pure (Some target) | None => check_memory_scalar_pointer_caps service rest source end
  end.
Theorem check_memory_scalar_pointer_caps_sound (service : memory_scalar_pointer_candidate_service) live caps source target :
  (forall describe source target, mayReturn (service describe source) (Some target) -> projected_region_contract live source target) ->
  mayReturn (check_memory_scalar_pointer_caps service caps source) (Some target) -> projected_region_contract live source target.
Proof.
  intro SOUND; induction caps as [|cap rest IH]; cbn; intro RUN.
  - apply mayReturn_pure in RUN; discriminate.
  - bind_imp_destruct RUN selected CHECK; destruct selected as [chosen|].
    + apply mayReturn_pure in RUN; inversion RUN; subst chosen; eapply SOUND; exact CHECK.
    + apply IH; exact RUN.
Qed.
Print Assumptions check_memory_scalar_pointer_caps_sound.
