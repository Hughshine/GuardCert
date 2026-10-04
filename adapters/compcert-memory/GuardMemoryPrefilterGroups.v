From Stdlib Require Import List Bool ZArith.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryParamPointerSyntax GuardMemoryVersionFamily
  GuardMemoryParamVersionComponents GuardMemoryParamVersionGroups.
From GuardMemory Require Import GuardMemoryPrefilterComponents.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.

Definition compile_memory_param_prefilter_groups source
  (check : memory_param_pointer_region_package source -> CoreAlarmed.Base.imp (option statement)) groups :=
  BIND components <- collect_memory_param_version_groups check groups -;
  pure (match components with
    | [] => None
    | _ => Some (memory_version_components_statement source
        (memory_prefilter_component_list source components)) end).

Theorem compile_memory_param_prefilter_groups_sound source live
  (check : memory_param_pointer_region_package source -> CoreAlarmed.Base.imp (option statement)) :
  (forall package target, mayReturn (check package) (Some target) ->
    exists components, memory_peel_guard_components target = Some components /\
      memory_version_components_valid live source components) ->
  forall groups target, mayReturn (compile_memory_param_prefilter_groups check groups) (Some target) ->
    projected_region_contract live source target.
Proof.
  intros CHECK groups target RUN; unfold compile_memory_param_prefilter_groups in RUN.
  bind_imp_destruct RUN components COLLECTED.
  pose proof (@collect_memory_param_version_groups_sound source live check CHECK groups components COLLECTED) as VALID.
  apply mayReturn_pure in RUN; destruct components as [|first rest]; [discriminate|].
  inversion RUN; subst target.
  exact (@memory_prefilter_component_list_sound live source (first::rest)
    ltac:(discriminate) VALID).
Qed.
Print Assumptions compile_memory_param_prefilter_groups_sound.
