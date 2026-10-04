From Stdlib Require Import List Bool ZArith.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryParamPointerSyntax GuardMemoryParamAxisDescribe.
From GuardMemory Require Import GuardMemoryVersionFamily GuardMemoryParamVersionComponents.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem check_memory_param_axis_profiles_components_sound source live
  (check : memory_param_pointer_region_package source -> CoreAlarmed.Base.imp (option statement)) :
  (forall package target, mayReturn (check package) (Some target) ->
    exists components, memory_peel_guard_components target = Some components /\
      memory_version_components_valid live source components) ->
  forall profiles target, mayReturn (check_memory_param_axis_profiles check profiles) (Some target) ->
    exists components, memory_peel_guard_components target = Some components /\
      memory_version_components_valid live source components.
Proof.
  intros CHECK profiles; induction profiles as [|profile profiles IH]; intros target RUN; cbn [check_memory_param_axis_profiles] in RUN.
  - apply mayReturn_pure in RUN; discriminate.
  - destruct (describe_memory_param_axis_at source profile) as [package|].
    + bind_imp_destruct RUN candidate ACCEPTED; destruct candidate as [candidate|].
      * apply mayReturn_pure in RUN; inversion RUN; subst target; apply CHECK with (package := package); exact ACCEPTED.
      * apply IH; exact RUN.
    + apply IH; exact RUN.
Qed.

Fixpoint collect_memory_param_version_groups source
  (check : memory_param_pointer_region_package source -> CoreAlarmed.Base.imp (option statement))
  (groups : list (list (list Z * list Z))) : CoreAlarmed.Base.imp (list memory_version_components) :=
  match groups with
  | [] => pure []
  | group::rest => BIND target <- check_memory_param_axis_profiles check group -;
      BIND others <- collect_memory_param_version_groups check rest -;
      pure (match target with
        | Some code => match memory_peel_guard_components code with Some components => components::others | None => others end
        | None => others end)
  end.

Theorem collect_memory_param_version_groups_sound source live
  (check : memory_param_pointer_region_package source -> CoreAlarmed.Base.imp (option statement)) :
  (forall package target, mayReturn (check package) (Some target) ->
    exists components, memory_peel_guard_components target = Some components /\
      memory_version_components_valid live source components) ->
  forall groups components, mayReturn (collect_memory_param_version_groups check groups) components ->
    Forall (memory_version_components_valid live source) components.
Proof.
  intros CHECK groups; induction groups as [|group rest IH]; intros components RUN; cbn [collect_memory_param_version_groups] in RUN.
  - apply mayReturn_pure in RUN; subst; constructor.
  - bind_imp_destruct RUN target SELECTED; bind_imp_destruct RUN others COLLECTED.
    pose proof (IH others COLLECTED) as VALID.
    apply mayReturn_pure in RUN; destruct target as [target|].
    + destruct (@check_memory_param_axis_profiles_components_sound source live check CHECK group target SELECTED)
        as [first [PEEL FIRST]].
      rewrite PEEL in RUN; subst components; constructor; assumption.
    + subst components; exact VALID.
Qed.

Definition compile_memory_param_version_groups source
  (check : memory_param_pointer_region_package source -> CoreAlarmed.Base.imp (option statement)) groups :=
  BIND components <- collect_memory_param_version_groups check groups -;
  pure (match components with [] => None | _ => Some (memory_version_components_statement source components) end).

Theorem compile_memory_param_version_groups_sound source live
  (check : memory_param_pointer_region_package source -> CoreAlarmed.Base.imp (option statement)) :
  (forall package target, mayReturn (check package) (Some target) ->
    exists components, memory_peel_guard_components target = Some components /\
      memory_version_components_valid live source components) ->
  forall groups target, mayReturn (compile_memory_param_version_groups check groups) (Some target) ->
    projected_region_contract live source target.
Proof.
  intros CHECK groups target RUN; unfold compile_memory_param_version_groups in RUN.
  bind_imp_destruct RUN components COLLECTED.
  pose proof (@collect_memory_param_version_groups_sound source live check CHECK groups components COLLECTED) as VALID.
  apply mayReturn_pure in RUN; destruct components as [|first rest]; [discriminate|].
  inversion RUN; subst target.
  exact (@memory_version_components_nonempty_sound live source (first::rest) ltac:(discriminate) VALID).
Qed.

Definition propose_memory_param_version_groups source :=
  let profiles := propose_memory_param_axis_profiles source in
  map (fun cap => filter (fun profile => forallb (fun actual => Z.eqb actual cap) (snd profile)) profiles) [64;16;8;4;1].
Print Assumptions compile_memory_param_version_groups_sound.
