From Stdlib Require Import List Bool.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryProjectedCondition GuardMemorySequentialCondition
  GuardMemoryVersionFamily.
From GuardMemory Require Import GuardMemoryCheckPrefix GuardMemoryPrefilterVersions.
Import ListNotations PrivateRegion.
Set Implicit Arguments.

Definition memory_prefilter_components source (components : memory_version_components) :
  option memory_version_components :=
  match fst components with
  | Ssequence header rest =>
      match memory_check_tree_parse header with
      | Some _ => Some (header,memory_sequential_guarded_statement
          (fst components) (snd components) source)
      | None => None end
  | _ => None end.

Theorem memory_prefilter_components_valid live source components transformed :
  memory_prefilter_components source components = Some transformed ->
  memory_version_components_valid live source components ->
  memory_version_components_valid live source transformed.
Proof.
  destruct components as [check candidate].
  unfold memory_prefilter_components; cbn.
  destruct check; try discriminate.
  destruct (memory_check_tree_parse check1) as [tree|] eqn:PARSE; [|discriminate].
  intros SAME [rule ENCODE]; inversion SAME; subst transformed.
  set (version := {| memory_version_candidate := candidate;
    memory_version_rule := rule; memory_version_check := Ssequence check1 check2;
    memory_version_encoding := ENCODE |}).
  exists (memory_verified_guarded_rule version (fun _ => True)).
  intros fe state DOMAIN.
  change (projected_rule_domain rule state) in DOMAIN.
  destruct (ENCODE fe state DOMAIN) as [accepted [checked [RUN PROPERTY]]].
  destruct (@memory_projected_tree_prefix fe state live check1 check2 tree accepted checked PARSE RUN)
    as [result PREFIX].
  exists result,(entry_temps state); split; [exact PREFIX|intros; exact I].
Qed.

Fixpoint memory_prefilter_component_list source (components : list memory_version_components) :=
  match components with
  | [] => []
  | first::rest =>
      (match memory_prefilter_components source first with
       | Some transformed => transformed | None => first end) ::
      memory_prefilter_component_list source rest
  end.

Theorem memory_prefilter_component_list_valid live source components :
  Forall (memory_version_components_valid live source) components ->
  Forall (memory_version_components_valid live source)
    (memory_prefilter_component_list source components).
Proof.
  intro VALID; induction VALID as [|first rest HEAD TAIL IH]; cbn; constructor; [|exact IH].
  destruct (memory_prefilter_components source first) as [transformed|] eqn:TRANSFORM;
    [eapply memory_prefilter_components_valid; eassumption|exact HEAD].
Qed.

Lemma memory_prefilter_component_list_length source components :
  length (memory_prefilter_component_list source components) = length components.
Proof. induction components; cbn; congruence. Qed.

Theorem memory_prefilter_component_list_sound live source components :
  components <> [] -> Forall (memory_version_components_valid live source) components ->
  projected_region_contract live source
    (memory_version_components_statement source (memory_prefilter_component_list source components)).
Proof.
  intros NONEMPTY VALID; apply memory_version_components_nonempty_sound.
  - intro EMPTY; apply (f_equal (@length memory_version_components)) in EMPTY.
    rewrite memory_prefilter_component_list_length in EMPTY.
    destruct components; [contradiction|discriminate].
  - apply memory_prefilter_component_list_valid; exact VALID.
Qed.
Print Assumptions memory_prefilter_component_list_sound.
