From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import Values.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightPureExpr ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryDynamicTensorLayout
  GuardMemoryDynamicTensorAccess GuardMemoryDynamicTensorBackend.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyTreeFacts ClightTensorVolumeGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Observation is a proof-facing computation on the current temporaries. The
    emitted guard consists of the actual dimension expressions, not this lookup.
    Original-source readiness remains a distinct producer obligation. *)
Fixpoint tensor_observe_dimensions sources (temps:temp_env) : option(list Z) :=
  match sources with
  | [] => Some []
  | source::rest =>
      let value := match source with
        | TensorDimensionConstant z => Some(Int.signed(Int.repr z))
        | TensorDimensionTemp identifier => match temps ! identifier with
          | Some(Vint word) => Some(Int.signed word) | _ => None end end in
      match value,tensor_observe_dimensions rest temps with
      | Some dimension,Some dimensions => Some(dimension::dimensions) | _,_ => None end end.
Theorem tensor_observe_dimensions_sound sources temps dimensions :
  tensor_observe_dimensions sources temps=Some dimensions ->
  tensor_dimension_view sources dimensions temps /\ Forall signed_range dimensions.
Proof.
  revert dimensions; induction sources as [|source sources IH]; intros dimensions OBSERVE; cbn [tensor_observe_dimensions] in OBSERVE.
  - inversion OBSERVE; split; constructor.
  - destruct source as [z|identifier]; cbn in OBSERVE.
    + destruct(tensor_observe_dimensions sources temps)as [tail|]eqn:TAIL; [|discriminate].
      inversion OBSERVE; subst dimensions; destruct(IH _ eq_refl)as [VIEW RANGE]; split; constructor; try assumption.
      * reflexivity.
      * apply Int.signed_range.
    + destruct(temps ! identifier)as [value|]eqn:WORD; [|discriminate]; destruct value; try discriminate.
      destruct(tensor_observe_dimensions sources temps)as [tail|]eqn:TAIL; [|discriminate].
      inversion OBSERVE; subst dimensions; destruct(IH _ eq_refl)as [VIEW RANGE]; split; constructor; try assumption.
      * cbn [tensor_dimension_value]; rewrite Int.repr_signed; exact WORD.
      * apply Int.signed_range.
Qed.
Lemma tensor_observed_guard_words entry sources dimensions :
  tensor_observe_dimensions sources(entry_temps entry)=Some dimensions ->
  Forall2(tensor_guard_operand entry)(map tensor_dimension_code sources)dimensions.
Proof.
  intro OBSERVE; destruct(@tensor_observe_dimensions_sound sources(entry_temps entry)dimensions OBSERVE)as [VIEW RANGE].
  pose proof(@tensor_dimension_view_evaluation(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    sources dimensions VIEW)as WORDS.
  clear OBSERVE VIEW; revert RANGE; induction WORDS as [|code dimension codes dimensions WORD WORDS IH]; intro RANGE.
  - constructor.
  - inversion RANGE; subst; constructor; [split; assumption|apply IH; assumption].
Qed.
Definition tensor_backend_guard sources := tensor_volume_guard(map tensor_dimension_code sources).
Definition tensor_backend_ready sources entry := exists dimensions,tensor_observe_dimensions sources(entry_temps entry)=Some dimensions.
Definition tensor_backend_layout sources entry := exists dimensions,
  tensor_observe_dimensions sources(entry_temps entry)=Some dimensions /\ tensor_layout_flag dimensions=true.

Lemma tensor_backend_guard_run entry sources dimensions :
  tensor_observe_dimensions sources(entry_temps entry)=Some dimensions ->
  decision_run entry(tensor_backend_guard sources)(tensor_volume_check tensor_volume_cap 1 dimensions).
Proof.
  intro OBSERVE; apply tensor_volume_guard_run; [apply tensor_observed_guard_words; exact OBSERVE| |pose proof tensor_volume_cap_range; lia].
  unfold tensor_operand; split; [reflexivity|split; [constructor|constructor]].
Qed.
Lemma tensor_backend_guard_pure sources : pure_tree(tensor_backend_guard sources).
Proof.
  unfold tensor_backend_guard; apply tensor_volume_guard_pure; [constructor|].
  induction sources as [|source sources IH]; cbn [map]; [constructor|constructor; [|exact IH]].
  destruct source; cbn [tensor_dimension_code]; [unfold ClightRectangularStore.rect_constant; destruct(z <? 0); repeat constructor|constructor].
Qed.
Theorem tensor_backend_guard_accepts entry sources dimensions :
  tensor_observe_dimensions sources(entry_temps entry)=Some dimensions ->
  decision_run entry(tensor_backend_guard sources)true -> tensor_layout_flag dimensions=true.
Proof.
  intros OBSERVE RUN; pose proof(@pure_tree_determinate(tensor_backend_guard sources)(tensor_backend_guard_pure sources)
    entry true(tensor_volume_check tensor_volume_cap 1 dimensions)RUN(@tensor_backend_guard_run entry sources dimensions OBSERVE))as SAME.
  apply tensor_volume_check_layout; symmetry; exact SAME.
Qed.
Definition tensor_backend_guard_condition fe O(observe:fragment_observation->O->Prop)sources :
  readonly_condition(readonly_clight_host fe observe)(tensor_backend_ready sources)(tensor_backend_layout sources)(tensor_backend_guard sources).
Proof.
  constructor.
  - intros entry [dimensions OBSERVE]; eapply pure_decision_run_safe;
      [apply tensor_backend_guard_pure|exact(@tensor_backend_guard_run entry sources dimensions OBSERVE)].
  - intros entry [dimensions OBSERVE]; exists(tensor_volume_check tensor_volume_cap 1 dimensions),entry;
      split; [exact(@tensor_backend_guard_run entry sources dimensions OBSERVE)|reflexivity].
  - intros entry accepted checked [dimensions OBSERVE] [RUN SAME]; split; [exact SAME|].
    intro ACCEPT; subst accepted; exists dimensions; split; [exact OBSERVE|eapply tensor_backend_guard_accepts; eassumption].
Defined.
Theorem tensor_backend_guard_nonalias entry sources dimensions logical_array block base :
  tensor_observe_dimensions sources(entry_temps entry)=Some dimensions -> decision_run entry(tensor_backend_guard sources)true ->
  locations_nonalias(tensor_pointer_locations logical_array block base dimensions).
Proof.
  intros OBSERVE RUN; apply tensor_pointer_locations_nonalias.
  exact(proj2(proj2(@tensor_layout_flag_sound dimensions(@tensor_backend_guard_accepts entry sources dimensions OBSERVE RUN)))).
Qed.

Print Assumptions tensor_observe_dimensions_sound.
Print Assumptions tensor_observed_guard_words.
Print Assumptions tensor_backend_guard_run.
Print Assumptions tensor_backend_guard_accepts.
Print Assumptions tensor_backend_guard_condition.
Print Assumptions tensor_backend_guard_nonalias.
