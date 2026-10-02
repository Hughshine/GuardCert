From Stdlib Require Import List.
From compcert.common Require Import Errors Smallstep Behaviors.
From compcert.cfrontend Require Import Clight Csyntax Csem.
From compcert.driver Require Import Compiler Complements.
From Guard Require Import ClightRegionRewrite ClightNoWrap ClightSignedCancel ClightSameAddress
  ClightRedundantSet ClightFrontendRegion ClightStructuredProgress AdaptiveRegionCompiler.
From Guard Require Import ClightScheduledMatrix.

(** An order is ordinary untrusted optimizer input. Soundness quantifies over
    every well-typed order, including proposals refused by the checker. *)
Definition select_scheduled_regions order (source : Clight.statement) : option Clight.statement :=
  match select_scheduled_matrix order source with
  | Some target => Some target
  | None => match select_loop_zero_trip source with
    | Some target => Some target
    | None => select_redundant_set source end
  end.

Lemma select_scheduled_regions_sound order source target :
  select_scheduled_regions order source = Some target -> region_contract source target.
Proof.
  unfold select_scheduled_regions; destruct (select_scheduled_matrix order source) as [selected|] eqn:SCHEDULE.
  - intro TARGET; inversion TARGET; subst; eapply select_scheduled_matrix_sound; exact SCHEDULE.
  - destruct (select_loop_zero_trip source) as [selected|] eqn:ZERO.
    + intro TARGET; inversion TARGET; subst; eapply select_loop_zero_trip_sound; exact ZERO.
    + apply select_redundant_set_sound.
Qed.

Definition compile_scheduled_regions order := compile_with_adaptive_regions structured_progress_supported
  select_no_wrap select_signed_memory_rewrites (select_scheduled_regions order).

Theorem compile_scheduled_regions_correct : forall order p tp,
  compile_scheduled_regions order p = OK tp ->
  backward_simulation (Csem.semantics p) (Asm.semantics tp).
Proof.
  intro order; unfold compile_scheduled_regions.
  apply compile_with_adaptive_regions_correct.
  - exact structured_progress_supported_sound.
  - exact select_no_wrap_sound.
  - exact (@select_scheduled_regions_sound order).
  - exact select_signed_memory_rewrites_sound.
Qed.

Theorem compile_scheduled_regions_preserves_spec : forall order p tp spec,
  compile_scheduled_regions order p = OK tp ->
  safety_enforcing_specification spec ->
  c_program_satisfies_spec p spec -> asm_program_satisfies_spec tp spec.
Proof.
  intro order; unfold compile_scheduled_regions.
  apply compile_with_adaptive_regions_preserves_spec.
  - exact structured_progress_supported_sound.
  - exact select_no_wrap_sound.
  - exact (@select_scheduled_regions_sound order).
  - exact select_signed_memory_rewrites_sound.
Qed.

Print Assumptions Compiler.transf_c_program_correct.
Print Assumptions compile_scheduled_regions_correct.
