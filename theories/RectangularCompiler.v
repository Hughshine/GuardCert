From compcert.common Require Import Errors Smallstep Behaviors.
From compcert.cfrontend Require Import Clight Csyntax Csem.
From compcert.driver Require Import Compiler Complements.
From Guard Require Import ClightGuard ClightNoWrap ClightCondition ClightTreeExamples
  ClightSameAddress ClightSignedCancel ClightRegionRewrite ClightStructuredProgress
  AdaptiveRegionCompiler ClightRectangularSelector ClightRectangularUpdateSelector ClightRectangularRowSelector.

Definition select_rectangular_regions (source : Clight.statement) : option Clight.statement :=
  match select_rectangle_interchange source with
  | Some target => Some target
  | None => match select_rectangle_update_interchange source with
    | Some target => Some target
    | None => match select_rectangle_row_update_interchange source with
      | Some target => Some target | None => select_progress_regions source end end
  end.
Lemma select_rectangular_regions_sound source target :
  select_rectangular_regions source = Some target -> region_contract source target.
Proof.
  unfold select_rectangular_regions; destruct (select_rectangle_interchange source) as [selected|] eqn:RECT.
  - intro TARGET; inversion TARGET; subst; eapply select_rectangle_interchange_sound; exact RECT.
  - destruct (select_rectangle_update_interchange source) as [selected|] eqn:UPDATE.
    + intro TARGET; inversion TARGET; subst; eapply select_rectangle_update_interchange_sound; exact UPDATE.
    + destruct (select_rectangle_row_update_interchange source) as [selected|] eqn:ROW.
      * intro TARGET; inversion TARGET; subst; eapply select_rectangle_row_update_interchange_sound; exact ROW.
      * apply select_progress_regions_sound.
Qed.

Definition compile_rectangular_regions := compile_with_adaptive_regions structured_progress_supported
  select_no_wrap select_signed_memory_rewrites select_rectangular_regions.
Corollary compile_rectangular_regions_correct : forall p tp,
  compile_rectangular_regions p = OK tp ->
  backward_simulation (Csem.semantics p) (Asm.semantics tp).
Proof.
  apply compile_with_adaptive_regions_correct; auto using structured_progress_supported_sound,
    select_no_wrap_sound, select_signed_memory_rewrites_sound, select_rectangular_regions_sound.
Qed.
Corollary compile_rectangular_regions_preserves_spec : forall p tp spec,
  compile_rectangular_regions p = OK tp -> safety_enforcing_specification spec ->
  c_program_satisfies_spec p spec -> asm_program_satisfies_spec tp spec.
Proof.
  apply compile_with_adaptive_regions_preserves_spec; auto using structured_progress_supported_sound,
    select_no_wrap_sound, select_signed_memory_rewrites_sound, select_rectangular_regions_sound.
Qed.

Print Assumptions Compiler.transf_c_program_correct.
Print Assumptions compile_rectangular_regions_correct.
