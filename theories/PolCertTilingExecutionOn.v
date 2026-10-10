From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg ImpureAlarmConfig.
From polcert.src Require Import TilingWitness.
From polcert.polygen Require Import PolIRs.
From Vpl Require Import Impure.
From Guard Require Import PolCertCandidateRepresentation PolCertTilingProgress.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** Complete the existing constructive tiling correspondence at the same
    parameter vector. The legacy existential-parameter theorem is separate. *)
Module Type TILING_PROGRESS (IRs : POLIRS).
Include PolCertTilingProgressFor IRs.
End TILING_PROGRESS.
Module PolCertTilingExecutionOnFor (IRs : POLIRS) (Progress : TILING_PROGRESS IRs).
Module P := Progress.
Module C := PolCertCandidateRepresentationFor P.TV.TilingPolIRs.
Module TP := P.TP.

Lemma tiling_point_contract parameters instructions point :
  C.memory_sequence_valid_point parameters instructions point <->
  P.multiple_program_point parameters instructions point.
Proof.
  unfold C.memory_sequence_valid_point,P.multiple_program_point,P.indexed_valid_point.
  split; intros [instruction [NTH POINT]]; exists instruction; split; try exact NTH.
  - destruct POINT as [PREFIX [BELONG LENGTH]].
    split; [exact PREFIX|]; split; [exact BELONG|]; split; [reflexivity|exact LENGTH].
  - destruct POINT as [PREFIX [BELONG [_ LENGTH]]].
    split; [exact PREFIX|]; split; [exact BELONG|exact LENGTH].
Qed.

Section CORRESPONDENCE.
Variable source candidate : list TP.PolyInstr.
Variable witnesses : list statement_tiling_witness.
Variable context : list TP.ident.
Variable variables : list (TP.ident*TP.Ty.t).
Variable parameters : list Z.
Hypothesis CHECK : P.TV.TilingCheck.check_pprog_tiling_sourceb
  (source,context,variables) (candidate,context,variables) witnesses=true.
Hypothesis LENGTH : length parameters=length context.

Definition tiling_complete_isomorphism : C.memory_point_isomorphism parameters source
  (P.multiple_retiled parameters source candidate witnesses).
Proof.
  refine {| C.point_forward := P.multiple_lift_before parameters source candidate witnesses;
            C.point_backward := P.multiple_project_old parameters source witnesses |}.
  - intros point VALID; apply tiling_point_contract in VALID.
    apply tiling_point_contract.
    exact (proj1 (@P.multiple_lift_shape source candidate witnesses context variables parameters CHECK LENGTH point VALID)).
  - intros point VALID; apply tiling_point_contract in VALID; apply tiling_point_contract.
    exact (@P.multiple_project_shape source candidate witnesses context variables parameters CHECK LENGTH point VALID).
  - intros point VALID; apply tiling_point_contract in VALID.
    exact (proj2 (@P.multiple_lift_shape source candidate witnesses context variables parameters CHECK LENGTH point VALID)).
  - intros point VALID; apply tiling_point_contract in VALID.
    exact (@P.multiple_lift_project source candidate witnesses context variables parameters CHECK LENGTH point VALID).
  - intros point VALID; apply tiling_point_contract in VALID.
    exact (@P.multiple_lift_timestamp source candidate witnesses context variables parameters CHECK LENGTH point VALID).
  - intros point VALID; apply tiling_point_contract in VALID.
    pose proof (@P.multiple_project_shape source candidate witnesses context variables parameters CHECK LENGTH point VALID) as OLD.
    pose proof (@P.multiple_lift_timestamp source candidate witnesses context variables parameters CHECK LENGTH _ OLD) as TIME.
    rewrite (@P.multiple_lift_project source candidate witnesses context variables parameters CHECK LENGTH point VALID) in TIME.
    symmetry; exact TIME.
  - intros point initial final VALID EXEC; apply tiling_point_contract in VALID.
    apply (proj1 (@P.multiple_lift_execution source candidate witnesses context variables parameters CHECK LENGTH point initial final VALID)); exact EXEC.
  - intros point initial final VALID EXEC; apply tiling_point_contract in VALID.
    pose proof (@P.multiple_project_shape source candidate witnesses context variables parameters CHECK LENGTH point VALID) as OLD.
    pose proof (@P.multiple_lift_execution source candidate witnesses context variables parameters CHECK LENGTH _ initial final OLD) as ACTION.
    rewrite (@P.multiple_lift_project source candidate witnesses context variables parameters CHECK LENGTH point VALID) in ACTION.
    apply (proj2 ACTION); exact EXEC.
Defined.

Theorem tiling_complete_execution initial final :
  (TP.poly_instance_list_semantics parameters (source,context,variables) initial final <->
   TP.poly_instance_list_semantics parameters
     (P.multiple_retiled parameters source candidate witnesses,context,variables) initial final).
Proof. exact (@C.memory_point_isomorphism_execution parameters source _ context variables initial final
  tiling_complete_isomorphism (eq_sym LENGTH)). Qed.
End CORRESPONDENCE.

Section EXACT_STATE.
Variable state_eq_exact : forall first second, IRs.State.eq first second -> first=second.
Theorem validated_tiling_execution_internal_at source candidate witnesses context variables parameters initial final :
  length parameters=length context -> IRs.Instr.NonAlias initial ->
  mayReturn (P.validate_memory_tiling_equivalence_internal (source,context,variables)
    (candidate,context,variables) witnesses) true ->
  (TP.poly_instance_list_semantics parameters (source,context,variables) initial final <->
   TP.poly_instance_list_semantics parameters (candidate,context,variables) initial final).
Proof.
  intros LENGTH NONALIAS CHECK; split.
  - eapply P.validated_multiple_tiling_progress_at; eauto.
  - intro RUN; unfold P.validate_memory_tiling_equivalence_internal in CHECK.
    destruct (P.TV.TilingCheck.check_pprog_tiling_sourceb (source,context,variables)
      (candidate,context,variables) witnesses) eqn:SHAPE;
      [|apply mayReturn_pure in CHECK; discriminate].
    bind_imp_destruct CHECK backward BACKWARD; bind_imp_destruct CHECK forward FORWARD.
    apply mayReturn_pure in CHECK; apply andb_true_iff in CHECK as [BACK FOR]; subst backward forward.
    cbn -[P.TV.GeneralValidator.validate_tiling] in BACKWARD.
    rewrite <- LENGTH in BACKWARD.
    destruct (@P.TV.GeneralValidator.validate_tiling_correct'
      (P.multiple_retiled parameters source candidate witnesses,context,variables)
      (candidate,context,variables) context context
      (P.multiple_retiled parameters source candidate witnesses) candidate variables variables
      parameters initial final true BACKWARD eq_refl eq_refl eq_refl (eq_sym LENGTH) NONALIAS RUN)
      as [result [RETILED SAME]].
    apply state_eq_exact in SAME; subst result.
    apply (proj2 (@tiling_complete_execution source candidate witnesses context variables parameters
      SHAPE LENGTH initial final)); exact RETILED.
Qed.
Corollary validated_tiling_execution_at source candidate witnesses context variables parameters initial final :
  length parameters=length context -> IRs.Instr.NonAlias initial ->
  mayReturn (P.validate_memory_tiling_equivalence (source,context,variables)
    (candidate,context,variables) witnesses) true ->
  (IRs.PolyLang.poly_instance_list_semantics parameters (source,context,variables) initial final <->
   IRs.PolyLang.poly_instance_list_semantics parameters (candidate,context,variables) initial final).
Proof.
  intros LENGTH NONALIAS CHECK.
  rewrite <- (P.TV.outer_to_tiling_poly_instance_list_semantics_iff parameters (source,context,variables) initial final).
  rewrite <- (P.TV.outer_to_tiling_poly_instance_list_semantics_iff parameters (candidate,context,variables) initial final).
  exact (@validated_tiling_execution_internal_at
    (map P.TV.outer_to_tiling_pinstr source) (map P.TV.outer_to_tiling_pinstr candidate)
    witnesses context variables parameters initial final LENGTH NONALIAS CHECK).
Qed.
End EXACT_STATE.
End PolCertTilingExecutionOnFor.
