From Guard Require Import PolCertCompat.
Require Import Bool.
Require Import List.
Require Import Permutation.
Require Import SetoidList.
Require Import Sorting.Sorted.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Require Import Base.
Require Import Misc.
Require Import PolyBase.
Require Import PolyLang.
Require Import Linalg.
Require Import LinalgExt.
Require Import ImpureAlarmConfig.
Require Import PolIRs.
Require Import ASTGen.
Require Import CodeGen.
Require Import LoopCleanup.
Require Import LoopSingletonCleanup.
Require Import SelectionSort.
Require Import LibTactics.

From polcert.polygen Require Import Projection.
From polcert.src Require Import PrepareCodegen.
From Guard Require Import ProjectionASTGen ProjectionCodeGen.

(** Reuse the existing dimension preparation and source execution proofs.
    Only raw AST generation depends on the supplied projection service. *)
Module ProjectionPreparedCodegen (PolIRs : POLIRS)
  (ProjectionService : PolyProject CoreAlarmed).
Module Prepared := PrepareCodegen PolIRs.
Import Prepared.
Module ASTGen := ProjectionASTGen PolIRs ProjectionService.
Module CodeGen := ProjectionCodeGen PolIRs ProjectionService.
Definition prepared_codegen_raw (pol: PolyLang.t) : imp Loop.t :=
  CodeGen.codegen (prepare_codegen pol).

Definition prepared_codegen (pol: PolyLang.t) : imp Loop.t :=
  BIND loop <- prepared_codegen_raw pol -;
  pure (Cleanup.cleanup loop).

Theorem prepared_codegen_raw_correct:
  forall pol st st',
    WHEN loop <- prepared_codegen_raw pol THEN
    PolyLang.wf_pprog_affine pol ->
    Loop.semantics loop st st' ->
    PolyLang.instance_list_semantics pol st st'.
Proof.
  intros [[pis varctxt] vars] st st' loop Hcodegen Hwf Hloop.
  pose proof (prepare_codegen_preserves_ready_at (pis, varctxt, vars) Hwf) as Hready.
  pose proof
    (prepare_codegen_target_dim_preserved ((pis, varctxt), vars) Hwf)
    as Hprepdim.
  assert (Hready' : codegen_ready_pprog (prepare_codegen (pis, varctxt, vars))).
  {
    unfold codegen_ready_pprog.
    rewrite Hprepdim.
    exact Hready.
  }
  pose proof
    (codegen_ready_pprog_implies_pprog_current_dim_eq_target
       (prepare_codegen (pis, varctxt, vars)) Hready')
    as Hprepcurdim.
  pose proof (prepare_codegen_preserves_wf_at ((pis, varctxt), vars) Hwf) as Hcgwf.
  destruct Hcgwf as [Hctxt [Hdim Hsched]].
  set (es := length varctxt).
  set (n := codegen_target_dim (pis, varctxt, vars)).
  set (prep_pis := map (prepare_pi es n) pis).
  unfold prepared_codegen_raw in Hcodegen.
  unfold CodeGen.codegen in Hcodegen. simpl in Hcodegen.
  bind_imp_destruct Hcodegen loop_stmt Hgen.
  eapply mayReturn_pure in Hcodegen. subst loop.
  inversion Hloop as
      [loop_ext loop_body ctxt' vars' envv mem1 mem2
       Hloop_ext Hcompat Hnonalias Hinit Hloop_body].
  inversion Hloop_ext; subst.
  assert (Hctxt' : (es <= n)%nat).
  { subst es n. exact Hctxt. }
  assert (Hdim' : ASTGen.pis_have_dimension prep_pis n).
  { subst prep_pis es n. exact Hdim. }
  assert (Hsched' : forall pi, In pi prep_pis -> (poly_nrl pi.(PolyLang.pi_schedule) <= n)%nat).
  { subst prep_pis es n. exact Hsched. }
  assert (Henvdim' :
    forall pi, In pi prep_pis ->
      PolyLang.current_env_dim_in_dim n pi.(PolyLang.pi_point_witness) = es).
  {
    intros pi Hin.
    subst prep_pis es n.
    eapply prepared_pi_current_env_dim_for_codegen; eauto.
  }
  change
    (mayReturn
       (CodeGen.complete_generate_many
          es
          (codegen_target_dim (prepare_codegen (pis, ctxt', vars')))
          prep_pis) loop_body) in Hgen.
  pose proof Hctxt' as Hctxt_gen.
  unfold n in Hctxt_gen.
  rewrite <- Hprepdim in Hctxt_gen.
  pose proof Hdim' as Hdim_gen.
  unfold n in Hdim_gen.
  rewrite <- Hprepdim in Hdim_gen.
  pose proof Hsched' as Hsched_gen.
  unfold n in Hsched_gen.
  rewrite <- Hprepdim in Hsched_gen.
  pose proof Henvdim' as Henvdim_gen.
  unfold n in Henvdim_gen.
  rewrite <- Hprepdim in Henvdim_gen.
  pose proof (CodeGen.complete_generate_many_preserve_sem
	        es (codegen_target_dim (prepare_codegen (pis, ctxt', vars')))
                prep_pis envv st st' Hctxt_gen loop_body Hgen Hloop_body) as Hpoly.
  eapply prepare_codegen_semantics_correct.
  - exact Hwf.
  - econstructor.
    + reflexivity.
    + exact Hcompat.
    + exact Hnonalias.
    + exact Hinit.
    + rewrite Hprepcurdim.
      unfold prepare_codegen, prep_pis, es, n.
      simpl.
      change
        (CodeGen.PolyLang.env_poly_semantics
           (rev envv)
           (codegen_target_dim (prepare_codegen (pis, ctxt', vars')))
           (map
              (prepare_pi (length ctxt')
                 (codegen_target_dim (pis, ctxt', vars'))) pis) st st').
      eapply Hpoly.
      * symmetry.
        eapply Instr.init_env_samelen with (envv := rev envv) in Hinit.
        rewrite rev_length in Hinit. exact Hinit.
      * exact Hdim_gen.
      * exact Henvdim_gen.
      * exact Hsched_gen.
Qed.

Theorem prepared_codegen_correct:
  forall pol st st',
    WHEN loop <- prepared_codegen pol THEN
    PolyLang.wf_pprog_affine pol ->
    Loop.semantics loop st st' ->
    PolyLang.instance_list_semantics pol st st'.
Proof.
  intros pol st st' loop Hcodegen Hwf Hloop.
  unfold prepared_codegen in Hcodegen.
  bind_imp_destruct Hcodegen loop_raw Hraw.
  eapply mayReturn_pure in Hcodegen. subst loop.
  pose proof ((proj1 (Cleanup.cleanup_correct loop_raw st st')) Hloop)
    as Hloop_raw.
  eapply prepared_codegen_raw_correct; eauto.
Qed.

Theorem prepared_codegen_raw_correct_general:
  forall pol st st',
    WHEN loop <- prepared_codegen_raw (PolyLang.current_view_pprog pol) THEN
    PolyLang.wf_pprog_general pol ->
    Loop.semantics loop st st' ->
    PolyLang.instance_list_semantics pol st st'.
Proof.
  intros pol st st' loop Hcodegen Hwf Hloop.
  pose proof
    (PolyLang.wf_pprog_general_current_view_affine pol Hwf)
    as Hwf_cur.
  pose proof
    (prepared_codegen_raw_correct
       (PolyLang.current_view_pprog pol) st st' loop
       Hcodegen Hwf_cur Hloop)
    as Hsem_cur.
  pose proof
    (PolyLang.instance_list_semantics_current_view_iff pol st st' Hwf)
    as Hview.
  apply (proj1 Hview).
  exact Hsem_cur.
Qed.

Theorem prepared_codegen_correct_general:
  forall pol st st',
    WHEN loop <- prepared_codegen (PolyLang.current_view_pprog pol) THEN
    PolyLang.wf_pprog_general pol ->
    Loop.semantics loop st st' ->
    PolyLang.instance_list_semantics pol st st'.
Proof.
  intros pol st st' loop Hcodegen Hwf Hloop.
  pose proof
    (PolyLang.wf_pprog_general_current_view_affine pol Hwf)
    as Hwf_cur.
  pose proof
    (prepared_codegen_correct
       (PolyLang.current_view_pprog pol) st st' loop
       Hcodegen Hwf_cur Hloop)
    as Hsem_cur.
  pose proof
    (PolyLang.instance_list_semantics_current_view_iff pol st st' Hwf)
    as Hview.
  apply (proj1 Hview).
  exact Hsem_cur.
Qed.

End ProjectionPreparedCodegen.
