From Stdlib Require Import List ZArith Bool Lia Sorting.Permutation Sorting.Sorted SetoidList.
From polcert.src Require Import PrepareCodegen ExtractorCorrect.
From polcert.polygen Require Import PolIRs Result.
From polcert.src Require Import SelectionSort Base PolyBase.
From polcert.lib Require Import ImpureAlarmConfig Misc Linalg.
From Vpl Require Import Impure.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** Fixed-parameter compositions of the vendored prepared-codegen and
    extractor proofs. No source or target parameter is existentially replaced.
    Collection/sorting below follows PrepareCodegen.prepare_codegen_semantics_correct,
    retaining its explicit environment instead of constructing wrapped semantics. *)
Module PolCertPreparedParameters (IRs : POLIRS).
Module Prepare := PrepareCodegen IRs.
Module Extract := ExtractorCorrect IRs.
Include Prepare.
Local Open Scope nat_scope.

Theorem prepare_codegen_semantics_correct_at pol envv initial final :
  PolyLang.wf_pprog_affine pol ->
  length (snd (fst pol)) = length envv ->
  PolyLang.env_poly_semantics envv (codegen_target_dim pol)
    (fst (fst (prepare_codegen pol))) initial final ->
  PolyLang.poly_instance_list_semantics envv pol initial final.
Proof.
  destruct pol as [[pis varctxt] vars].
  intros Hwf Henvlen Henvsem.
  cbn in Henvlen.
  change (PolyLang.env_poly_semantics envv
    (codegen_target_dim (pis, varctxt, vars))
    (map (prepare_pi (length varctxt) (codegen_target_dim (pis, varctxt, vars))) pis)
    initial final) in Henvsem.
  unfold PolyLang.env_poly_semantics in Henvsem.
  pose proof
    (wf_pprog_affine_implies_pprog_current_dim_le_target
       pis varctxt vars Hwf)
    as Hcurdim.
  set (cols := codegen_target_dim (pis, varctxt, vars)).
  assert (Hdim_cols :
            (PolyLang.pprog_current_dim (pis, varctxt, vars) <= cols)%nat).
  {
    exact Hcurdim.
  }
  destruct
    (prepare_poly_semantics_collect
       pis varctxt vars cols envv
       (PolyLang.env_scan
          (map (prepare_pi (length varctxt) cols) pis)
          envv cols)
       initial final
       Hwf Hdim_cols
       (eq_sym Henvlen) Henvsem (fun _ _ H => H))
    as [exec_ipl [Hexec_sem [Hexec_sched [Hexec_nodup Hexec_char]]]].
  set (ipl := SelectionSort np_ltb np_eqb exec_ipl).
  assert (Hsort :
    Permutation exec_ipl ipl /\
    Sorted_b (combine_leb np_ltb np_eqb) ipl).
  {
    unfold ipl.
    eapply selection_sort_np_is_correct.
    reflexivity.
  }
  destruct Hsort as [Hperm_exec Hsortedb].
  assert (Hipl_nodup : NoDup ipl).
  {
    eapply Permutation_NoDup; eauto.
  }
  assert (Hipl_source :
    forall ip,
      In ip ipl ->
      exists n pi,
        nth_error pis n = Some pi /\
        firstn (length varctxt) (PolyLang.ip_index ip) = envv /\
        PolyLang.belongs_to ip pi /\
        PolyLang.ip_nth ip = n /\
        length (PolyLang.ip_index ip) = length varctxt + pi.(PolyLang.pi_depth)).
  {
    intros ip Hin.
    assert (Hin_exec : In ip exec_ipl).
    {
      eapply Permutation_in.
      - apply Permutation_sym. exact Hperm_exec.
      - exact Hin.
    }
    destruct (Hexec_char ip) as [Hchar_forw _].
    destruct (Hchar_forw Hin_exec) as [n0 [p [pi [Hnth [Hscan Hip]]]]].
    subst ip.
    pose proof
      (prepare_env_scan_true_implies_source_ip_props
         pis varctxt vars cols envv n0 p pi
         Hwf Hdim_cols (eq_sym Henvlen) Hnth Hscan)
      as Hprops.
    destruct Hprops as [Hpref [Hbel [Hlen [_ _]]]].
    exists n0.
    exists pi.
    split; [exact Hnth|].
    split; [exact Hpref|].
    split; [exact Hbel|].
    split.
    - apply source_ip_of_nth.
    - exact Hlen.
  }
  assert (Hipl_nodupa : NoDupA PolyLang.np_eq ipl).
  {
    eapply source_like_points_imply_NoDupA_np; eauto.
  }
  assert (Hipl_sorted : Sorted PolyLang.np_lt ipl).
  {
    eapply sortedb_np_nodup_implies_sorted_np; eauto.
  }
  assert (Hflat : PolyLang.flatten_instrs envv pis ipl).
  {
    split.
    - intros ip Hin.
      destruct (Hipl_source ip Hin)
        as [n [pi [Hnth [Hpref [Hbel [Hn Hlen]]]]]].
      rewrite <- Henvlen.
      exact Hpref.
    - split.
      + intros ip.
        split.
        * intros Hin.
          destruct (Hipl_source ip Hin)
            as [n [pi [Hnth [Hpref [Hbel [Hn Hlen]]]]]].
          exists pi.
          rewrite Hn.
          split; [exact Hnth|].
          split.
          { rewrite <- Henvlen. exact Hpref. }
          split.
          { exact Hbel. }
          { rewrite <- Henvlen. exact Hlen. }
        * intros [pi [Hnth [Hpref [Hbel Hlen]]]].
          rewrite <- Henvlen in Hpref.
          rewrite <- Henvlen in Hlen.
          assert (Hscan :
            PolyLang.env_scan
              (map (prepare_pi (length varctxt) cols) pis)
              envv cols (PolyLang.ip_nth ip) (PolyLang.ip_index ip) = true).
          {
            eapply source_ip_props_imply_prepare_env_scan_true; eauto.
          }
          assert (Hin_exec : In ip exec_ipl).
          {
            destruct (Hexec_char ip) as [_ Hchar_back].
            apply Hchar_back.
            exists ip.(PolyLang.ip_nth).
            exists ip.(PolyLang.ip_index).
            exists pi.
            split; [exact Hnth|].
            split; [exact Hscan|].
            symmetry.
            eapply source_ip_of_self; eauto.
          }
          eapply Permutation_in.
          { exact Hperm_exec. }
          { exact Hin_exec. }
      + split.
        * exact Hipl_nodup.
        * exact Hipl_sorted.
  }
  eapply PolyLang.PolyPointListSema with (ipl := ipl) (sorted_ipl := exec_ipl).
  - reflexivity.
  - exact Hflat.
  - apply Permutation_sym. exact Hperm_exec.
  - exact Hexec_sched.
  - exact Hexec_sem.
Qed.


Theorem prepared_codegen_raw_correct_at pol envv initial final generated :
  mayReturn (prepared_codegen_raw pol) generated ->
  PolyLang.wf_pprog_affine pol ->
  length (snd (fst pol)) = length envv ->
  Loop.loop_semantics (fst (fst generated)) envv initial final ->
  PolyLang.poly_instance_list_semantics (rev envv) pol initial final.
Proof.
  destruct pol as [[pis varctxt] vars].
  intros Hcodegen Hwf Henvlen Hloop.
  cbn in Henvlen.
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
  eapply mayReturn_pure in Hcodegen. subst generated.
  cbn in Hloop.
  assert (Hvarctxt : (es <= n)%nat).
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
          (codegen_target_dim (prepare_codegen (pis, varctxt, vars)))
          prep_pis) loop_stmt) in Hgen.
  pose proof Hvarctxt as Hctxt_gen.
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
	        es (codegen_target_dim (prepare_codegen (pis, varctxt, vars)))
                prep_pis envv initial final Hctxt_gen loop_stmt Hgen Hloop) as Hpoly.
  eapply prepare_codegen_semantics_correct_at.
  - exact Hwf.
  - rewrite rev_length. exact Henvlen.
  - change (CodeGen.PolyLang.env_poly_semantics (rev envv)
      (codegen_target_dim (pis, varctxt, vars)) prep_pis initial final).
    rewrite <- Hprepdim.
    eapply Hpoly.
    + symmetry. exact Henvlen.
    + exact Hdim_gen.
    + exact Henvdim_gen.
    + exact Hsched_gen.
Qed.

Theorem prepared_codegen_correct_at pol envv initial final generated :
  mayReturn (prepared_codegen pol) generated ->
  PolyLang.wf_pprog_affine pol ->
  length (snd (fst pol)) = length envv ->
  Loop.loop_semantics (fst (fst generated)) envv initial final ->
  PolyLang.poly_instance_list_semantics (rev envv) pol initial final.
Proof.
  intros GENERATED WF LENGTH EXEC.
  unfold prepared_codegen in GENERATED.
  bind_imp_destruct GENERATED raw RAW.
  apply mayReturn_pure in GENERATED; subst generated.
  destruct raw as [[body context] variables].
  change (Loop.loop_semantics (Cleanup.cleanup_stmt_pass body) envv initial final) in EXEC.
  pose proof (proj1 (Cleanup.cleanup_stmt_pass_semantics body envv initial final) EXEC) as RUN.
  exact (@prepared_codegen_raw_correct_at pol envv initial final
    (body, context, variables) RAW WF LENGTH RUN).
Qed.

Theorem extractor_correct_at loop pol envv initial final :
  Extract.extractor loop = Okk pol ->
  length (snd (fst loop)) = length envv ->
  PolyLang.poly_instance_list_semantics (rev envv) pol initial final ->
  exists result, Loop.loop_semantics (fst (fst loop)) envv initial result /\ State.eq final result.
Proof.
  destruct loop as [[body context] variables].
  intros EXTRACT LENGTH EXEC.
  pose proof (Extract.extractor_success_implies_wf_scop _ _ _ _ EXTRACT) as WF.
  apply Extract.extractor_success_inv in EXTRACT.
  destruct EXTRACT as [pis [EXTRACT [WFCHECK SAME]]]; subst pol.
  apply Extract.poly_instance_list_semantics_inv in EXEC.
  destruct EXEC as [pis' [context' [variables' [points [ordered [SAME [FLAT [PERM [SORT EXEC]]]]]]]]].
  inversion SAME; subst pis' context' variables'.
  destruct (Extract.extract_stmt_to_loop_semantics_core_sched_constrs
    body [] [] context variables pis (rev envv) points ordered initial final
    WF EXTRACT eq_refl WFCHECK FLAT PERM SORT EXEC) as [result [RUN EQUAL]].
  - rewrite rev_length. symmetry. exact LENGTH.
  - rewrite rev_involutive in RUN. exists result; auto.
Qed.

Print Assumptions prepare_codegen_semantics_correct_at.
Print Assumptions prepared_codegen_raw_correct_at.
Print Assumptions prepared_codegen_correct_at.
Print Assumptions extractor_correct_at.

End PolCertPreparedParameters.
