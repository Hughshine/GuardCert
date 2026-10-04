From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryWindowCells GuardMemoryBooleanScan GuardMemoryNaryAffineAccess GuardMemoryFootprintCapabilities.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestPackageGuard
  AffineNestPackageWords AffineNestDomainGuard AffineNestMultiStaticPackage AffineNestMultiPresumption
  AffineNestPackageScanFootprint AffineNestPackageScanAccesses AffineNestScanAccesses AffineNestScanAll
  AffineNestScanModel AffineNestScanPoints AffineNestScanSeparation.
Import ListNotations.
Set Implicit Arguments.

Definition affine_multi_guard_code source parameters live allocated proposal
  (package:affine_multi_static_package source parameters live allocated proposal) :=
  Ssequence(affine_package_guard_code(affine_multi_guard package))
    (Sifthenelse(Etempvar(affine_proposed_result proposal) type_int32s)
      (affine_scan_all_code(affine_proposal_nest proposal)(affine_proposal_rename proposal)
        (affine_multi_right_controls proposal allocated)(affine_proposed_result proposal)
        (Etempvar(affine_proposed_iterator proposal) type_int32s)(affine_scan_accesses(affine_proposed_operations proposal))) Sskip).

Theorem affine_multi_guard_execution source parameters live allocated proposal
  (package:affine_multi_static_package source parameters live allocated proposal) fe ge locals temps memory source_after source_final :
  exec_stmt fe ge locals temps memory source E0 source_after source_final Out_normal ->
  exists after,
    exec_stmt fe ge locals temps memory(affine_multi_guard_code package) E0 after memory Out_normal /\
    temp_agree live temps after /\
    after!(affine_proposed_result proposal)=Some(memory_boolean_word
      (affine_multi_guard_flag parameters proposal(Entry ge locals temps memory))).
Proof.
  intro SOURCE.
  destruct(@affine_package_guard_execution source parameters live proposal(affine_multi_guard package)
    fe ge locals temps memory source_after source_final SOURCE) as [guarded [GUARD [PUBLIC [FLAG DOMAIN]]]].
  set(numeric:=affine_package_guard_flag parameters proposal(Entry ge locals temps memory)) in *.
  assert(FRAME:temp_agree live temps guarded).
  { eapply temp_agree_weaken; [|exact PUBLIC]; intros identifier MEMBER; repeat rewrite in_app_iff; auto. }
  destruct(@affine_probe_result_test(affine_proposed_result proposal) numeric ge locals guarded memory FLAG) as [value [EVAL BOOL]].
  assert(SELECTED:exists after,
    exec_stmt fe ge locals guarded memory
      (if numeric then affine_scan_all_code(affine_proposal_nest proposal)(affine_proposal_rename proposal)
        (affine_multi_right_controls proposal allocated)(affine_proposed_result proposal)
        (Etempvar(affine_proposed_iterator proposal) type_int32s)(affine_scan_accesses(affine_proposed_operations proposal)) else Sskip)
      E0 after memory Out_normal /\ temp_agree live guarded after /\
    after!(affine_proposed_result proposal)=Some(memory_boolean_word(numeric&&affine_multi_alias_result proposal temps))).
  { destruct numeric eqn:ACCEPT.
    - specialize(DOMAIN eq_refl).
      pose proof(@affine_package_accepted_word_view source parameters live proposal(affine_multi_guard package)
        fe ge locals temps memory source_after source_final ACCEPT SOURCE) as WORDS.
      destruct(@affine_package_root_words source parameters live proposal(affine_multi_guard package)
        fe ge locals temps memory source_after source_final SOURCE) as [[root_word ROOT_WORD] [bound_word BOUND_WORD]].
      pose proof(@affine_package_scan_capabilities source parameters live proposal(affine_multi_guard package)
        (affine_multi_source_loop package) fe ge locals temps memory source_after source_final(affine_multi_pointer_private package)
        (affine_multi_source_lower package) ACCEPT SOURCE) as CAPABLE.
      unfold affine_multi_alias_result; eapply affine_scan_all_execution with
        (left_names:=affine_multi_left_namespace package)(right_names:=affine_multi_right_namespace package)
        (original:=temps)(valuation:=affine_word_valuation temps)(bounds:=affine_proposed_leaf_bounds proposal)
        (layout:=affine_proposal_layout proposal parameters); try eassumption.
      + pose proof(described_affine_dependencies(affine_package_description(affine_multi_guard package))) as DEPENDENCIES.
        rewrite(affine_package_nest(affine_multi_guard package)) in DEPENDENCIES; exact DEPENDENCIES.
      + exact(affine_multi_parameters_public package).
      + exact(affine_multi_root_public package).
      + exact(affine_multi_window_low package).
      + exact(affine_multi_window_high package).
      + unfold affine_word_valuation,temp_word; rewrite ROOT_WORD; cbn; rewrite Int.repr_signed; reflexivity.
      + intros access MEMBER; split.
        * apply(affine_multi_pointer_public package); exact(proj1(affine_package_scan_access(affine_multi_guard package) access MEMBER)).
        * intros identifier READ; exact(@affine_package_scan_access_reads source parameters live proposal
            (affine_multi_guard package) access identifier MEMBER READ).
      + intros point POINT; apply Forall_forall; intros cell MEMBER.
        apply Forall_forall with(x:=cell) in CAPABLE; [exact CAPABLE|].
        unfold affine_package_scan_cells,affine_scan_cells; apply in_flat_map; exists point; split;
          [apply affine_scan_points_exact; exact POINT|exact MEMBER].
    - exists guarded; repeat split; auto using exec_Sskip,temp_agree_refl. }
  destruct SELECTED as [after [RUN [AFTER RESULT]]]; exists after; split.
  - unfold affine_multi_guard_code; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact GUARD|].
    eapply exec_Sifthenelse with(v1:=value)(b:=numeric); eassumption.
  - split; [eapply temp_agree_trans; eassumption|exact RESULT].
Qed.
Print Assumptions affine_multi_guard_execution.
