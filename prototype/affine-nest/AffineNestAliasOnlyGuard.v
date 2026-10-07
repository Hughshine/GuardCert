From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap.
From GuardMemory Require Import GuardMemoryBooleanScan GuardMemoryWindowCells.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage
  AffineNestPackageGuard AffineNestPackageWords AffineNestMultiStaticPackage AffineNestMultiPresumption
  AffineNestPackageScanFootprint AffineNestPackageScanAccesses AffineNestScanAccesses AffineNestScanAll
  AffineNestScanModel AffineNestScanPoints AffineNestScanSeparation AffineNestMathDomain.
Import ListNotations.
Set Implicit Arguments.

(** Residual guard after a certified numeric check. The precondition is a
    semantic fact at this entry, not an unchecked optimizer assertion. *)
Definition affine_multi_alias_only_code source parameters live allocated proposal
  (package:affine_multi_static_package source parameters live allocated proposal) :=
  affine_scan_all_code(affine_proposal_nest proposal)(affine_proposal_rename proposal)
    (affine_multi_right_controls proposal allocated)(affine_proposed_result proposal)
    (Etempvar(affine_proposed_iterator proposal) type_int32s)
    (affine_scan_accesses(affine_proposed_operations proposal)).

Theorem affine_multi_alias_only_execution source parameters live allocated proposal
  (package:affine_multi_static_package source parameters live allocated proposal)
  fe ge locals temps memory source_after source_final :
  exec_stmt fe ge locals temps memory source E0 source_after source_final Out_normal ->
  affine_package_guard_flag parameters proposal(Entry ge locals temps memory)=true ->
  temps!(affine_proposed_result proposal)=Some(memory_boolean_word true) ->
  exists after,
    exec_stmt fe ge locals temps memory(affine_multi_alias_only_code package) E0 after memory Out_normal /\
    temp_agree live temps after /\
    after!(affine_proposed_result proposal)=Some(memory_boolean_word
      (affine_multi_guard_flag parameters proposal(Entry ge locals temps memory))).
Proof.
  intros SOURCE NUMERIC FLAG.
  destruct(@affine_package_guard_execution source parameters live proposal(affine_multi_guard package)
    fe ge locals temps memory source_after source_final SOURCE) as [unused [_ [_ [_ DOMAIN]]]].
  specialize(DOMAIN NUMERIC).
  pose proof(@affine_package_accepted_word_view source parameters live proposal(affine_multi_guard package)
    fe ge locals temps memory source_after source_final NUMERIC SOURCE) as WORDS.
  destruct(@affine_package_root_words source parameters live proposal(affine_multi_guard package)
    fe ge locals temps memory source_after source_final SOURCE) as [[root_word ROOT_WORD] [bound_word BOUND_WORD]].
  pose proof(@affine_package_scan_capabilities source parameters live proposal(affine_multi_guard package)
    (affine_multi_source_loop package) fe ge locals temps memory source_after source_final(affine_multi_pointer_private package)
    (affine_multi_source_lower package) NUMERIC SOURCE) as CAPABLE.
  unfold affine_multi_alias_only_code,affine_multi_guard_flag; rewrite NUMERIC.
  unfold affine_multi_alias_result; eapply affine_scan_all_execution with
    (left_names:=affine_multi_left_namespace package)(right_names:=affine_multi_right_namespace package)
    (original:=temps)(valuation:=affine_word_valuation temps)(bounds:=affine_proposed_leaf_bounds proposal)
    (layout:=affine_proposal_layout proposal parameters)(accepted:=true); try eassumption.
  - pose proof(described_affine_dependencies(affine_package_description(affine_multi_guard package))) as DEPENDENCIES.
    rewrite(affine_package_nest(affine_multi_guard package)) in DEPENDENCIES; exact DEPENDENCIES.
  - exact(affine_multi_parameters_public package).
  - exact(affine_multi_root_public package).
  - exact(affine_multi_window_low package).
  - exact(affine_multi_window_high package).
  - unfold affine_word_valuation,temp_word; rewrite ROOT_WORD; cbn; rewrite Int.repr_signed,ROOT_WORD; reflexivity.
  - apply temp_agree_refl.
  - intros access MEMBER; split.
    + apply(affine_multi_pointer_public package); exact(proj1(affine_package_scan_access(affine_multi_guard package) access MEMBER)).
    + intros identifier READ; exact(@affine_package_scan_access_reads source parameters live proposal
        (affine_multi_guard package) access identifier MEMBER READ).
  - intros point POINT; apply Forall_forall; intros cell MEMBER.
    apply Forall_forall with(x:=cell) in CAPABLE; [exact CAPABLE|].
    unfold affine_package_scan_cells,affine_scan_cells; apply in_flat_map; exists point; split;
      [apply affine_scan_points_exact; exact POINT|exact MEMBER].
Qed.

Print Assumptions affine_multi_alias_only_execution.
