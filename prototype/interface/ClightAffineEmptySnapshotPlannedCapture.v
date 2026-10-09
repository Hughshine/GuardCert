From Stdlib Require Import List Bool.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightGuard ClightPrivateRegion
  ClightRegionProgress ClightTempFootprint ClightStraightLine ClightLoopSyntax CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax.
From GuardInterface Require Import ClightAffineSnapshotSyntax ClightAffineSnapshotCaptureCandidate
  ClightAffineZeroSnapshotPreparation ClightAffineEmptyWidth ClightAffineEmptySnapshotCondition
  ClightAffineEmptySnapshotRewrite ClightAffineEmptySnapshotCapture ClightAffineOuterEmpty
  ClightSourceObservation ClightCheckPlanFrame ClightReadonlyAlternativePlan.
Set Implicit Arguments.

Definition affine_empty_snapshot_plan original(site:affine_snapshot_source_package original)width :=
  let shape:=affine_inner_pointer_shape(snapshot_cached_package site)in
  readonly_alternative_plan(affine_outer_empty_tree(affine_inner_pointer_row shape)(affine_inner_pointer_bound shape))
    (affine_empty_snapshot_tree site width).
Definition affine_empty_snapshot_planned_yes original(site:affine_snapshot_source_package original) :=
  let shape:=affine_inner_pointer_shape(snapshot_cached_package site)in
  readonly_alternative_yes(affine_outer_empty_tree(affine_inner_pointer_row shape)(affine_inner_pointer_bound shape))
    (affine_empty_snapshot_restore site).
Definition affine_empty_snapshot_planned_captured original(site:affine_snapshot_source_package original)width result :=
  Ssequence(affine_snapshot_capture_statement site)
    (ClightCheckPlan.check_plan_guarded_statement(affine_empty_snapshot_plan site width)result
      (affine_empty_snapshot_planned_yes site)original).

Section CAPTURE.
Variable original : statement.
Variable site : affine_snapshot_source_package original.
Variable live : list ident.
Variable capture : affine_snapshot_capture_package site live.
Let package:=snapshot_cached_package site.
Variable width : decision_tree.
Hypothesis WIDTH : compile_affine_empty_width
  (affine_inner_pointer_row(affine_inner_pointer_shape package))
  (memory_affine_inner_pointer_header(affine_inner_pointer_shape package)(affine_inner_pointer_expression package))
  (affine_zero_snapshot_header_bounds site)(affine_inner_pointer_expression package)=Some width.
Variable result : ident.
Hypothesis RESOURCES : check_plan_resources(affine_empty_snapshot_plan site width)result live
  (affine_empty_snapshot_planned_yes site)original=true.

(** The old execution is a proof witness, not code executed by the target.
    The original-source receipt still supplies capture definedness. *)
Theorem affine_empty_snapshot_planned_captured_execution fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory original E0 after final Out_normal ->
  exists target,exec_stmt fe ge locals temps memory(affine_empty_snapshot_planned_captured site width result)
    E0 target final Out_normal /\ temp_agree live after target.
Proof.
  intro SOURCE.
  destruct(@affine_empty_snapshot_captured_execution original site live capture width WIDTH
    fe ge locals temps memory after final SOURCE)as [old[RUN PUBLIC]].
  unfold affine_empty_snapshot_captured in RUN.
  destruct(sequence_normal_decode RUN)as [checked[checked_memory[CAPTURE SELECT]]].
  unfold affine_empty_snapshot_guarded in SELECT.
  destruct(@readonly_alternative_planned_execution fe ge locals checked checked_memory
    (affine_outer_empty_tree(affine_inner_pointer_row(affine_inner_pointer_shape package))
      (affine_inner_pointer_bound(affine_inner_pointer_shape package)))
    (affine_empty_snapshot_tree site width)result live(affine_empty_snapshot_restore site)original
    old final RESOURCES SELECT)as [target[EXECUTE FRAME]].
  exists target; split.
  - unfold affine_empty_snapshot_planned_captured,affine_empty_snapshot_plan,affine_empty_snapshot_planned_yes,
      readonly_alternative_statement in *.
    eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); eassumption.
  - eapply temp_agree_trans; eassumption.
Qed.

Theorem affine_empty_snapshot_planned_prefix_contract loads :
  PrivateRegion.projected_region_contract live(Ssequence(source_load_prefix loads)original)
    (Ssequence(source_load_prefix loads)(affine_empty_snapshot_planned_captured site width result)).
Proof.
  apply source_prefix_region_contract with
    (writes:=source_load_targets loads++statement_temps original)(domain:=fun _=>True).
  - apply source_load_prefix_supported.
  - apply writes_sequence.
    + eapply writes_only_weaken; [intros id MEMBER; apply in_or_app; left; exact MEMBER|apply source_load_prefix_writes].
    + eapply writes_only_weaken; [intros id MEMBER; apply in_or_app; right; exact MEMBER|].
      apply check_plan_frameable_writes; exact(snapshot_capture_frameable capture).
  - intros; exact I.
  - intros temps p locals entry memory after final SCOPE DOMAIN SOURCE.
    destruct(@affine_empty_snapshot_planned_captured_execution(adapter_entry temps)(globalenv p)locals entry memory
      after final SOURCE)as [target[EXECUTE PUBLIC]].
    exists target,final; split; [exact EXECUTE|split; [exact PUBLIC|apply memory_equivalent_refl]].
Qed.
End CAPTURE.

Print Assumptions affine_empty_snapshot_planned_captured_execution.
Print Assumptions affine_empty_snapshot_planned_prefix_contract.
