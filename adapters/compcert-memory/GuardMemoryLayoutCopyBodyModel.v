From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightStraightLine ClightLoopSyntax ClightRegionProgress ClightRectangularStore ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryRegistryBackend
  GuardMemoryParametricBody GuardMemoryCommonLayout GuardMemoryLayoutCopy GuardMemoryLayoutCopyInstruction
  GuardMemoryLayoutCopyRegistry GuardMemoryCopyLayoutRegistry.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Lemma memory_layout_copy_common_points write_shape read_shape i j :
  rectangle_layout_valid write_shape -> rectangle_layout_valid read_shape ->
  0 <= i < rectangle_outer_limit (memory_common_layout write_shape read_shape) ->
  0 <= j < rectangle_stride (memory_common_layout write_shape read_shape) ->
  0 <= i*rectangle_stride write_shape+j < rectangle_extent write_shape /\
  0 <= i*rectangle_stride read_shape+j < rectangle_extent read_shape.
Proof.
  intros WVALID RVALID I J.
  pose proof (rectangle_limits (memory_common_layout_valid WVALID RVALID)) as [_ [_ [POSITIVE LIMIT]]].
  eapply memory_common_layout_points; eauto; lia.
Qed.
Definition memory_layout_copy_body_model write_shape read_shape write_array read_array row column body
  (WVALID : rectangle_layout_valid write_shape) (RVALID : rectangle_layout_valid read_shape)
  (COMPATIBLE : memory_copy_layout_compatible write_shape read_shape write_array read_array)
  (BODY : flatten_region body = [memory_layout_copy_statement write_shape read_shape write_array read_array row column]) :
  memory_parametric_body_model (memory_common_layout write_shape read_shape) row column body.
Proof.
  refine {| parametric_body_descriptors := memory_copy_layout_descriptors write_shape read_shape write_array read_array;
    parametric_body_instructions := [memory_layout_copy_instruction write_shape read_shape write_array read_array];
    parametric_body_point := fun ge locals i j => memory_layout_copy_point ge locals write_shape read_shape write_array read_array i j |}.
  - apply flatten_normal_certificate; rewrite BODY; constructor; [reflexivity|constructor].
  - apply flatten_quiet_certificate; rewrite BODY; constructor; [reflexivity|constructor].
  - apply flatten_writes_certificate; rewrite BODY; constructor; constructor.
  - intros fe ge locals le before after final i j I J ROW COLUMN RUN.
    destruct (@memory_layout_copy_common_points write_shape read_shape i j WVALID RVALID I J) as [WINDEX RINDEX].
    apply (@flattened_singleton_execution fe ge locals body
      (memory_layout_copy_statement write_shape read_shape write_array read_array row column)
      le before after final BODY) in RUN.
    destruct (@memory_layout_copy_statement_inverse write_shape read_shape WVALID RVALID fe ge locals le before
      write_array read_array row column i j E0 after final Out_normal ROW COLUMN WINDEX RINDEX RUN)
      as [wb [rb [WB [RB [TRACE [TEMPS [OUT ACT]]]]]]].
    split; [exists wb,rb; auto|exact TEMPS].
  - intros; eapply memory_copy_layout_registry; eassumption.
  - intros entries ge locals i j before after ARRAYS UNIQUE I J.
    destruct (@memory_layout_copy_common_points write_shape read_shape i j WVALID RVALID I J) as [WINDEX RINDEX].
    rewrite parametric_body_singleton_point; apply memory_copy_layout_point_execution; assumption.
Defined.
Print Assumptions memory_layout_copy_body_model.
