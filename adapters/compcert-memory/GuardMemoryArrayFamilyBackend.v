From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightRectangularStore ClightCondition ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryPolyhedral GuardMemoryArrayBackend.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition same_array_layout base shape :=
  rectangle_extent shape = rectangle_extent base /\ rectangle_stride shape = rectangle_stride base.
Definition same_array_layout_check base shape :=
  (rectangle_extent shape =? rectangle_extent base) && (rectangle_stride shape =? rectangle_stride base).
Lemma same_array_layout_check_sound base shape :
  same_array_layout_check base shape = true -> same_array_layout base shape.
Proof. unfold same_array_layout_check,same_array_layout; rewrite andb_true_iff,!Z.eqb_eq; tauto. Qed.
Lemma same_array_layout_valid base shape :
  rectangle_layout_valid base -> same_array_layout base shape -> rectangle_layout_valid shape.
Proof.
  intros VALID [EXTENT STRIDE]; unfold rectangle_layout_valid in *; rewrite EXTENT,STRIDE; exact VALID.
Qed.
Fixpoint lower_array_family shapes array logical_array instruction codes : option statement :=
  match shapes with
  | [] => None
  | shape::rest => match lower_array_write shape array logical_array instruction codes with
    | Some code => Some code | None => lower_array_family rest array logical_array instruction codes end
  end.
Lemma lower_array_family_member shapes array logical_array instruction codes code :
  lower_array_family shapes array logical_array instruction codes = Some code ->
  exists shape, In shape shapes /\ lower_array_write shape array logical_array instruction codes = Some code.
Proof.
  induction shapes; cbn; [discriminate|].
  destruct (lower_array_write a array logical_array instruction codes) as [first|] eqn:FIRST.
  - intro EQ; inversion EQ; subst first; exists a; auto.
  - intro COMPILE; destruct (IHshapes COMPILE) as [shape [MEMBER LOWER]]; exists shape; auto.
Qed.

Section FAMILY.
Variable base : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid base.
Variable shapes : list rectangle_shape.
Hypothesis LAYOUTS : Forall (same_array_layout base) shapes.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable array logical_array : ident.
Variable block : Values.block.
Hypothesis ARRAY : rect_array_binding base ge locals array block.

Definition array_family_backend : MemoryBody.instruction_backend fe ge locals
  (array_memory_view base logical_array block).
Proof.
  refine {| MemoryBody.lower_instruction := lower_array_family shapes array logical_array |}.
  intros instruction codes values code temps memory source target writes reads COMPILE OPERANDS RUN VIEW.
  destruct (@lower_array_family_member shapes array logical_array instruction codes code COMPILE)
    as [shape [MEMBER LOWER]].
  rewrite Forall_forall in LAYOUTS; pose proof (LAYOUTS shape MEMBER) as LAYOUT.
  destruct LAYOUT as [EXTENT STRIDE].
  assert (VALID_SHAPE : rectangle_layout_valid shape).
  { eapply same_array_layout_valid; [exact VALID|split; assumption]. }
  assert (ARRAY_SHAPE : rect_array_binding shape ge locals array block).
  { unfold rect_array_binding,rect_array_type; rewrite EXTENT; exact ARRAY. }
  assert (VIEW_SHAPE : array_memory_view shape logical_array block source memory).
  { unfold array_memory_view in *; rewrite EXTENT; exact VIEW. }
  destruct (@MemoryBody.instruction_execution fe ge locals (array_memory_view shape logical_array block)
    (@array_write_backend shape VALID_SHAPE fe ge locals array logical_array block ARRAY_SHAPE)
    instruction codes values code temps memory source target writes reads LOWER OPERANDS RUN VIEW_SHAPE)
    as [final [FINAL EXEC]].
  exists final; split; [|exact EXEC].
  unfold array_memory_view in *; rewrite EXTENT in FINAL; exact FINAL.
Defined.

Definition compile_memory_array_family_loop layout bounds live pool loop :=
  MemoryNested.checked_compile_nested_raw (lower_array_family shapes array logical_array) layout bounds live pool loop.
Theorem compile_memory_array_family_loop_within_correct layout bounds live pool loop code parameters temps source target memory :
  compile_memory_array_family_loop layout bounds live pool loop = Some code ->
  MemoryNested.A.typed_view layout parameters temps -> MemoryNested.A.env_within bounds parameters ->
  GuardMemoryIRs.Loop.loop_semantics loop parameters source target ->
  array_memory_view base logical_array block source memory ->
  exists target_temps target_memory, array_memory_view base logical_array block target target_memory /\
    temp_agree (layout ++ live) temps target_temps /\
    exec_stmt fe ge locals temps memory code E0 target_temps target_memory Out_normal.
Proof.
  unfold compile_memory_array_family_loop,MemoryNested.checked_compile_nested_raw.
  intros COMPILE VIEW WITHIN RUN MEMORY.
  destruct (MemoryNested.scratch_check pool (layout ++ live)) eqn:FRESH; try discriminate.
  eapply MemoryNested.compile_nested_correct with (backend := array_family_backend); eauto.
  apply MemoryNested.scratch_check_sound; exact FRESH.
Qed.
End FAMILY.
Print Assumptions array_family_backend.
Print Assumptions compile_memory_array_family_loop_within_correct.
