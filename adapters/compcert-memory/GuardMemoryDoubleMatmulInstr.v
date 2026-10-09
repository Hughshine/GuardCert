From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers Maps.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.src Require Import PolyBase.
From polcert.lib Require Import Linalg.
From polcert.polygen Require Import Loop.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryValueInstr GuardMemoryDynamicTensorLayout
  GuardMemoryDoubleValue GuardMemoryDoubleLocations GuardMemoryDoubleAssignment GuardMemoryDoubleMatmul.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Module DoubleAssignmentLoop := Loop DoubleAssignmentInstr.
Definition double_matmul_C_access site : AccessFunction :=
  (matmul_C site,[([1;0;0],matmul_padding site);([0;1;0],matmul_padding site)]).
Definition double_matmul_A_access site : AccessFunction :=
  (matmul_A site,[([1;0;0],matmul_padding site);([0;0;1],matmul_padding site)]).
Definition double_matmul_B_access site : AccessFunction :=
  (matmul_B site,[([0;0;1],matmul_padding site);([0;1;0],matmul_padding site)]).
Definition double_matmul_instruction site :=
  MemoryValueInstruction (double_matmul_C_access site)
    [(matmul_beta site,[]);double_matmul_C_access site;(matmul_alpha site,[]);
     double_matmul_A_access site;double_matmul_B_access site] double_matmul_expression.
Definition double_matmul_write_cell site i j :=
  {| arr_id := matmul_C site; arr_index := [i+matmul_padding site;j+matmul_padding site] |}.
Definition double_matmul_read_cells site i j k :=
  [{| arr_id := matmul_beta site; arr_index := [] |};double_matmul_write_cell site i j;
   {| arr_id := matmul_alpha site; arr_index := [] |};
   {| arr_id := matmul_A site; arr_index := [i+matmul_padding site;k+matmul_padding site] |};
   {| arr_id := matmul_B site; arr_index := [k+matmul_padding site;j+matmul_padding site] |}].
Lemma double_matmul_exact_write site i j k :
  exact_cell (value_instruction_write (double_matmul_instruction site)) [i;j;k] = double_matmul_write_cell site i j.
Proof.
  cbn [double_matmul_instruction value_instruction_write double_matmul_C_access exact_cell affine_product dot_product map fst snd].
  unfold double_matmul_write_cell; repeat f_equal; ring.
Qed.
Lemma double_matmul_exact_reads site i j k :
  map (fun access => exact_cell access [i;j;k]) (value_instruction_reads (double_matmul_instruction site)) =
  double_matmul_read_cells site i j k.
Proof.
  cbn [double_matmul_instruction value_instruction_reads double_matmul_C_access double_matmul_A_access double_matmul_B_access
    exact_cell affine_product dot_product map fst snd].
  unfold double_matmul_read_cells, double_matmul_write_cell; repeat f_equal; ring.
Qed.

Lemma double_global_scalar_resolution (ge : genv) (layouts : PTree.t (list Z)) array block :
  Genv.find_symbol ge array = Some block -> layouts ! array = Some [] ->
  global_double_locations ge layouts {| arr_id := array; arr_index := [] |} =
    Some (MemoryLocation Mfloat64 block 0).
Proof. intros SYMBOL LAYOUT; unfold global_double_locations; cbn; rewrite SYMBOL,LAYOUT; reflexivity. Qed.
Lemma double_global_matrix_resolution (ge : genv) (layouts : PTree.t (list Z)) array block extent i j :
  Genv.find_symbol ge array = Some block -> layouts ! array = Some [extent;extent] ->
  0 <= i < extent -> 0 <= j < extent ->
  global_double_locations ge layouts {| arr_id := array; arr_index := [i;j] |} =
    Some (MemoryLocation Mfloat64 block (8*(i*extent+j))).
Proof.
  intros SYMBOL LAYOUT I J; unfold global_double_locations; cbn [arr_id arr_index]; rewrite SYMBOL,LAYOUT.
  cbn [tensor_index tensor_volume].
  rewrite (proj2 (Z.leb_le 0 i) ltac:(lia)), (proj2 (Z.ltb_lt i extent) ltac:(lia)),
    (proj2 (Z.leb_le 0 j) ltac:(lia)), (proj2 (Z.ltb_lt j extent) ltac:(lia)); cbn.
  repeat f_equal; ring.
Qed.
Definition double_matmul_layout_certificate site (layouts : PTree.t (list Z)) :=
  layouts ! (matmul_A site) = Some [matmul_extent site;matmul_extent site] /\
  layouts ! (matmul_B site) = Some [matmul_extent site;matmul_extent site] /\
  layouts ! (matmul_C site) = Some [matmul_extent site;matmul_extent site] /\
  layouts ! (matmul_alpha site) = Some [] /\ layouts ! (matmul_beta site) = Some [].

Theorem double_matmul_registry_resolution ge locals temps site blocks layouts i j k :
  double_matmul_entry ge locals temps site blocks i j k -> double_matmul_layout_certificate site layouts ->
  global_double_locations ge layouts (double_matmul_write_cell site i j) =
    Some (double_matmul_location site (matmul_C_block blocks) i j) /\
  resolve_cells (double_matmul_read_cells site i j k) (global_double_locations ge layouts) =
    Some (double_matmul_locations site blocks i j k).
Proof.
  intros [[_ A] [_ B] [_ C] [_ ALPHA] [_ BETA] IV JV KV PAD I J K SPAN] [LA [LB [LC [LALPHA LBETA]]]].
  assert (CW : global_double_locations ge layouts (double_matmul_write_cell site i j) =
    Some (double_matmul_location site (matmul_C_block blocks) i j)).
  { unfold double_matmul_write_cell, double_matmul_location; eapply double_global_matrix_resolution; eauto. }
  split; [exact CW|].
  unfold double_matmul_read_cells, double_matmul_locations; cbn [resolve_cells].
  rewrite (@double_global_scalar_resolution ge layouts (matmul_beta site) (matmul_beta_block blocks) BETA LBETA), CW,
    (@double_global_scalar_resolution ge layouts (matmul_alpha site) (matmul_alpha_block blocks) ALPHA LALPHA),
    (@double_global_matrix_resolution ge layouts (matmul_A site) (matmul_A_block blocks) (matmul_extent site)
      (i+matmul_padding site) (k+matmul_padding site) A LA I K),
    (@double_global_matrix_resolution ge layouts (matmul_B site) (matmul_B_block blocks) (matmul_extent site)
      (k+matmul_padding site) (j+matmul_padding site) B LB K J).
  reflexivity.
Qed.

Lemma double_assignment_resolved_instruction instruction parameters locations write reads before after :
  locations (exact_cell (value_instruction_write instruction) parameters) = Some write ->
  resolve_cells (map (fun access => exact_cell access parameters) (value_instruction_reads instruction)) locations = Some reads ->
  (DoubleAssignmentInstr.instr_semantics instruction parameters
    [exact_cell (value_instruction_write instruction) parameters]
    (map (fun access => exact_cell access parameters) (value_instruction_reads instruction))
    (RuntimeState locations before) (RuntimeState locations after) <->
   memory_action_run (MemoryAction reads write
     (fun values => compute_double_assignment values (value_instruction_code instruction))) before after).
Proof.
  intros WRITE READ; split.
  - intros [_ [_ [actual_write [actual_reads [ACTUAL_WRITE [ACTUAL_READ [_ RUN]]]]]]].
    cbn [runtime_locations runtime_memory] in ACTUAL_WRITE,ACTUAL_READ,RUN.
    rewrite WRITE in ACTUAL_WRITE; inversion ACTUAL_WRITE; subst actual_write.
    rewrite READ in ACTUAL_READ; inversion ACTUAL_READ; subst actual_reads; exact RUN.
  - intro RUN; split; [reflexivity|]; split; [reflexivity|].
    exists write,reads; repeat split; assumption || reflexivity.
Qed.

Definition double_matmul_loop_body site :=
  DoubleAssignmentLoop.Instr (double_matmul_instruction site)
    [DoubleAssignmentLoop.Var 2;DoubleAssignmentLoop.Var 1;DoubleAssignmentLoop.Var 0].
Theorem double_matmul_loop_body_execution site i j k parameters before after :
  DoubleAssignmentLoop.loop_semantics (double_matmul_loop_body site) (k::j::i::parameters) before after <->
  DoubleAssignmentInstr.instr_semantics (double_matmul_instruction site) [i;j;k]
    [double_matmul_write_cell site i j] (double_matmul_read_cells site i j k) before after.
Proof.
  split; intro RUN.
  - inversion RUN as [inst args env first final writes reads EXEC| | | | | ]; subst.
    change (DoubleAssignmentInstr.instr_semantics (double_matmul_instruction site) [i;j;k] writes reads before after) in EXEC.
    destruct EXEC as [WRITES [READS EXEC]]; rewrite double_matmul_exact_write in WRITES;
      rewrite double_matmul_exact_reads in READS; subst writes reads.
    rewrite double_matmul_exact_write in EXEC.
    unfold DoubleAssignmentInstr.instr_semantics;
      rewrite double_matmul_exact_write,double_matmul_exact_reads; repeat split; assumption || reflexivity.
  - apply DoubleAssignmentLoop.LInstr with (wcs := [double_matmul_write_cell site i j])
      (rcs := double_matmul_read_cells site i j k); exact RUN.
Qed.

Theorem double_matmul_loop_source_bridge fe ge locals temps memory site blocks layouts i j k parameters :
  double_matmul_entry ge locals temps site blocks i j k -> double_matmul_layout_certificate site layouts ->
  forall final,
  (exec_stmt fe ge locals temps memory (double_matmul_body site) E0 temps final Out_normal <->
   DoubleAssignmentLoop.loop_semantics (double_matmul_loop_body site) (k::j::i::parameters)
     (RuntimeState (global_double_locations ge layouts) memory)
     (RuntimeState (global_double_locations ge layouts) final)).
Proof.
  intros ENTRY LAYOUT final; rewrite double_matmul_loop_body_execution.
  rewrite <- (double_matmul_exact_write site i j k), <- (double_matmul_exact_reads site i j k).
  destruct (double_matmul_registry_resolution ENTRY LAYOUT) as [WRITE READ].
  rewrite <- (double_matmul_exact_write site i j k) in WRITE;
    rewrite <- (double_matmul_exact_reads site i j k) in READ.
  rewrite (@double_assignment_resolved_instruction (double_matmul_instruction site) [i;j;k]
    (global_double_locations ge layouts) (double_matmul_location site (matmul_C_block blocks) i j)
    (double_matmul_locations site blocks i j k) memory final WRITE READ).
  change (exec_stmt fe ge locals temps memory (double_matmul_body site) E0 temps final Out_normal <->
    memory_action_run (MemoryAction (double_matmul_locations site blocks i j k)
      (double_matmul_location site (matmul_C_block blocks) i j)
      (fun values => compute_double_assignment values double_matmul_expression)) memory final).
  split.
  - intro RUN; exact (proj2 (proj2 (proj2 (double_matmul_source_decode ENTRY RUN)))).
  - eapply double_matmul_lowered_execution; exact ENTRY.
Qed.

Print Assumptions double_matmul_exact_write.
Print Assumptions double_matmul_exact_reads.
Print Assumptions double_matmul_registry_resolution.
Print Assumptions double_matmul_loop_body_execution.
Print Assumptions double_matmul_loop_source_bridge.
