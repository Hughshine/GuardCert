From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Integers Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryDoubleValue GuardMemoryDoubleLocations
  GuardMemoryDoubleAssignment GuardMemoryLongControl.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** This source template preserves beta*C + (alpha*A)*B and its IEEE operation
    order. It uses the original nested global-array and mixed I64/I32 indices. *)
Record double_matmul_site := DoubleMatmulSite {
  matmul_A : ident; matmul_B : ident; matmul_C : ident;
  matmul_alpha : ident; matmul_beta : ident;
  matmul_i : ident; matmul_j : ident; matmul_k : ident;
  matmul_extent : Z; matmul_padding : Z
}.
Record double_matmul_blocks := DoubleMatmulBlocks {
  matmul_A_block : block; matmul_B_block : block; matmul_C_block : block;
  matmul_alpha_block : block; matmul_beta_block : block
}.
Definition double_matmul_index site iterator :=
  memory_long_plus_int (Etempvar iterator memory_long_type) (matmul_padding site).
Definition double_matmul_cell site array row column :=
  double_matrix_lvalue array (matmul_extent site) (matmul_extent site)
    (double_matmul_index site row) (double_matmul_index site column).
Definition double_matmul_target site :=
  double_matmul_cell site (matmul_C site) (matmul_i site) (matmul_j site).
Definition double_matmul_reads site :=
  [Evar (matmul_beta site) memory_double_type; double_matmul_target site;
   Evar (matmul_alpha site) memory_double_type;
   double_matmul_cell site (matmul_A site) (matmul_i site) (matmul_k site);
   double_matmul_cell site (matmul_B site) (matmul_k site) (matmul_j site)].
Definition double_matmul_rhs site :=
  Ebinop Oadd
    (Ebinop Omul (Evar (matmul_beta site) memory_double_type)
      (double_matmul_target site) memory_double_type)
    (Ebinop Omul
      (Ebinop Omul (Evar (matmul_alpha site) memory_double_type)
        (double_matmul_cell site (matmul_A site) (matmul_i site) (matmul_k site)) memory_double_type)
      (double_matmul_cell site (matmul_B site) (matmul_k site) (matmul_j site)) memory_double_type)
    memory_double_type.
Definition double_matmul_body site := Sassign (double_matmul_target site) (double_matmul_rhs site).
Definition double_matmul_expression :=
  DoubleBinary DoubleAdd (DoubleBinary DoubleMul (DoubleRead 0) (DoubleRead 1))
    (DoubleBinary DoubleMul (DoubleBinary DoubleMul (DoubleRead 2) (DoubleRead 3)) (DoubleRead 4)).
Definition double_matmul_location site block i j :=
  MemoryLocation Mfloat64 block
    (8*((i+matmul_padding site)*matmul_extent site+(j+matmul_padding site))).
Definition double_matmul_locations site blocks i j k :=
  [MemoryLocation Mfloat64 (matmul_beta_block blocks) 0;
   double_matmul_location site (matmul_C_block blocks) i j;
   MemoryLocation Mfloat64 (matmul_alpha_block blocks) 0;
   double_matmul_location site (matmul_A_block blocks) i k;
   double_matmul_location site (matmul_B_block blocks) k j].

Lemma double_matmul_source_reads site : double_source_reads (double_matmul_rhs site) = double_matmul_reads site.
Proof. reflexivity. Qed.
Lemma double_matmul_value_code site :
  double_value_code (double_matmul_reads site) double_matmul_expression = Some (double_matmul_rhs site).
Proof. reflexivity. Qed.

Lemma double_global_location_receipt ge locals temps memory identifier block :
  double_global_binding ge locals identifier block ->
  double_memory_location_receipt ge locals temps memory (Evar identifier memory_double_type)
    (MemoryLocation Mfloat64 block 0).
Proof.
  intros [LOCAL SYMBOL]; unfold double_memory_location_receipt.
  split; [reflexivity|]; split; [reflexivity|]; split; [cbn; lia|]; split.
  - change (8 <= 18446744073709551616); lia.
  - change (eval_lvalue ge locals temps memory (Evar identifier memory_double_type) block Ptrofs.zero Full).
    apply eval_Evar_global; assumption.
Qed.

Lemma double_matmul_cell_receipt ge locals temps memory site array block row column i j :
  double_global_binding ge locals array block ->
  temps ! row = Some (Vlong (Int64.repr i)) -> temps ! column = Some (Vlong (Int64.repr j)) ->
  Int.min_signed <= matmul_padding site <= Int.max_signed ->
  0 <= i+matmul_padding site < matmul_extent site ->
  0 <= j+matmul_padding site < matmul_extent site ->
  8*(matmul_extent site*matmul_extent site) <= Ptrofs.modulus ->
  double_memory_location_receipt ge locals temps memory (double_matmul_cell site array row column)
    (double_matmul_location site block i j).
Proof.
  intros GLOBAL ROW COLUMN PAD I J SPAN; unfold double_memory_location_receipt, double_matmul_location.
  repeat split; try reflexivity; cbn [location_offset location_chunk location_block].
  - nia.
  - nia.
  - unfold double_matmul_cell; eapply double_matrix_lvalue_execution; try reflexivity; try exact GLOBAL; try lia.
    + apply memory_long_plus_int_execution; [reflexivity|exact PAD|constructor; exact ROW].
    + apply memory_long_plus_int_execution; [reflexivity|exact PAD|constructor; exact COLUMN].
Qed.

(** All fields are address/control facts. No field assumes a memory load,
    floating result, or successful source/candidate statement. *)
Record double_matmul_entry ge locals temps site blocks i j k : Prop := {
  matmul_A_binding : double_global_binding ge locals (matmul_A site) (matmul_A_block blocks);
  matmul_B_binding : double_global_binding ge locals (matmul_B site) (matmul_B_block blocks);
  matmul_C_binding : double_global_binding ge locals (matmul_C site) (matmul_C_block blocks);
  matmul_alpha_binding : double_global_binding ge locals (matmul_alpha site) (matmul_alpha_block blocks);
  matmul_beta_binding : double_global_binding ge locals (matmul_beta site) (matmul_beta_block blocks);
  matmul_i_value : temps ! (matmul_i site) = Some (Vlong (Int64.repr i));
  matmul_j_value : temps ! (matmul_j site) = Some (Vlong (Int64.repr j));
  matmul_k_value : temps ! (matmul_k site) = Some (Vlong (Int64.repr k));
  matmul_padding_range : Int.min_signed <= matmul_padding site <= Int.max_signed;
  matmul_i_bounds : 0 <= i+matmul_padding site < matmul_extent site;
  matmul_j_bounds : 0 <= j+matmul_padding site < matmul_extent site;
  matmul_k_bounds : 0 <= k+matmul_padding site < matmul_extent site;
  matmul_array_span : 8*(matmul_extent site*matmul_extent site) <= Ptrofs.modulus
}.

Theorem double_matmul_entry_receipts ge locals temps memory site blocks i j k :
  double_matmul_entry ge locals temps site blocks i j k ->
  Forall2 (double_memory_location_receipt ge locals temps memory) (double_matmul_reads site)
    (double_matmul_locations site blocks i j k) /\
  double_memory_location_receipt ge locals temps memory (double_matmul_target site)
    (double_matmul_location site (matmul_C_block blocks) i j).
Proof.
  intros [A B C ALPHA BETA I J K PAD IB JB KB SPAN]; split.
  - unfold double_matmul_reads, double_matmul_locations.
    constructor; [apply double_global_location_receipt; exact BETA|].
    constructor; [unfold double_matmul_target; eapply double_matmul_cell_receipt; eauto|].
    constructor; [apply double_global_location_receipt; exact ALPHA|].
    constructor; [eapply double_matmul_cell_receipt; eauto|].
    constructor; [eapply double_matmul_cell_receipt; eauto|constructor].
  - unfold double_matmul_target; eapply double_matmul_cell_receipt; eauto.
Qed.

Theorem double_matmul_source_decode fe ge locals temps memory site blocks i j k trace final_temps final outcome :
  double_matmul_entry ge locals temps site blocks i j k ->
  exec_stmt fe ge locals temps memory (double_matmul_body site) trace final_temps final outcome ->
  trace=E0 /\ final_temps=temps /\ outcome=Out_normal /\
  memory_action_run (MemoryAction (double_matmul_locations site blocks i j k)
    (double_matmul_location site (matmul_C_block blocks) i j)
    (fun values => compute_double_assignment values double_matmul_expression)) memory final.
Proof.
  intros ENTRY RUN; destruct (@double_matmul_entry_receipts ge locals temps memory site blocks i j k ENTRY) as [READS WRITE].
  unfold double_matmul_body in RUN; eapply double_assignment_source_decode; [|exact WRITE| |exact RUN].
  - rewrite double_matmul_source_reads; exact READS.
  - rewrite double_matmul_source_reads; apply double_matmul_value_code.
Qed.

Theorem double_matmul_lowered_execution fe ge locals temps memory site blocks i j k final :
  double_matmul_entry ge locals temps site blocks i j k ->
  memory_action_run (MemoryAction (double_matmul_locations site blocks i j k)
    (double_matmul_location site (matmul_C_block blocks) i j)
    (fun values => compute_double_assignment values double_matmul_expression)) memory final ->
  exec_stmt fe ge locals temps memory (double_matmul_body site) E0 temps final Out_normal.
Proof.
  intros ENTRY RUN; destruct (@double_matmul_entry_receipts ge locals temps memory site blocks i j k ENTRY) as [READS WRITE].
  unfold double_matmul_body; eapply double_assignment_lowered_execution;
    [exact READS|exact WRITE|apply double_matmul_value_code|exact RUN].
Qed.

Print Assumptions double_matmul_value_code.
Print Assumptions double_matmul_entry_receipts.
Print Assumptions double_matmul_source_decode.
Print Assumptions double_matmul_lowered_execution.
