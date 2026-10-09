From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import CompCertMemoryActions CompCertStoreSchedule.
From GuardMemory Require Import GuardMemoryDoubleValue GuardMemoryDoubleLocations GuardMemoryDoubleAssignment
  GuardMemoryDoubleMatmul GuardMemoryLongControl GuardMemoryObservationDeterminism.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma global_symbols_distinct_blocks (ge : genv) first second first_block second_block :
  Genv.find_symbol ge first = Some first_block -> Genv.find_symbol ge second = Some second_block ->
  first <> second -> first_block <> second_block.
Proof.
  intros FIRST SECOND DIFFERENT SAME; subst second_block.
  apply DIFFERENT; exact (@Senv.find_symbol_injective (Genv.to_senv ge) first second first_block FIRST SECOND).
Qed.
Lemma global_store_preserves_other_load (ge : genv) write_id header_id write_block header_block
  write_chunk header_chunk write_offset header_offset value before after :
  Genv.find_symbol ge write_id = Some write_block -> Genv.find_symbol ge header_id = Some header_block ->
  write_id <> header_id -> Mem.store write_chunk before write_block write_offset value = Some after ->
  Mem.load header_chunk after header_block header_offset = Mem.load header_chunk before header_block header_offset.
Proof.
  intros WRITE HEADER DIFFERENT STORE; eapply Mem.load_store_other; [exact STORE|left].
  pose proof (@global_symbols_distinct_blocks ge write_id header_id write_block header_block WRITE HEADER DIFFERENT); congruence.
Qed.

Theorem double_matmul_action_preserves_global ge locals temps memory site blocks i j k final
  header_id header_block header_chunk header_offset :
  double_matmul_entry ge locals temps site blocks i j k ->
  Genv.find_symbol ge header_id = Some header_block -> matmul_C site <> header_id ->
  memory_action_run (MemoryAction (double_matmul_locations site blocks i j k)
    (double_matmul_location site (matmul_C_block blocks) i j)
    (fun values => compute_double_assignment values double_matmul_expression)) memory final ->
  Mem.load header_chunk final header_block header_offset = Mem.load header_chunk memory header_block header_offset.
Proof.
  intros ENTRY HEADER DIFFERENT [values [value [READS [COMPUTE STORE]]]].
  destruct (matmul_C_binding ENTRY) as [_ WRITE].
  change (Mem.store Mfloat64 memory (matmul_C_block blocks)
    (8*((i+matmul_padding site)*matmul_extent site+(j+matmul_padding site))) value=Some final) in STORE.
  eapply global_store_preserves_other_load; eauto.
Qed.
Theorem double_matmul_source_preserves_global fe ge locals temps memory site blocks i j k trace final_temps final outcome
  header_id header_block header_chunk header_offset :
  double_matmul_entry ge locals temps site blocks i j k ->
  Genv.find_symbol ge header_id = Some header_block -> matmul_C site <> header_id ->
  exec_stmt fe ge locals temps memory (double_matmul_body site) trace final_temps final outcome ->
  Mem.load header_chunk final header_block header_offset = Mem.load header_chunk memory header_block header_offset.
Proof.
  intros ENTRY HEADER DIFFERENT RUN.
  destruct (double_matmul_source_decode ENTRY RUN) as [_ [_ [_ ACTION]]].
  eapply double_matmul_action_preserves_global; eauto.
Qed.

Lemma memory_global_long_loadv memory block :
  Mem.loadv Mint64 memory (Vptr block Ptrofs.zero) = Mem.load Mint64 memory block 0.
Proof. reflexivity. Qed.
Theorem memory_global_long_execution ge locals temps memory identifier block value :
  double_global_binding ge locals identifier block -> Mem.load Mint64 memory block 0 = Some (Vlong value) ->
  eval_expr ge locals temps memory (Evar identifier memory_long_type) (Vlong value).
Proof.
  intros [LOCAL SYMBOL] LOAD; eapply eval_Elvalue with (loc:=block) (ofs:=Ptrofs.zero) (bf:=Full).
  - apply eval_Evar_global; assumption.
  - apply deref_loc_value with (chunk:=Mint64); [reflexivity|rewrite memory_global_long_loadv; exact LOAD].
Qed.
Theorem memory_global_long_decode ge locals temps memory identifier block value :
  double_global_binding ge locals identifier block ->
  eval_expr ge locals temps memory (Evar identifier memory_long_type) value -> Mem.load Mint64 memory block 0 = Some value.
Proof.
  intros [LOCAL SYMBOL] RUN; inversion RUN; subst.
  match goal with LV : eval_lvalue _ _ _ _ (Evar _ _) _ _ _ |- _ =>
    inversion LV; subst; [rewrite LOCAL in *; discriminate|] end.
  assert (SAME : loc=block) by congruence; subst loc.
  match goal with READ : deref_loc _ _ _ _ _ _ |- _ => inversion READ; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  match goal with LOAD : Mem.loadv _ _ _ = Some _ |- _ => rewrite memory_global_long_loadv in LOAD; exact LOAD end.
Qed.

Print Assumptions global_store_preserves_other_load.
Print Assumptions double_matmul_action_preserves_global.
Print Assumptions double_matmul_source_preserves_global.
Print Assumptions memory_global_long_execution.
Print Assumptions memory_global_long_decode.
