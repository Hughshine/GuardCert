From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions ClightGlobalScope ClightRegionProgress.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryValueInstr GuardMemoryDynamicTensorLayout
  GuardMemoryDoubleValue GuardMemoryDoubleLocations GuardMemoryDoubleAssignment
  GuardMemoryDoubleAssignmentFactory GuardMemoryDoubleAffineSourceAccess
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleMatmulInstr GuardMemoryDoubleHeaderFrame.
Import ListNotations.
Set Implicit Arguments.

(** A region can use one checked registry across several instructions. The
    instruction's own minimal registry need not equal the region registry. *)
Definition double_source_layout_certificate description layouts :=
  forall access, In access (double_source_instruction_accesses description) ->
    layouts ! (fst (double_affine_source_function access))=Some (double_affine_source_dimensions access).
Lemma checked_double_source_layout_certificate description layouts :
  double_source_layout_check layouts (double_source_instruction_accesses description)=true ->
  double_source_layout_certificate description layouts.
Proof.
  intro CHECK; exact (@double_source_layout_check_sound layouts
    (double_source_instruction_accesses description) CHECK).
Qed.

Theorem checked_double_source_shared_receipts p controls source description valuation ge locals temps memory
  layouts write reads :
  checked_double_source_instruction p controls source=Some description ->
  double_source_layout_certificate description layouts ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_source_instruction_globals description) locals ->
  (forall identifier, In identifier controls -> temps ! identifier=Some (Vlong (Int64.repr (valuation identifier)))) ->
  global_double_locations ge layouts
    (exact_cell (value_instruction_write (double_source_instruction_model description)) (map valuation controls))=Some write ->
  resolve_cells (map (fun access => exact_cell access (map valuation controls))
    (value_instruction_reads (double_source_instruction_model description))) (global_double_locations ge layouts)=Some reads ->
  double_memory_location_receipt ge locals temps memory
    (double_assignment_target (double_source_assignment description)) write /\
  Forall2 (double_memory_location_receipt ge locals temps memory)
    (double_assignment_reads (double_source_assignment description)) reads.
Proof.
  intros CHECK LAYOUT GLOBAL LOCAL WORDS WRITE READS.
  destruct (@checked_double_source_instruction_sound p controls source description CHECK)
    as [ASSIGN [WRITE_CHECK [READS_CHECK OWN_LAYOUT]]].
  assert (ACCESS_LOCAL : forall access, In access (double_source_instruction_accesses description) ->
    locals_avoid [fst (double_affine_source_function access)] locals).
  { intros access MEMBER identifier SINGLE; cbn in SINGLE; destruct SINGLE as [SAME|IMPOSSIBLE];
      [subst identifier|contradiction].
    apply LOCAL; unfold double_source_instruction_globals; apply in_map_iff.
    exists access; split; [reflexivity|exact MEMBER]. }
  split.
  - eapply checked_double_affine_source_access_receipt;
      [exact WRITE_CHECK|exact GLOBAL|apply ACCESS_LOCAL; cbn; auto|exact WORDS|apply LAYOUT; cbn; auto|exact WRITE].
  - eapply checked_double_affine_source_reads_receipts;
      [exact READS_CHECK|exact GLOBAL| |exact WORDS|].
    + intros access MEMBER; split; [apply ACCESS_LOCAL|apply LAYOUT]; cbn; auto.
    + unfold double_source_instruction_model in READS; cbn [value_instruction_reads] in READS;
        rewrite map_map in READS; exact READS.
Qed.

Theorem checked_double_source_shared_execution p controls source description valuation fe ge locals temps memory
  layouts write reads trace after final outcome :
  checked_double_source_instruction p controls source=Some description ->
  double_source_layout_certificate description layouts ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_source_instruction_globals description) locals ->
  (forall identifier, In identifier controls -> temps ! identifier=Some (Vlong (Int64.repr (valuation identifier)))) ->
  global_double_locations ge layouts
    (exact_cell (value_instruction_write (double_source_instruction_model description)) (map valuation controls))=Some write ->
  resolve_cells (map (fun access => exact_cell access (map valuation controls))
    (value_instruction_reads (double_source_instruction_model description))) (global_double_locations ge layouts)=Some reads ->
  exec_stmt fe ge locals temps memory source trace after final outcome ->
  trace=E0 /\ after=temps /\ outcome=Out_normal /\
  DoubleAssignmentInstr.instr_semantics (double_source_instruction_model description) (map valuation controls)
    [exact_cell (value_instruction_write (double_source_instruction_model description)) (map valuation controls)]
    (map (fun access => exact_cell access (map valuation controls))
      (value_instruction_reads (double_source_instruction_model description)))
    (RuntimeState (global_double_locations ge layouts) memory) (RuntimeState (global_double_locations ge layouts) final).
Proof.
  intros CHECK LAYOUT GLOBAL LOCAL WORDS WRITE READS SOURCE.
  destruct (@checked_double_source_shared_receipts p controls source description valuation ge locals temps memory
    layouts write reads CHECK LAYOUT GLOBAL LOCAL WORDS WRITE READS) as [WR RR].
  destruct (@checked_double_source_instruction_sound p controls source description CHECK) as [ASSIGN _].
  destruct (@decoded_double_assignment_source_execution fe ge locals temps memory source
    (double_source_assignment description) reads write trace after final outcome ASSIGN RR WR SOURCE)
    as [TRACE [TEMPS [OUTCOME ACTION]]].
  split; [exact TRACE|]; split; [exact TEMPS|]; split; [exact OUTCOME|].
  apply (proj2 (@double_assignment_resolved_instruction (double_source_instruction_model description)
    (map valuation controls) (global_double_locations ge layouts) write reads memory final WRITE READS)); exact ACTION.
Qed.

Theorem checked_double_source_shared_execution_iff p controls source description valuation fe ge locals temps memory
  layouts write reads final :
  checked_double_source_instruction p controls source=Some description ->
  double_source_layout_certificate description layouts ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_source_instruction_globals description) locals ->
  (forall identifier, In identifier controls -> temps ! identifier=Some (Vlong (Int64.repr (valuation identifier)))) ->
  global_double_locations ge layouts
    (exact_cell (value_instruction_write (double_source_instruction_model description)) (map valuation controls))=Some write ->
  resolve_cells (map (fun access => exact_cell access (map valuation controls))
    (value_instruction_reads (double_source_instruction_model description))) (global_double_locations ge layouts)=Some reads ->
  (exec_stmt fe ge locals temps memory source E0 temps final Out_normal <->
   DoubleAssignmentInstr.instr_semantics (double_source_instruction_model description) (map valuation controls)
    [exact_cell (value_instruction_write (double_source_instruction_model description)) (map valuation controls)]
    (map (fun access => exact_cell access (map valuation controls))
      (value_instruction_reads (double_source_instruction_model description)))
    (RuntimeState (global_double_locations ge layouts) memory) (RuntimeState (global_double_locations ge layouts) final)).
Proof.
  intros CHECK LAYOUT GLOBAL LOCAL WORDS WRITE READS.
  destruct (@checked_double_source_shared_receipts p controls source description valuation ge locals temps memory
    layouts write reads CHECK LAYOUT GLOBAL LOCAL WORDS WRITE READS) as [WR RR].
  destruct (@checked_double_source_instruction_sound p controls source description CHECK) as [ASSIGN _].
  rewrite (@double_assignment_resolved_instruction (double_source_instruction_model description)
    (map valuation controls) (global_double_locations ge layouts) write reads memory final WRITE READS).
  eapply decoded_double_assignment_execution_iff; eassumption.
Qed.

Lemma checked_double_source_assignment_effects p controls source description fe ge locals temps memory
  trace after final outcome :
  checked_double_source_instruction p controls source=Some description ->
  exec_stmt fe ge locals temps memory source trace after final outcome ->
  trace=E0 /\ after=temps /\ outcome=Out_normal.
Proof.
  intro CHECK; destruct (@checked_double_source_instruction_sound p controls source description CHECK) as [ASSIGN _].
  destruct (@decoded_double_assignment_shape source (double_source_assignment description) ASSIGN) as [rhs [SHAPE TYPE]].
  rewrite SHAPE; intro RUN; inversion RUN; subst; auto.
Qed.

Lemma global_double_location_symbol ge layouts cell location :
  global_double_locations ge layouts cell=Some location ->
  Genv.find_symbol ge (arr_id cell)=Some (location_block location).
Proof.
  unfold global_double_locations; destruct (Genv.find_symbol ge (arr_id cell)) as [block|] eqn:SYMBOL;
    try discriminate.
  destruct (layouts ! (arr_id cell)) as [dimensions|]; try discriminate.
  destruct (tensor_index dimensions (arr_index cell)) as [index|]; try discriminate.
  intro RESOLVE; inversion RESOLVE; subst location; reflexivity.
Qed.
Theorem double_source_model_preserves_global description parameters (ge : genv) layouts memory final
  header header_block chunk offset :
  Genv.find_symbol ge header=Some header_block ->
  fst (value_instruction_write (double_source_instruction_model description))<>header ->
  DoubleAssignmentInstr.instr_semantics (double_source_instruction_model description) parameters
    [exact_cell (value_instruction_write (double_source_instruction_model description)) parameters]
    (map (fun access => exact_cell access parameters)
      (value_instruction_reads (double_source_instruction_model description)))
    (RuntimeState (global_double_locations ge layouts) memory) (RuntimeState (global_double_locations ge layouts) final) ->
  Mem.load chunk final header_block offset=Mem.load chunk memory header_block offset.
Proof.
  intros HEADER DIFFERENT [_ [_ [write [reads [WRITE [READS [SAME ACTION]]]]]]].
  destruct ACTION as [values [value [LOADS [COMPUTE STORE]]]].
  pose proof (@global_double_location_symbol ge layouts
    (exact_cell (value_instruction_write (double_source_instruction_model description)) parameters) write WRITE) as SYMBOL.
  destruct (value_instruction_write (double_source_instruction_model description)) as [identifier rows];
    cbn [exact_cell arr_id fst] in SYMBOL,DIFFERENT.
  eapply global_store_preserves_other_load;
    [exact SYMBOL|exact HEADER|exact DIFFERENT|exact STORE].
Qed.

Print Assumptions checked_double_source_layout_certificate.
Print Assumptions checked_double_source_shared_receipts.
Print Assumptions checked_double_source_shared_execution.
Print Assumptions checked_double_source_shared_execution_iff.
Print Assumptions checked_double_source_assignment_effects.
Print Assumptions global_double_location_symbol.
Print Assumptions double_source_model_preserves_global.
