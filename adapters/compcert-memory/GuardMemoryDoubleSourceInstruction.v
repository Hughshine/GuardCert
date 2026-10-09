From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions ClightGlobalScope ClightRegionProgress.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryValueInstr GuardMemoryDynamicTensorLayout
  GuardMemoryDoubleValue GuardMemoryDoubleLocations GuardMemoryDoubleAssignment
  GuardMemoryDoubleAssignmentFactory GuardMemoryDoubleTensorBackend
  GuardMemoryDoubleMatmulInstr GuardMemoryDoubleAffineSourceAccess.
Import ListNotations.
Set Implicit Arguments.

(** All source-dependent outputs are ordinary data. The registry is constructed
    from actual access descriptors and checked for consistent repeated names. *)
Definition double_source_layouts (accesses : list double_affine_source_access) :=
  fold_left (fun layouts access => PTree.set (fst (double_affine_source_function access))
    (double_affine_source_dimensions access) layouts) accesses (PTree.empty (list Z)).
Definition double_source_layout_check layouts accesses := forallb
  (fun access => match layouts ! (fst (double_affine_source_function access)) with
    | Some dimensions => if @List.list_eq_dec Z Z.eq_dec dimensions (double_affine_source_dimensions access)
        then true else false
    | None => false end) accesses.
Lemma double_source_layout_check_sound layouts accesses :
  double_source_layout_check layouts accesses=true ->
  forall access, In access accesses ->
    layouts ! (fst (double_affine_source_function access))=Some (double_affine_source_dimensions access).
Proof.
  intros CHECK access MEMBER; unfold double_source_layout_check in CHECK.
  apply forallb_forall with (x:=access) in CHECK; [|exact MEMBER].
  destruct (layouts ! (fst (double_affine_source_function access))) as [dimensions|] eqn:LAYOUT;
    try discriminate.
  destruct (@List.list_eq_dec Z Z.eq_dec dimensions (double_affine_source_dimensions access)) as [SAME|];
    try discriminate; subst dimensions; reflexivity.
Qed.

Record double_source_instruction := DoubleSourceInstruction {
  double_source_assignment : double_assignment_descriptor;
  double_source_write : double_affine_source_access;
  double_source_instruction_reads : list double_affine_source_access
}.
Definition double_source_instruction_accesses description :=
  double_source_write description::double_source_instruction_reads description.
Definition double_source_instruction_layouts description :=
  double_source_layouts (double_source_instruction_accesses description).
Definition double_source_instruction_globals description :=
  map (fun access => fst (double_affine_source_function access)) (double_source_instruction_accesses description).
Definition double_source_instruction_model description := MemoryValueInstruction
  (double_affine_source_function (double_source_write description))
  (map double_affine_source_function (double_source_instruction_reads description))
  (double_assignment_value (double_source_assignment description)).
Definition checked_double_source_instruction p controls source : option double_source_instruction :=
  match decode_double_assignment source with
  | Some assignment => match checked_double_affine_source_access p controls (double_assignment_target assignment),
      checked_double_affine_source_reads p controls (double_assignment_reads assignment) with
    | Some write,Some reads => let description := DoubleSourceInstruction assignment write reads in
        if double_source_layout_check (double_source_instruction_layouts description)
            (double_source_instruction_accesses description) then Some description else None
    | _,_ => None end
  | None => None end.
Lemma checked_double_source_instruction_sound p controls source description :
  checked_double_source_instruction p controls source=Some description ->
  decode_double_assignment source=Some (double_source_assignment description) /\
  checked_double_affine_source_access p controls (double_assignment_target (double_source_assignment description))=
    Some (double_source_write description) /\
  checked_double_affine_source_reads p controls (double_assignment_reads (double_source_assignment description))=
    Some (double_source_instruction_reads description) /\
  double_source_layout_check (double_source_instruction_layouts description)
    (double_source_instruction_accesses description)=true.
Proof.
  unfold checked_double_source_instruction; destruct (decode_double_assignment source) as [assignment|] eqn:ASSIGN;
    try discriminate.
  destruct (checked_double_affine_source_access p controls (double_assignment_target assignment)) as [write|] eqn:WRITE;
    try discriminate.
  destruct (checked_double_affine_source_reads p controls (double_assignment_reads assignment)) as [reads|] eqn:READS;
    try discriminate.
  destruct (double_source_layout_check (double_source_instruction_layouts (DoubleSourceInstruction assignment write reads))
    (double_source_instruction_accesses (DoubleSourceInstruction assignment write reads))) eqn:LAYOUT;
    try discriminate; intro RESULT; inversion RESULT; subst description; auto.
Qed.

Theorem checked_double_source_instruction_receipts p controls source description valuation ge locals temps memory write reads :
  checked_double_source_instruction p controls source=Some description ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_source_instruction_globals description) locals ->
  (forall identifier, In identifier controls -> temps ! identifier=Some (Vlong (Int64.repr (valuation identifier)))) ->
  global_double_locations ge (double_source_instruction_layouts description)
    (exact_cell (value_instruction_write (double_source_instruction_model description)) (map valuation controls))=Some write ->
  resolve_cells (map (fun access => exact_cell access (map valuation controls))
    (value_instruction_reads (double_source_instruction_model description)))
    (global_double_locations ge (double_source_instruction_layouts description))=Some reads ->
  double_memory_location_receipt ge locals temps memory
    (double_assignment_target (double_source_assignment description)) write /\
  Forall2 (double_memory_location_receipt ge locals temps memory)
    (double_assignment_reads (double_source_assignment description)) reads.
Proof.
  intros CHECK GLOBAL LOCAL WORDS WRITE READS.
  destruct (@checked_double_source_instruction_sound p controls source description CHECK)
    as [ASSIGN [WRITE_CHECK [READS_CHECK LAYOUT_CHECK]]].
  pose proof (@double_source_layout_check_sound (double_source_instruction_layouts description)
    (double_source_instruction_accesses description) LAYOUT_CHECK) as LAYOUT.
  assert (ACCESS_LOCAL : forall access, In access (double_source_instruction_accesses description) ->
    locals_avoid [fst (double_affine_source_function access)] locals).
  { intros access MEMBER identifier SINGLE; cbn in SINGLE; destruct SINGLE as [SAME|IMPOSSIBLE]; [subst identifier|contradiction].
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

(** A finite local source/model equivalence. Point bounds/resolution and the
    I64 control-state view are dynamic premises; successful model execution
    retains the real CompCert load/store permissions. *)
Theorem checked_double_source_instruction_execution_iff p controls source description valuation fe ge locals temps memory
  write reads final :
  checked_double_source_instruction p controls source=Some description ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_source_instruction_globals description) locals ->
  (forall identifier, In identifier controls -> temps ! identifier=Some (Vlong (Int64.repr (valuation identifier)))) ->
  global_double_locations ge (double_source_instruction_layouts description)
    (exact_cell (value_instruction_write (double_source_instruction_model description)) (map valuation controls))=Some write ->
  resolve_cells (map (fun access => exact_cell access (map valuation controls))
    (value_instruction_reads (double_source_instruction_model description)))
    (global_double_locations ge (double_source_instruction_layouts description))=Some reads ->
  (exec_stmt fe ge locals temps memory source E0 temps final Out_normal <->
   DoubleAssignmentInstr.instr_semantics (double_source_instruction_model description) (map valuation controls)
    [exact_cell (value_instruction_write (double_source_instruction_model description)) (map valuation controls)]
    (map (fun access => exact_cell access (map valuation controls))
      (value_instruction_reads (double_source_instruction_model description)))
    (RuntimeState (global_double_locations ge (double_source_instruction_layouts description)) memory)
    (RuntimeState (global_double_locations ge (double_source_instruction_layouts description)) final)).
Proof.
  intros CHECK GLOBAL LOCAL WORDS WRITE READS.
  destruct (@checked_double_source_instruction_receipts p controls source description valuation ge locals temps memory
    write reads CHECK GLOBAL LOCAL WORDS WRITE READS) as [WRITE_RECEIPT READ_RECEIPTS].
  destruct (@checked_double_source_instruction_sound p controls source description CHECK) as [ASSIGN _].
  rewrite (@double_assignment_resolved_instruction (double_source_instruction_model description) (map valuation controls)
    (global_double_locations ge (double_source_instruction_layouts description)) write reads memory final WRITE READS).
  eapply decoded_double_assignment_execution_iff; eassumption.
Qed.

Print Assumptions double_source_layout_check_sound.
Print Assumptions checked_double_source_instruction_sound.
Print Assumptions checked_double_source_instruction_receipts.
Print Assumptions checked_double_source_instruction_execution_iff.
