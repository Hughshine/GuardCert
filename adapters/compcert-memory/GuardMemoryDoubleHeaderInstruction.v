From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.src Require Import PolyBase.
From polcert.lib Require Import Linalg.
From Guard Require Import CompCertMemoryActions ClightGlobalScope ClightRegionProgress.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryValueInstr GuardMemoryDynamicTensorLayout
  GuardMemoryDoubleValue GuardMemoryDoubleLocations GuardMemoryDoubleAssignment
  GuardMemoryDoubleAssignmentFactory GuardMemoryDoubleTensorBackend
  GuardMemoryDoubleMatmulInstr GuardMemoryDoubleAffineSourceAccess GuardMemoryDoubleSourceAccess
  GuardMemoryDoubleHeaderSourceAccess GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceTransport
  GuardMemoryDoubleSourceResolvedPoints GuardMemoryDoubleInitializedReductionSource.
Import ListNotations.
Set Implicit Arguments.

Definition checked_double_header_source_instruction p header controls source : option double_source_instruction :=
  match decode_double_assignment source with
  | Some assignment => match checked_double_header_affine_source_access p header controls (double_assignment_target assignment),
      checked_double_header_affine_source_reads p header controls (double_assignment_reads assignment) with
    | Some write,Some reads => let description := DoubleSourceInstruction assignment write reads in
        if double_source_layout_check (double_source_instruction_layouts description)
            (double_source_instruction_accesses description) then Some description else None
    | _,_ => None end
  | None => None end.
Lemma checked_double_header_source_instruction_sound p header controls source description :
  checked_double_header_source_instruction p header controls source=Some description ->
  decode_double_assignment source=Some (double_source_assignment description) /\
  checked_double_header_affine_source_access p header controls (double_assignment_target (double_source_assignment description))=
    Some (double_source_write description) /\
  checked_double_header_affine_source_reads p header controls (double_assignment_reads (double_source_assignment description))=
    Some (double_source_instruction_reads description) /\
  double_source_layout_check (double_source_instruction_layouts description)
    (double_source_instruction_accesses description)=true.
Proof.
  unfold checked_double_header_source_instruction; destruct (decode_double_assignment source) as [assignment|] eqn:ASSIGN;
    try discriminate.
  destruct (checked_double_header_affine_source_access p header controls (double_assignment_target assignment)) as [write|] eqn:WRITE;
    try discriminate.
  destruct (checked_double_header_affine_source_reads p header controls (double_assignment_reads assignment)) as [reads|] eqn:READS;
    try discriminate.
  destruct (double_source_layout_check (double_source_instruction_layouts (DoubleSourceInstruction assignment write reads))
    (double_source_instruction_accesses (DoubleSourceInstruction assignment write reads))) eqn:LAYOUT;
    try discriminate; intro RESULT; inversion RESULT; subst description; auto.
Qed.

Theorem checked_double_header_source_shared_receipts p header controls source description valuation ge locals temps memory
  layouts write reads :
  checked_double_header_source_instruction p header controls source=Some description ->
  double_source_layout_certificate description layouts ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_source_instruction_globals description) locals ->
  eval_expr ge locals temps memory (Evar header memory_long_type)
    (Vlong (Int64.repr (valuation header))) ->
  (forall identifier, In identifier controls -> identifier<>header -> temps ! identifier=Some (Vlong (Int64.repr (valuation identifier)))) ->
  global_double_locations ge layouts
    (exact_cell (value_instruction_write (double_source_instruction_model description)) (map valuation controls))=Some write ->
  resolve_cells (map (fun access => exact_cell access (map valuation controls))
    (value_instruction_reads (double_source_instruction_model description))) (global_double_locations ge layouts)=Some reads ->
  double_memory_location_receipt ge locals temps memory
    (double_assignment_target (double_source_assignment description)) write /\
  Forall2 (double_memory_location_receipt ge locals temps memory)
    (double_assignment_reads (double_source_assignment description)) reads.
Proof.
  intros CHECK LAYOUT GLOBAL LOCAL HEADER WORDS WRITE READS.
  destruct (@checked_double_header_source_instruction_sound p header controls source description CHECK)
    as [ASSIGN [WRITE_CHECK [READS_CHECK OWN_LAYOUT]]].
  assert (ACCESS_LOCAL : forall access, In access (double_source_instruction_accesses description) ->
    locals_avoid [fst (double_affine_source_function access)] locals).
  { intros access MEMBER identifier SINGLE; cbn in SINGLE; destruct SINGLE as [SAME|IMPOSSIBLE];
      [subst identifier|contradiction].
    apply LOCAL; unfold double_source_instruction_globals; apply in_map_iff.
    exists access; split; [reflexivity|exact MEMBER]. }
  split.
  - eapply checked_double_header_affine_source_access_receipt;
      [exact WRITE_CHECK|exact GLOBAL|apply ACCESS_LOCAL; cbn; auto|exact HEADER|exact WORDS|apply LAYOUT; cbn; auto|exact WRITE].
  - eapply checked_double_header_affine_source_reads_receipts;
      [exact READS_CHECK|exact GLOBAL| |exact HEADER|exact WORDS|].
    + intros access MEMBER; split; [apply ACCESS_LOCAL|apply LAYOUT]; cbn; auto.
    + unfold double_source_instruction_model in READS; cbn [value_instruction_reads] in READS;
        rewrite map_map in READS; exact READS.
Qed.

Theorem checked_double_header_source_shared_execution p header controls source description valuation fe ge locals temps memory
  layouts write reads trace after final outcome :
  checked_double_header_source_instruction p header controls source=Some description ->
  double_source_layout_certificate description layouts ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_source_instruction_globals description) locals ->
  eval_expr ge locals temps memory (Evar header memory_long_type)
    (Vlong (Int64.repr (valuation header))) ->
  (forall identifier, In identifier controls -> identifier<>header -> temps ! identifier=Some (Vlong (Int64.repr (valuation identifier)))) ->
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
  intros CHECK LAYOUT GLOBAL LOCAL HEADER WORDS WRITE READS SOURCE.
  destruct (@checked_double_header_source_shared_receipts p header controls source description valuation ge locals temps memory
    layouts write reads CHECK LAYOUT GLOBAL LOCAL HEADER WORDS WRITE READS) as [WR RR].
  destruct (@checked_double_header_source_instruction_sound p header controls source description CHECK) as [ASSIGN _].
  destruct (@decoded_double_assignment_source_execution fe ge locals temps memory source
    (double_source_assignment description) reads write trace after final outcome ASSIGN RR WR SOURCE)
    as [TRACE [TEMPS [OUTCOME ACTION]]].
  split; [exact TRACE|]; split; [exact TEMPS|]; split; [exact OUTCOME|].
  apply (proj2 (@double_assignment_resolved_instruction (double_source_instruction_model description)
    (map valuation controls) (global_double_locations ge layouts) write reads memory final WRITE READS)); exact ACTION.
Qed.

Theorem checked_double_header_source_shared_execution_iff p header controls source description valuation fe ge locals temps memory
  layouts write reads final :
  checked_double_header_source_instruction p header controls source=Some description ->
  double_source_layout_certificate description layouts ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_source_instruction_globals description) locals ->
  eval_expr ge locals temps memory (Evar header memory_long_type)
    (Vlong (Int64.repr (valuation header))) ->
  (forall identifier, In identifier controls -> identifier<>header -> temps ! identifier=Some (Vlong (Int64.repr (valuation identifier)))) ->
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
  intros CHECK LAYOUT GLOBAL LOCAL HEADER WORDS WRITE READS.
  destruct (@checked_double_header_source_shared_receipts p header controls source description valuation ge locals temps memory
    layouts write reads CHECK LAYOUT GLOBAL LOCAL HEADER WORDS WRITE READS) as [WR RR].
  destruct (@checked_double_header_source_instruction_sound p header controls source description CHECK) as [ASSIGN _].
  rewrite (@double_assignment_resolved_instruction (double_source_instruction_model description)
    (map valuation controls) (global_double_locations ge layouts) write reads memory final WRITE READS).
  eapply decoded_double_assignment_execution_iff; eassumption.
Qed.

Lemma checked_double_header_source_assignment_effects p header controls source description fe ge locals temps memory
  trace after final outcome :
  checked_double_header_source_instruction p header controls source=Some description ->
  exec_stmt fe ge locals temps memory source trace after final outcome ->
  trace=E0 /\ after=temps /\ outcome=Out_normal.
Proof.
  intro CHECK; destruct (@checked_double_header_source_instruction_sound p header controls source description CHECK) as [ASSIGN _].
  destruct (@decoded_double_assignment_shape source (double_source_assignment description) ASSIGN) as [rhs [SHAPE TYPE]].
  rewrite SHAPE; intro RUN; inversion RUN; subst; auto.
Qed.

Theorem checked_double_header_source_access_resolved p header controls source access ge locals layouts parameters :
  checked_double_header_affine_source_access p header controls source=Some access ->
  preserving_globals (globalenv p) ge -> locals_avoid [fst (double_affine_source_function access)] locals ->
  layouts ! (fst (double_affine_source_function access))=Some (double_affine_source_dimensions access) ->
  double_source_access_bounded access parameters ->
  exists location, global_double_locations ge layouts (exact_cell (double_affine_source_function access) parameters)=Some location.
Proof.
  intros CHECK GLOBAL LOCAL LAYOUT BOUNDED.
  destruct (@checked_double_header_affine_source_access_sound p header controls source access CHECK) as [DECODE STATIC].
  destruct (@double_source_access_static_sound p (double_affine_source_metadata access) ge locals STATIC GLOBAL LOCAL)
    as [block [[ABSENT SYMBOL] [POSITIVE SPAN]]].
  destruct (@double_source_bounded_tensor_index (double_affine_source_dimensions access)
    (affine_product (snd (double_affine_source_function access)) parameters) BOUNDED) as [index INDEX].
  change (Genv.find_symbol ge (fst (double_affine_source_function access))=Some block) in SYMBOL.
  exists (MemoryLocation Mfloat64 block (8*index)).
  unfold global_double_locations; destruct (double_affine_source_function access) as [identifier rows] eqn:ACCESS.
  cbn [exact_cell arr_id arr_index fst snd double_affine_source_metadata double_source_array] in *.
  rewrite SYMBOL,LAYOUT,INDEX; reflexivity.
Qed.
Lemma checked_double_header_source_reads_resolved p header controls sources accesses ge locals layouts parameters :
  checked_double_header_affine_source_reads p header controls sources=Some accesses ->
  preserving_globals (globalenv p) ge ->
  (forall access, In access accesses -> locals_avoid [fst (double_affine_source_function access)] locals /\
    layouts ! (fst (double_affine_source_function access))=Some (double_affine_source_dimensions access) /\
    double_source_access_bounded access parameters) ->
  exists locations, resolve_cells (map (fun access => exact_cell (double_affine_source_function access) parameters) accesses)
    (global_double_locations ge layouts)=Some locations.
Proof.
  intro CHECK; revert accesses CHECK; induction sources as [|source rest IH]; intros accesses CHECK GLOBAL READY;
    cbn [checked_double_header_affine_source_reads] in CHECK.
  - inversion CHECK; subst; exists []; reflexivity.
  - destruct (checked_double_header_affine_source_access p header controls source) as [access|] eqn:ACCESS; try discriminate.
    destruct (checked_double_header_affine_source_reads p header controls rest) as [tail|] eqn:TAIL; try discriminate.
    inversion CHECK; subst accesses.
    destruct (READY access ltac:(cbn; auto)) as [LOCAL [LAYOUT BOUNDED]].
    destruct (@checked_double_header_source_access_resolved p header controls source access ge locals layouts parameters
      ACCESS GLOBAL LOCAL LAYOUT BOUNDED) as [location LOCATION].
    destruct (@IH tail eq_refl GLOBAL ltac:(intros item MEMBER; apply READY; cbn; auto)) as [remaining REMAINING].
    exists (location::remaining); cbn [map resolve_cells]; rewrite LOCATION,REMAINING; reflexivity.
Qed.
Theorem checked_double_header_source_instruction_resolved_from_bounds p header controls source description ge locals layouts parameters :
  checked_double_header_source_instruction p header controls source=Some description ->
  double_source_layout_certificate description layouts ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_source_instruction_globals description) locals ->
  double_source_instruction_bounded description parameters ->
  double_source_instruction_resolved description parameters ge layouts.
Proof.
  intros CHECK LAYOUT GLOBAL LOCAL BOUNDS.
  destruct (@checked_double_header_source_instruction_sound p header controls source description CHECK) as [_ [WC [RC OWN]]].
  assert (ACCESS_LOCAL : forall access, In access (double_source_instruction_accesses description) ->
    locals_avoid [fst (double_affine_source_function access)] locals).
  { intros access MEMBER identifier SINGLE; cbn in SINGLE; destruct SINGLE as [SAME|IMPOSSIBLE];
      [subst identifier|contradiction].
    apply LOCAL; unfold double_source_instruction_globals; apply in_map_iff; exists access; auto. }
  destruct (@checked_double_header_source_access_resolved p header controls
    (GuardMemoryDoubleAssignmentFactory.double_assignment_target (double_source_assignment description))
    (double_source_write description) ge locals layouts parameters WC GLOBAL
    ltac:(apply ACCESS_LOCAL; cbn; auto) ltac:(apply LAYOUT; cbn; auto) ltac:(apply BOUNDS; cbn; auto)) as [write WRITE].
  destruct (@checked_double_header_source_reads_resolved p header controls
    (GuardMemoryDoubleAssignmentFactory.double_assignment_reads (double_source_assignment description))
    (double_source_instruction_reads description) ge locals layouts parameters RC GLOBAL
    ltac:(intros access MEMBER; split; [apply ACCESS_LOCAL|split; [apply LAYOUT|apply BOUNDS]]; cbn; auto))
    as [reads READS].
  exists write,reads; split; [exact WRITE|].
  unfold double_source_instruction_model; cbn [value_instruction_reads]; rewrite map_map; exact READS.
Qed.


Print Assumptions checked_double_header_source_instruction_sound.
Print Assumptions checked_double_header_source_shared_receipts.
Print Assumptions checked_double_header_source_shared_execution.
Print Assumptions checked_double_header_source_shared_execution_iff.
Print Assumptions checked_double_header_source_assignment_effects.
Print Assumptions checked_double_header_source_access_resolved.
Print Assumptions checked_double_header_source_reads_resolved.
Print Assumptions checked_double_header_source_instruction_resolved_from_bounds.
