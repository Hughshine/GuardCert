From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Globalenvs.
From compcert.cfrontend Require Import Clight.
From polcert.src Require Import PolyBase.
From polcert.lib Require Import Linalg.
From Guard Require Import CompCertMemoryActions ClightGlobalScope ClightRegionProgress.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryValueInstr GuardMemoryDoubleLocations
  GuardMemoryDynamicTensorLayout GuardMemoryDoubleSourceAccess GuardMemoryDoubleAffineSourceAccess
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceTransport GuardMemoryDoubleInitializedReductionSource.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma double_source_bounded_tensor_index dimensions coordinates :
  Forall2 (fun dimension coordinate => 0<=coordinate<dimension) dimensions coordinates ->
  exists index, tensor_index dimensions coordinates=Some index.
Proof.
  intro BOUNDS; induction BOUNDS as [|dimension coordinate dimensions coordinates RANGE REST IH].
  - exists 0; reflexivity.
  - destruct IH as [index INDEX]; exists (coordinate*tensor_volume dimensions+index); cbn [tensor_index].
    rewrite (proj2 (Z.leb_le 0 coordinate) ltac:(lia)),
      (proj2 (Z.ltb_lt coordinate dimension) ltac:(lia)),INDEX; reflexivity.
Qed.
Definition double_source_access_bounded access parameters :=
  Forall2 (fun dimension coordinate => 0<=coordinate<dimension)
    (double_affine_source_dimensions access)
    (affine_product (snd (double_affine_source_function access)) parameters).
Definition double_source_instruction_bounded description parameters :=
  forall access, In access (double_source_instruction_accesses description) -> double_source_access_bounded access parameters.

Theorem checked_double_source_access_resolved p controls source access ge locals layouts parameters :
  checked_double_affine_source_access p controls source=Some access ->
  preserving_globals (globalenv p) ge -> locals_avoid [fst (double_affine_source_function access)] locals ->
  layouts ! (fst (double_affine_source_function access))=Some (double_affine_source_dimensions access) ->
  double_source_access_bounded access parameters ->
  exists location, global_double_locations ge layouts (exact_cell (double_affine_source_function access) parameters)=Some location.
Proof.
  intros CHECK GLOBAL LOCAL LAYOUT BOUNDED.
  destruct (@checked_double_affine_source_access_sound p controls source access CHECK) as [DECODE STATIC].
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
Lemma checked_double_source_reads_resolved p controls sources accesses ge locals layouts parameters :
  checked_double_affine_source_reads p controls sources=Some accesses ->
  preserving_globals (globalenv p) ge ->
  (forall access, In access accesses -> locals_avoid [fst (double_affine_source_function access)] locals /\
    layouts ! (fst (double_affine_source_function access))=Some (double_affine_source_dimensions access) /\
    double_source_access_bounded access parameters) ->
  exists locations, resolve_cells (map (fun access => exact_cell (double_affine_source_function access) parameters) accesses)
    (global_double_locations ge layouts)=Some locations.
Proof.
  intro CHECK; revert accesses CHECK; induction sources as [|source rest IH]; intros accesses CHECK GLOBAL READY;
    cbn [checked_double_affine_source_reads] in CHECK.
  - inversion CHECK; subst; exists []; reflexivity.
  - destruct (checked_double_affine_source_access p controls source) as [access|] eqn:ACCESS; try discriminate.
    destruct (checked_double_affine_source_reads p controls rest) as [tail|] eqn:TAIL; try discriminate.
    inversion CHECK; subst accesses.
    destruct (READY access ltac:(cbn; auto)) as [LOCAL [LAYOUT BOUNDED]].
    destruct (@checked_double_source_access_resolved p controls source access ge locals layouts parameters
      ACCESS GLOBAL LOCAL LAYOUT BOUNDED) as [location LOCATION].
    destruct (@IH tail eq_refl GLOBAL ltac:(intros item MEMBER; apply READY; cbn; auto)) as [remaining REMAINING].
    exists (location::remaining); cbn [map resolve_cells]; rewrite LOCATION,REMAINING; reflexivity.
Qed.
Theorem checked_double_source_instruction_resolved_from_bounds p controls source description ge locals layouts parameters :
  checked_double_source_instruction p controls source=Some description ->
  double_source_layout_certificate description layouts ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_source_instruction_globals description) locals ->
  double_source_instruction_bounded description parameters ->
  double_source_instruction_resolved description parameters ge layouts.
Proof.
  intros CHECK LAYOUT GLOBAL LOCAL BOUNDS.
  destruct (@checked_double_source_instruction_sound p controls source description CHECK) as [_ [WC [RC OWN]]].
  assert (ACCESS_LOCAL : forall access, In access (double_source_instruction_accesses description) ->
    locals_avoid [fst (double_affine_source_function access)] locals).
  { intros access MEMBER identifier SINGLE; cbn in SINGLE; destruct SINGLE as [SAME|IMPOSSIBLE];
      [subst identifier|contradiction].
    apply LOCAL; unfold double_source_instruction_globals; apply in_map_iff; exists access; auto. }
  destruct (@checked_double_source_access_resolved p controls
    (GuardMemoryDoubleAssignmentFactory.double_assignment_target (double_source_assignment description))
    (double_source_write description) ge locals layouts parameters WC GLOBAL
    ltac:(apply ACCESS_LOCAL; cbn; auto) ltac:(apply LAYOUT; cbn; auto) ltac:(apply BOUNDS; cbn; auto)) as [write WRITE].
  destruct (@checked_double_source_reads_resolved p controls
    (GuardMemoryDoubleAssignmentFactory.double_assignment_reads (double_source_assignment description))
    (double_source_instruction_reads description) ge locals layouts parameters RC GLOBAL
    ltac:(intros access MEMBER; split; [apply ACCESS_LOCAL|split; [apply LAYOUT|apply BOUNDS]]; cbn; auto))
    as [reads READS].
  exists write,reads; split; [exact WRITE|].
  unfold double_source_instruction_model; cbn [value_instruction_reads]; rewrite map_map; exact READS.
Qed.

Print Assumptions double_source_bounded_tensor_index.
Print Assumptions checked_double_source_access_resolved.
Print Assumptions checked_double_source_reads_resolved.
Print Assumptions checked_double_source_instruction_resolved_from_bounds.
