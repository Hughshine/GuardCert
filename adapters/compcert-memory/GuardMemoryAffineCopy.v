From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightRectangularStore ClightIndexedArray CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryMultipleArrays
  GuardMemoryRegistryBackend GuardMemoryLayoutRegistry GuardMemoryRectangles GuardMemoryCopyArray
  GuardMemoryAffineAccessExpressions GuardMemoryAffineAccess.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_copy_statement write read := Sassign (memory_access_code write) (memory_access_code read).
Definition memory_affine_copy_instruction write read := MemoryInstruction
  (memory_access_instruction write) [memory_access_instruction read]
  (AddValue (LoadedValue 0) (ConstantValue 0)).
Definition memory_affine_copy_action write read wb rb i j := MemoryAction
  [MemoryLocation Mint32 rb (4*memory_index_value (memory_access_index read) i j)]
  (MemoryLocation Mint32 wb (4*memory_index_value (memory_access_index write) i j)) memory_copy_compute.
Definition memory_affine_copy_physical ge locals write read i j before after :=
  exists wb rb, rect_array_binding (memory_access_shape write) ge locals (memory_access_array write) wb /\
    rect_array_binding (memory_access_shape read) ge locals (memory_access_array read) rb /\
    memory_action_run (memory_affine_copy_action write read wb rb i j) before after.

Lemma memory_affine_copy_inverse write read row column fe ge locals temps memory after final i j :
  rectangle_layout_valid (memory_access_shape write) -> rectangle_layout_valid (memory_access_shape read) ->
  row <> column ->
  memory_encode_index row column (memory_access_expression write) = Some (memory_access_index write) ->
  memory_encode_index row column (memory_access_expression read) = Some (memory_access_index read) ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  0 <= memory_index_value (memory_access_index write) i j < rectangle_extent (memory_access_shape write) ->
  0 <= memory_index_value (memory_access_index read) i j < rectangle_extent (memory_access_shape read) ->
  exec_stmt fe ge locals temps memory (memory_affine_copy_statement write read) E0 after final Out_normal ->
  memory_affine_copy_physical ge locals write read i j memory final /\ after = temps.
Proof.
  intros WVALID RVALID DISTINCT WE RE ROW COLUMN WBOUND RBOUND RUN; inversion RUN; subst.
  match goal with LVALUE : eval_lvalue _ _ ?current _ (memory_access_code write) _ _ _ |- _ =>
    destruct (@memory_affine_access_inverse (memory_access_shape write) (memory_access_array write)
      (memory_access_expression write) row column (memory_access_index write) ge locals current memory i j _ _ _
      WVALID DISTINCT WE ROW COLUMN WBOUND LVALUE) as [ARRAY [OFFSET FIELD]]; subst end.
  match goal with READ : eval_expr _ _ ?current _ (memory_access_code read) ?value |- _ =>
    destruct (@memory_affine_access_load_inverse (memory_access_shape read) (memory_access_array read)
      (memory_access_expression read) row column (memory_access_index read) ge locals current memory i j value
      RVALID DISTINCT RE ROW COLUMN RBOUND READ) as [rb [READ_BIND LOAD]] end.
  match goal with CAST : sem_cast ?old _ _ _ = Some _ |- _ =>
    destruct old; try discriminate CAST; inversion CAST; subst end.
  match goal with ASSIGN : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion ASSIGN; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  match goal with STORE : Mem.storev _ _ _ _ = Some _ |- _ =>
    cbn [Mem.storev] in STORE; rewrite Ptrofs.unsigned_repr in STORE by
      (apply (@rect_small_offset_bound _ WVALID); lia);
    destruct (zle (4*memory_index_value (memory_access_index write) i j+size_chunk Mint32) Ptrofs.modulus);
      try discriminate STORE end.
  split; [|reflexivity]; exists loc,rb; split; [exact ARRAY|]; split; [exact READ_BIND|].
  exists [Vint i0],(Vint i0); split.
  - change (match Mem.load Mint32 memory rb (4*memory_index_value (memory_access_index read) i j) with
      Some value => Some [value] | None => None end = Some [Vint i0]); rewrite LOAD; reflexivity.
  - split; [reflexivity|assumption].
Qed.

Theorem memory_affine_copy_registry_point descriptors entries ge locals write read i j before after :
  Forall2 (memory_descriptor_binding ge locals) descriptors entries ->
  memory_descriptors_cover descriptors [memory_access_descriptor write;memory_access_descriptor read] ->
  NoDup (map memory_array_id entries) ->
  0 <= memory_index_value (memory_access_index write) i j < rectangle_extent (memory_access_shape write) ->
  0 <= memory_index_value (memory_access_index read) i j < rectangle_extent (memory_access_shape read) ->
  (memory_affine_copy_physical ge locals write read i j before after <->
    memory_point (memory_affine_copy_instruction write read) i j
      (RuntimeState (memory_array_registry entries) before) (RuntimeState (memory_array_registry entries) after)).
Proof.
  intros ARRAYS COVER UNIQUE WBOUND RBOUND.
  assert (WCOVER : memory_descriptors_cover descriptors [memory_access_descriptor write]).
  { inversion COVER; subst; constructor; [assumption|constructor]. }
  assert (RCOVER : memory_descriptors_cover descriptors [memory_access_descriptor read]).
  { inversion COVER; subst; match goal with REST : Forall _ [_] |- _ => exact REST end. }
  destruct (@memory_registry_requested_array descriptors [memory_access_descriptor write] entries ge locals
    (memory_access_array write) (memory_access_shape write) ARRAYS WCOVER ltac:(cbn; auto))
    as [we [WMEMBER [WID [WEXTENT WRITE]]]].
  destruct (@memory_registry_requested_array descriptors [memory_access_descriptor read] entries ge locals
    (memory_access_array read) (memory_access_shape read) ARRAYS RCOVER ltac:(cbn; auto))
    as [re [RMEMBER [RID [REXTENT READ]]]].
  set (wb := memory_array_block we); set (rb := memory_array_block re).
  assert (WRITE_LOOKUP : memory_array_registry entries (exact_cell (memory_access_instruction write) [i;j]) =
    Some (MemoryLocation Mint32 wb (4*memory_index_value (memory_access_index write) i j)))
    by (eapply memory_affine_access_registry; eassumption).
  assert (READ_LOOKUP : memory_array_registry entries (exact_cell (memory_access_instruction read) [i;j]) =
    Some (MemoryLocation Mint32 rb (4*memory_index_value (memory_access_index read) i j)))
    by (eapply memory_affine_access_registry; eassumption).
  unfold memory_point.
  rewrite (@resolved_instruction_execution (memory_affine_copy_instruction write read) [i;j]
    (memory_array_registry entries)
    (MemoryLocation Mint32 wb (4*memory_index_value (memory_access_index write) i j))
    [MemoryLocation Mint32 rb (4*memory_index_value (memory_access_index read) i j)] before after).
  - split.
    + intros [actual_wb [actual_rb [AW [AR [inputs [value [LOAD [COMPUTE STORE]]]]]]]].
      assert (SW : actual_wb = wb) by (eapply rect_array_binding_unique; eassumption).
      assert (SR : actual_rb = rb) by (eapply rect_array_binding_unique; eassumption).
      subst actual_wb actual_rb; exists inputs,value; split; [exact LOAD|]; split; [|exact STORE].
      destruct (@singleton_load_inputs _ _ _ LOAD) as [old ->].
      unfold memory_copy_compute in COMPUTE; destruct old; try discriminate COMPUTE.
      cbn [memory_compute memory_affine_copy_instruction instruction_value evaluate_value nth_error]; rewrite Int.add_zero; exact COMPUTE.
    + intros [inputs [value [LOAD [COMPUTE STORE]]]].
      exists wb,rb; split; [exact WRITE|]; split; [exact READ|]; exists inputs,value; split; [exact LOAD|]; split; [|exact STORE].
      destruct (@singleton_load_inputs _ _ _ LOAD) as [old ->].
      cbn [memory_compute memory_affine_copy_instruction instruction_value evaluate_value nth_error] in COMPUTE; destruct old; try discriminate COMPUTE.
      rewrite Int.add_zero in COMPUTE; exact COMPUTE.
  - exact WRITE_LOOKUP.
  - cbn [memory_read_cells memory_affine_copy_instruction instruction_reads map resolve_cells].
    rewrite READ_LOOKUP; reflexivity.
Qed.
Print Assumptions memory_affine_copy_inverse.
Print Assumptions memory_affine_copy_registry_point.

Lemma memory_affine_copy_initial_bindings ge locals write read before after :
  memory_index_value (memory_access_index write) 0 0 = 0 ->
  memory_index_value (memory_access_index read) 0 0 = 0 ->
  memory_affine_copy_physical ge locals write read 0 0 before after ->
  forall descriptor, In descriptor [memory_access_descriptor write;memory_access_descriptor read] ->
    exists block, rect_array_binding (memory_descriptor_shape descriptor) ge locals
      (memory_descriptor_variable descriptor) block /\ Mem.valid_pointer before block 0 = true.
Proof.
  intros WZERO RZERO [wb [rb [WRITE [READ [inputs [value [LOAD [_ STORE]]]]]]]] descriptor MEMBER.
  change (Mem.store Mint32 before wb (4*memory_index_value (memory_access_index write) 0 0) value = Some after) in STORE.
  change (match Mem.load Mint32 before rb (4*memory_index_value (memory_access_index read) 0 0) with
    Some old => Some [old] | None => None end = Some inputs) in LOAD.
  rewrite WZERO in STORE; rewrite RZERO in LOAD; cbn in STORE,LOAD.
  destruct MEMBER as [<-|[<-|[]]]; cbn.
  - exists wb; split; [exact WRITE|]; apply Mem.valid_pointer_nonempty_perm.
    pose proof (@Mem.store_valid_access_3 _ _ _ _ _ _ STORE) as [PERMISSION ALIGN].
    eapply Mem.perm_implies; [apply PERMISSION; change (0 <= 0 < 4); lia|constructor].
  - exists rb; split; [exact READ|].
    destruct (Mem.load Mint32 before rb 0) as [old|] eqn:LOADED; [|discriminate].
    apply Mem.valid_pointer_nonempty_perm.
    pose proof (@Mem.load_valid_access _ _ _ _ _ LOADED) as [PERMISSION ALIGN].
    eapply Mem.perm_implies; [apply PERMISSION; change (0 <= 0 < 4); lia|constructor].
Qed.
