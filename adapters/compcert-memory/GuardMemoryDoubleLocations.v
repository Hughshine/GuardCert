From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Globalenvs.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From polcert.src Require Import PolyBase.
From polcert.lib Require Import Linalg.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDynamicTensorLayout
  GuardMemoryDoubleValue GuardMemoryObservationDeterminism.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition double_tensor_locations array block dimensions (cell : MemCell) :=
  if Pos.eqb (arr_id cell) array then
    match tensor_index dimensions (arr_index cell) with
    | Some index => Some (MemoryLocation Mfloat64 block (8 * index)) | None => None end
  else None.

Theorem double_tensor_locations_nonalias array block dimensions :
  locations_nonalias (double_tensor_locations array block dimensions).
Proof.
  intros [first_id first] [second_id second] first_location second_location FIRST SECOND DIFFERENT.
  unfold double_tensor_locations in FIRST,SECOND; cbn [arr_id arr_index] in FIRST,SECOND.
  destruct (Pos.eqb first_id array) eqn:FID; try discriminate FIRST.
  destruct (Pos.eqb second_id array) eqn:SID; try discriminate SECOND.
  apply Pos.eqb_eq in FID,SID; subst first_id second_id.
  destruct (tensor_index dimensions first) as [x|] eqn:X; try discriminate FIRST.
  destruct (tensor_index dimensions second) as [y|] eqn:Y; try discriminate SECOND.
  inversion FIRST; inversion SECOND; subst first_location second_location.
  assert (DISTINCT : x <> y).
  { intro SAME; subst y; pose proof (@tensor_index_injective dimensions first second x X Y) as EQ; subst second.
    unfold cell_neq in DIFFERENT; cbn in DIFFERENT; destruct DIFFERENT as [BAD|BAD];
      [congruence|apply BAD,veq_refl]. }
  right; change (8*x+8 <= 8*y \/ 8*y+8 <= 8*x).
  destruct (Z.lt_trichotomy x y) as [LT|[EQ|GT]]; [left|exfalso|right]; lia.
Qed.

Definition global_double_locations (ge : genv) (layouts : PTree.t (list Z)) (cell : MemCell) :=
  match Genv.find_symbol ge (arr_id cell), layouts ! (arr_id cell) with
  | Some block, Some dimensions => match tensor_index dimensions (arr_index cell) with
      | Some index => Some (MemoryLocation Mfloat64 block (8*index)) | None => None end
  | _, _ => None end.

Theorem global_double_locations_nonalias ge layouts :
  locations_nonalias (global_double_locations ge layouts).
Proof.
  intros [first_id first] [second_id second] first_location second_location FIRST SECOND DIFFERENT.
  unfold global_double_locations in FIRST,SECOND; cbn [arr_id arr_index] in FIRST,SECOND.
  destruct (Genv.find_symbol ge first_id) as [first_block|] eqn:FID; try discriminate FIRST.
  destruct (layouts ! first_id) as [first_dimensions|] eqn:FD; try discriminate FIRST.
  destruct (tensor_index first_dimensions first) as [x|] eqn:X; try discriminate FIRST.
  destruct (Genv.find_symbol ge second_id) as [second_block|] eqn:SID; try discriminate SECOND.
  destruct (layouts ! second_id) as [second_dimensions|] eqn:SD; try discriminate SECOND.
  destruct (tensor_index second_dimensions second) as [y|] eqn:Y; try discriminate SECOND.
  inversion FIRST; inversion SECOND; subst first_location second_location.
  destruct (peq first_id second_id) as [SAME|OTHER].
  - subst second_id; assert (second_block = first_block) by congruence; subst second_block.
    assert (second_dimensions = first_dimensions) by congruence; subst second_dimensions.
    assert (DISTINCT : x <> y).
    { intro SAME; subst y; pose proof (@tensor_index_injective first_dimensions first second x X Y) as EQ; subst second.
      unfold cell_neq in DIFFERENT; cbn in DIFFERENT; destruct DIFFERENT as [BAD|BAD];
        [congruence|apply BAD,veq_refl]. }
    right; change (8*x+8 <= 8*y \/ 8*y+8 <= 8*x).
    destruct (Z.lt_trichotomy x y) as [LT|[EQ|GT]]; [left|exfalso|right]; lia.
  - left; cbn; intro SAME; subst second_block.
    apply OTHER; exact (@Senv.find_symbol_injective (Genv.to_senv ge) first_id second_id first_block FID SID).
Qed.

Definition double_row_type columns := Tarray memory_double_type columns noattr.
Definition double_matrix_type rows columns := Tarray (double_row_type columns) rows noattr.
Definition memory_long_type := Tlong Signed noattr.
Definition double_global_binding (ge : genv) (locals : env) identifier block :=
  locals ! identifier = None /\ Genv.find_symbol ge identifier = Some block.
Definition double_matrix_lvalue array rows columns row column :=
  Ederef (Ebinop Oadd
    (Ederef (Ebinop Oadd (Evar array (double_matrix_type rows columns)) row
      (Tpointer (double_row_type columns) noattr)) (double_row_type columns))
    column (Tpointer memory_double_type noattr)) memory_double_type.

Lemma double_pointer_long_repr value : Ptrofs.of_int64 (Int64.repr value) = Ptrofs.repr value.
Proof.
  apply Ptrofs.agree64_of_int_eq; apply Ptrofs.agree64_repr; reflexivity.
Qed.
Lemma double_pointer_multiply first second :
  Ptrofs.mul (Ptrofs.repr first) (Ptrofs.repr second) = Ptrofs.repr (first*second).
Proof.
  unfold Ptrofs.mul; apply Ptrofs.eqm_samerepr; apply Ptrofs.eqm_mult;
    apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
Qed.
Lemma double_pointer_add first second :
  Ptrofs.add (Ptrofs.repr first) (Ptrofs.repr second) = Ptrofs.repr (first+second).
Proof.
  unfold Ptrofs.add; apply Ptrofs.eqm_samerepr; apply Ptrofs.eqm_add;
    apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
Qed.

Lemma double_global_reference ge locals temps memory identifier ty block :
  double_global_binding ge locals identifier block -> access_mode ty = By_reference ->
  eval_expr ge locals temps memory (Evar identifier ty) (Vptr block Ptrofs.zero).
Proof.
  intros [ABSENT SYMBOL] MODE; eapply eval_Elvalue with (loc:=block) (ofs:=Ptrofs.zero) (bf:=Full).
  - apply eval_Evar_global; assumption.
  - apply deref_loc_reference; exact MODE.
Qed.

Theorem double_matrix_lvalue_execution ge locals temps memory array rows columns row column block i j :
  double_global_binding ge locals array block -> 0 < columns ->
  typeof row = memory_long_type -> typeof column = memory_long_type ->
  eval_expr ge locals temps memory row (Vlong (Int64.repr i)) ->
  eval_expr ge locals temps memory column (Vlong (Int64.repr j)) ->
  eval_lvalue ge locals temps memory (double_matrix_lvalue array rows columns row column)
    block (Ptrofs.repr (8*(i*columns+j))) Full.
Proof.
  intros GLOBAL COLUMNS RT CT ROW COLUMN.
  unfold double_matrix_lvalue; apply eval_Ederef.
  eapply eval_Ebinop with (v1 := Vptr block (Ptrofs.repr (8*(i*columns)))) (v2 := Vlong (Int64.repr j)).
  - eapply eval_Elvalue with (loc:=block) (ofs:=Ptrofs.repr (8*(i*columns))) (bf:=Full).
    + apply eval_Ederef; eapply eval_Ebinop with
        (v1 := Vptr block Ptrofs.zero) (v2 := Vlong (Int64.repr i)).
      * eapply double_global_reference; [exact GLOBAL|reflexivity].
      * exact ROW.
      * cbn [typeof]; rewrite RT.
        change (Some (Vptr block (Ptrofs.add Ptrofs.zero
          (Ptrofs.mul (Ptrofs.repr (8*Z.max 0 columns)) (Ptrofs.of_int64 (Int64.repr i))))) =
          Some (Vptr block (Ptrofs.repr (8*(i*columns))))).
        rewrite Z.max_r by lia; rewrite double_pointer_long_repr, Ptrofs.add_zero_l, double_pointer_multiply.
        f_equal; f_equal; f_equal; ring.
    + apply deref_loc_reference; reflexivity.
  - exact COLUMN.
  - cbn [typeof]; rewrite CT.
    change (Some (Vptr block (Ptrofs.add (Ptrofs.repr (8*(i*columns)))
      (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 (Int64.repr j))))) =
      Some (Vptr block (Ptrofs.repr (8*(i*columns+j))))).
    rewrite double_pointer_long_repr, double_pointer_multiply, double_pointer_add.
    f_equal; f_equal; f_equal; ring.
Qed.

Lemma double_raw_loadv memory block index :
  0 <= 8*index -> 8*index+8 <= Ptrofs.modulus ->
  Mem.loadv Mfloat64 memory (Vptr block (Ptrofs.repr (8*index))) =
  Mem.load Mfloat64 memory block (8*index).
Proof.
  intros LOWER UPPER; cbn [Mem.loadv].
  rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
  destruct (zle (8*index+size_chunk Mfloat64) Ptrofs.modulus); [reflexivity|].
  change (size_chunk Mfloat64) with 8 in *; lia.
Qed.
Lemma double_raw_storev memory block index value :
  0 <= 8*index -> 8*index+8 <= Ptrofs.modulus ->
  Mem.storev Mfloat64 memory (Vptr block (Ptrofs.repr (8*index))) value =
  Mem.store Mfloat64 memory block (8*index) value.
Proof.
  intros LOWER UPPER; cbn [Mem.storev].
  rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
  destruct (zle (8*index+size_chunk Mfloat64) Ptrofs.modulus); [reflexivity|].
  change (size_chunk Mfloat64) with 8 in *; lia.
Qed.

Theorem double_matrix_load_receipt ge locals temps memory array rows columns row column block i j value :
  double_global_binding ge locals array block -> 0 < columns ->
  typeof row = memory_long_type -> typeof column = memory_long_type ->
  eval_expr ge locals temps memory row (Vlong (Int64.repr i)) ->
  eval_expr ge locals temps memory column (Vlong (Int64.repr j)) ->
  0 <= 8*(i*columns+j) -> 8*(i*columns+j)+8 <= Ptrofs.modulus ->
  Mem.load Mfloat64 memory block (8*(i*columns+j)) = Some value ->
  eval_expr ge locals temps memory (double_matrix_lvalue array rows columns row column) value.
Proof.
  intros GLOBAL COLUMNS RT CT ROW COLUMN LOWER UPPER LOAD.
  eapply eval_Elvalue; [eapply double_matrix_lvalue_execution; eauto|].
  apply deref_loc_value with (chunk := Mfloat64); [reflexivity|].
  rewrite double_raw_loadv by assumption; exact LOAD.
Qed.

Lemma double_cell_alignment index : (align_chunk Mfloat64 | 8*index).
Proof. change (8 | 8*index); exists index; ring. Qed.

Print Assumptions double_tensor_locations_nonalias.
Print Assumptions global_double_locations_nonalias.
Print Assumptions double_matrix_lvalue_execution.
Print Assumptions double_matrix_load_receipt.
