From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightRectangularStore ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryMultipleArrays
  GuardMemoryRegistryBackend GuardMemoryLayoutRegistry GuardMemoryLayoutOperations GuardMemoryLayoutRanges
  GuardMemoryAffineAccessExpressions GuardMemoryAffineAccess GuardMemoryAffineCopy GuardMemoryGeneralLayoutOperations.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition memory_index_offset_box_check rows columns extent term :=
  (0 <? rows) && (0 <? columns) && (0 <=? memory_index_row term) &&
  (0 <=? memory_index_column term) && (0 <=? memory_index_bias term) &&
  (memory_index_value term (rows-1) (columns-1) <? extent).
Lemma memory_index_offset_box_sound rows columns extent term :
  memory_index_offset_box_check rows columns extent term = true ->
  forall i j, 0 <= i < rows -> 0 <= j < columns -> 0 <= memory_index_value term i j < extent.
Proof.
  unfold memory_index_offset_box_check; rewrite !andb_true_iff,!Z.ltb_lt,!Z.leb_le.
  intros [[[[[ROWS COLUMNS] ROW] COLUMN] BIAS] LAST] i j I J.
  unfold memory_index_value in *; nia.
Qed.
Definition memory_offset_access_valid base row column access :=
  rectangle_layout_valid (memory_access_shape access) /\
  memory_encode_index row column (memory_access_expression access) = Some (memory_access_index access) /\
  forall i j, 0 <= i < rectangle_outer_limit base -> 0 <= j < rectangle_stride base ->
    0 <= memory_index_value (memory_access_index access) i j < rectangle_extent (memory_access_shape access).
Definition memory_offset_access_check base row column access :=
  rectangle_layout_check (memory_access_shape access) &&
  memory_index_offset_box_check (rectangle_outer_limit base) (rectangle_stride base)
    (rectangle_extent (memory_access_shape access)) (memory_access_index access) &&
  match memory_encode_index row column (memory_access_expression access) with
  | Some term => if memory_affine_index_eq term (memory_access_index access) then true else false
  | None => false end.
Lemma memory_offset_access_check_sound base row column access :
  memory_offset_access_check base row column access = true -> memory_offset_access_valid base row column access.
Proof.
  unfold memory_offset_access_check; rewrite !andb_true_iff.
  intros [[LAYOUT BOX] ENCODE].
  destruct (memory_encode_index row column (memory_access_expression access)) as [term|] eqn:EXPRESSION; [|discriminate].
  destruct (memory_affine_index_eq term (memory_access_index access)) as [SAME|]; [subst term|discriminate].
  split; [apply rectangle_layout_check_sound; exact LAYOUT|]; split; [exact EXPRESSION|].
  eapply memory_index_offset_box_sound; exact BOX.
Qed.
Definition memory_offset_operation_valid base row column operation := match operation with
  | MemoryGeneralLayout operation => Forall (fun descriptor =>
      rectangle_layout_valid (memory_descriptor_shape descriptor) /\
      memory_layout_range base (memory_descriptor_shape descriptor)) (memory_layout_operation_requests operation)
  | MemoryGeneralAffineCopy write read => memory_offset_access_valid base row column write /\ memory_offset_access_valid base row column read end.
Definition memory_offset_operation_check base row column operation := match operation with
  | MemoryGeneralLayout operation => memory_layout_requests_check base (memory_layout_operation_requests operation)
  | MemoryGeneralAffineCopy write read => memory_offset_access_check base row column write && memory_offset_access_check base row column read end.
Lemma memory_offset_operation_check_sound base row column operation :
  memory_offset_operation_check base row column operation = true -> memory_offset_operation_valid base row column operation.
Proof.
  destruct operation; cbn [memory_offset_operation_check memory_offset_operation_valid].
  - apply memory_layout_requests_check_sound.
  - rewrite andb_true_iff; intros [WRITE READ]; split; apply memory_offset_access_check_sound; assumption.
Qed.
Lemma memory_offset_operation_inverse base row column operation fe ge locals temps memory after final i j :
  rectangle_layout_valid base -> row <> column -> memory_offset_operation_valid base row column operation ->
  0 <= i < rectangle_outer_limit base -> 0 <= j < rectangle_stride base ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  exec_stmt fe ge locals temps memory (memory_general_layout_statement row column operation) E0 after final Out_normal ->
  memory_general_layout_physical ge locals i j operation memory final /\ after = temps.
Proof.
  destruct operation as [operation|write read]; intros VALID DISTINCT CERT I J ROW COLUMN RUN; cbn in RUN |- *.
  - eapply memory_layout_operation_clight_inverse; [|exact ROW|exact COLUMN|exact RUN].
    eapply memory_layout_request_indices; eassumption.
  - destruct CERT as [[WV [WE WB]] [RV [RE RB]]].
    eapply memory_affine_copy_inverse; [exact WV|exact RV|exact DISTINCT|exact WE|exact RE|
      exact ROW|exact COLUMN|apply WB; assumption|apply RB; assumption|exact RUN].
Qed.
Lemma memory_offset_descriptor_valid base row column operation :
  memory_offset_operation_valid base row column operation ->
  Forall (fun descriptor => rectangle_layout_valid (memory_descriptor_shape descriptor)) (memory_general_layout_requests operation).
Proof.
  destruct operation as [operation|write read]; cbn; intro CERT.
  - eapply Forall_impl; [|exact CERT]; intros descriptor [VALID RANGE]; exact VALID.
  - destruct CERT as [[WV REST] [RV REST']]; constructor; [exact WV|]; constructor; [exact RV|constructor].
Qed.
Theorem memory_offset_operation_registry_execution base row column descriptors entries ge locals operation i j before after :
  rectangle_layout_valid base -> Forall2 (memory_descriptor_binding ge locals) descriptors entries ->
  memory_descriptors_cover descriptors (memory_general_layout_requests operation) -> NoDup (map memory_array_id entries) ->
  memory_offset_operation_valid base row column operation ->
  0 <= i < rectangle_outer_limit base -> 0 <= j < rectangle_stride base ->
  (memory_general_layout_physical ge locals i j operation before after <->
    memory_point (memory_general_layout_instruction operation) i j
      (RuntimeState (memory_array_registry entries) before) (RuntimeState (memory_array_registry entries) after)).
Proof.
  destruct operation as [operation|write read]; intros VALID ARRAYS COVER UNIQUE CERT I J; cbn in COVER |- *.
  - apply memory_layout_operation_registry_execution with (descriptors := descriptors); auto.
    eapply memory_layout_request_indices; eassumption.
  - destruct CERT as [[WV [WE WB]] [RV [RE RB]]].
    apply memory_affine_copy_registry_point with (descriptors := descriptors); auto.
Qed.
Print Assumptions memory_index_offset_box_sound.
Print Assumptions memory_offset_operation_inverse.
Print Assumptions memory_offset_operation_registry_execution.
