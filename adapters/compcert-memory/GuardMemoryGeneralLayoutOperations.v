From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightRectangularStore ClightRectangularGuard ClightRegionProgress ClightLoopSyntax ClightStraightLine ClightTempFrame CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryMultipleArrays
  GuardMemoryRegistryBackend GuardMemoryLayoutRegistry GuardMemoryLayoutOperations GuardMemoryLayoutRanges
  GuardMemoryAffineAccessExpressions GuardMemoryAffineAccess GuardMemoryAffineCopy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_index_eq : forall a b : memory_affine_index, {a=b}+{a<>b}.
Proof. decide equality; apply Z.eq_dec. Defined.
Definition memory_affine_access_valid base row column access :=
  rectangle_layout_valid (memory_access_shape access) /\
  memory_encode_index row column (memory_access_expression access) = Some (memory_access_index access) /\
  memory_index_value (memory_access_index access) 0 0 = 0 /\
  forall i j, 0 <= i < rectangle_outer_limit base -> 0 <= j < rectangle_stride base ->
    0 <= memory_index_value (memory_access_index access) i j < rectangle_extent (memory_access_shape access).
Definition memory_affine_access_check base row column access :=
  rectangle_layout_check (memory_access_shape access) &&
  memory_index_box_check (rectangle_outer_limit base) (rectangle_stride base)
    (rectangle_extent (memory_access_shape access)) (memory_access_index access) &&
  match memory_encode_index row column (memory_access_expression access) with
  | Some term => if memory_affine_index_eq term (memory_access_index access) then true else false
  | None => false end.
Lemma memory_affine_access_check_sound base row column access :
  memory_affine_access_check base row column access = true -> memory_affine_access_valid base row column access.
Proof.
  unfold memory_affine_access_check; rewrite !andb_true_iff.
  intros [[LAYOUT BOX] ENCODE].
  destruct (memory_encode_index row column (memory_access_expression access)) as [term|] eqn:EXPRESSION; [|discriminate].
  destruct (memory_affine_index_eq term (memory_access_index access)) as [SAME|]; [subst term|discriminate].
  split; [apply rectangle_layout_check_sound; exact LAYOUT|].
  split; [exact EXPRESSION|]; split; [eapply memory_index_box_zero; exact BOX|].
  eapply memory_index_box_sound; exact BOX.
Qed.

Inductive memory_general_layout_operation :=
| MemoryGeneralLayout (operation : memory_layout_operation)
| MemoryGeneralAffineCopy (write read : memory_affine_access).
Definition memory_general_layout_requests operation := match operation with
  | MemoryGeneralLayout operation => memory_layout_operation_requests operation
  | MemoryGeneralAffineCopy write read => [memory_access_descriptor write;memory_access_descriptor read] end.
Definition memory_general_layout_instruction operation := match operation with
  | MemoryGeneralLayout operation => memory_layout_operation_instruction operation
  | MemoryGeneralAffineCopy write read => memory_affine_copy_instruction write read end.
Definition memory_general_layout_statement row column operation := match operation with
  | MemoryGeneralLayout operation => memory_layout_operation_statement row column operation
  | MemoryGeneralAffineCopy write read => memory_affine_copy_statement write read end.
Definition memory_general_layout_physical ge locals i j operation := match operation with
  | MemoryGeneralLayout operation => memory_layout_operation_physical ge locals i j operation
  | MemoryGeneralAffineCopy write read => memory_affine_copy_physical ge locals write read i j end.
Definition memory_general_layout_valid base row column operation := match operation with
  | MemoryGeneralLayout operation => Forall (fun descriptor =>
      rectangle_layout_valid (memory_descriptor_shape descriptor) /\
      memory_layout_range base (memory_descriptor_shape descriptor)) (memory_layout_operation_requests operation)
  | MemoryGeneralAffineCopy write read =>
      memory_affine_access_valid base row column write /\ memory_affine_access_valid base row column read end.
Definition memory_general_layout_check base row column operation := match operation with
  | MemoryGeneralLayout operation => memory_layout_requests_check base (memory_layout_operation_requests operation)
  | MemoryGeneralAffineCopy write read => memory_affine_access_check base row column write && memory_affine_access_check base row column read end.
Lemma memory_general_layout_check_sound base row column operation :
  memory_general_layout_check base row column operation = true -> memory_general_layout_valid base row column operation.
Proof.
  destruct operation; cbn [memory_general_layout_check memory_general_layout_valid].
  - apply memory_layout_requests_check_sound.
  - rewrite andb_true_iff; intros [WRITE READ]; split; apply memory_affine_access_check_sound; assumption.
Qed.
Lemma memory_general_layout_normal row column operation :
  normal_statement (memory_general_layout_statement row column operation) = true.
Proof. destruct operation; cbn [memory_general_layout_statement memory_affine_copy_statement]; [apply memory_layout_operation_normal|reflexivity]. Qed.
Lemma memory_general_layout_quiet row column operation :
  quiet_statement (memory_general_layout_statement row column operation) = true.
Proof. destruct operation; cbn [memory_general_layout_statement memory_affine_copy_statement]; [apply memory_layout_operation_quiet|reflexivity]. Qed.
Lemma memory_general_layout_writes row column operation :
  writes_only [] (memory_general_layout_statement row column operation).
Proof. destruct operation; cbn [memory_general_layout_statement memory_affine_copy_statement]; [apply memory_layout_operation_writes|constructor]. Qed.

Lemma memory_general_layout_clight_inverse base row column operation fe ge locals temps memory after final i j :
  rectangle_layout_valid base -> row <> column -> memory_general_layout_valid base row column operation ->
  0 <= i < rectangle_outer_limit base -> 0 <= j < rectangle_stride base ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  exec_stmt fe ge locals temps memory (memory_general_layout_statement row column operation) E0 after final Out_normal ->
  memory_general_layout_physical ge locals i j operation memory final /\ after = temps.
Proof.
  destruct operation as [operation|write read]; intros VALID DISTINCT CERT I J ROW COLUMN RUN; cbn in RUN |- *.
  - eapply memory_layout_operation_clight_inverse; [|exact ROW|exact COLUMN|exact RUN].
    eapply memory_layout_request_indices; eassumption.
  - destruct CERT as [[WV [WE [WZ WB]]] [RV [RE [RZ RB]]]].
    eapply memory_affine_copy_inverse; [exact WV|exact RV|exact DISTINCT|exact WE|exact RE|
      exact ROW|exact COLUMN|apply WB; assumption|apply RB; assumption|exact RUN].
Qed.
Lemma memory_general_layout_physical_store ge locals operation i j before after :
  memory_general_layout_physical ge locals i j operation before after ->
  exists block offset value, Mem.store Mint32 before block offset value = Some after.
Proof.
  destruct operation as [operation|write read]; cbn.
  - intro RUN; destruct (@memory_layout_operation_physical_store ge locals operation i j before after RUN)
      as [block [value STORE]]; eauto.
  - intros [wb [rb [_ [_ [inputs [value [_ [_ STORE]]]]]]]]; eauto.
Qed.
Lemma memory_general_layout_initial_bindings base row column ge locals operation before after :
  memory_general_layout_valid base row column operation ->
  memory_general_layout_physical ge locals 0 0 operation before after ->
  forall descriptor, In descriptor (memory_general_layout_requests operation) ->
    exists block, rect_array_binding (memory_descriptor_shape descriptor) ge locals
      (memory_descriptor_variable descriptor) block /\ Mem.valid_pointer before block 0 = true.
Proof.
  destruct operation as [operation|write read]; cbn; intros CERT RUN.
  - eapply memory_layout_operation_initial_bindings; exact RUN.
  - destruct CERT as [[WV [WE [WZ WB]]] [RV [RE [RZ RB]]]].
    eapply memory_affine_copy_initial_bindings; eassumption.
Qed.
Theorem memory_general_layout_registry_execution base row column descriptors entries ge locals operation i j before after :
  rectangle_layout_valid base ->
  Forall2 (memory_descriptor_binding ge locals) descriptors entries ->
  memory_descriptors_cover descriptors (memory_general_layout_requests operation) ->
  NoDup (map memory_array_id entries) -> memory_general_layout_valid base row column operation ->
  0 <= i < rectangle_outer_limit base -> 0 <= j < rectangle_stride base ->
  (memory_general_layout_physical ge locals i j operation before after <->
    memory_point (memory_general_layout_instruction operation) i j
      (RuntimeState (memory_array_registry entries) before) (RuntimeState (memory_array_registry entries) after)).
Proof.
  destruct operation as [operation|write read]; intros VALID ARRAYS COVER UNIQUE CERT I J; cbn in COVER |- *.
  - apply memory_layout_operation_registry_execution with (descriptors := descriptors); auto.
    eapply memory_layout_request_indices; eassumption.
  - destruct CERT as [[WV [WE [WZ WB]]] [RV [RE [RZ RB]]]].
    apply memory_affine_copy_registry_point with (descriptors := descriptors); auto.
Qed.
Print Assumptions memory_general_layout_clight_inverse.
Print Assumptions memory_general_layout_registry_execution.
