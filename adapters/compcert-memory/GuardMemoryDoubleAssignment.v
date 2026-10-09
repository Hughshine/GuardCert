From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Integers Floats Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightPureExpr CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryValueInstr GuardMemoryDoubleValue GuardMemoryDoubleSource
  GuardMemoryDoubleLocations GuardMemoryObservationDeterminism.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A double assignment casts its result. Raw Vundef is not a successful
    assignment value, even when a memory load can return it. *)
Definition compute_double_assignment values expression :=
  match evaluate_double_value values expression with
  | Some (Vfloat value) => Some (Vfloat value) | _ => None end.
Module DoubleAssignmentValue <: MEMORY_VALUE_CODE.
  Definition t := double_value_expression.
  Definition eq_dec := double_value_expression_eq_dec.
  Definition dummy := DoubleBits 0.
  Definition evaluate (_ : list Z) := compute_double_assignment.
End DoubleAssignmentValue.
Module DoubleAssignmentInstr := MakeMemoryValueInstr DoubleAssignmentValue.

Lemma compute_double_assignment_result values expression value :
  compute_double_assignment values expression = Some value ->
  evaluate_double_value values expression = Some value /\ exists number, value = Vfloat number.
Proof.
  unfold compute_double_assignment; destruct (evaluate_double_value values expression) as [result|] eqn:RESULT;
    try discriminate; destruct result; try discriminate; intro COMPUTE; inversion COMPUTE; subst; eauto.
Qed.

Fixpoint double_source_reads code : list expr :=
  match code with
  | Econst_float _ _ => []
  | Ebinop _ first second _ => double_source_reads first ++ double_source_reads second
  | Eunop Oneg child _ => double_source_reads child
  | _ => [code] end.

Theorem double_source_reads_licensed ge locals temps memory code value :
  eval_expr ge locals temps memory code value ->
  Forall (fun input => exists observed, eval_expr ge locals temps memory input observed)
    (double_source_reads code).
Proof.
  revert value; induction code as
    [i ty|f ty|f ty|i ty|id ty|id ty|code IHcode ty|code IHcode ty|
     op code IHcode ty|op code1 IHcode1 code2 IHcode2 ty|code IHcode ty|
     code IHcode field ty|other_ty ty|other_ty ty]; intros value RUN; cbn [double_source_reads];
    try solve [constructor; [exists value; exact RUN|constructor]]; try solve [constructor].
  - destruct op; cbn; try solve [constructor; [exists value; exact RUN|constructor]].
    inversion RUN; subst.
    + eapply IHcode; eauto.
    + match goal with H : eval_lvalue _ _ _ _ (Eunop _ _ _) _ _ _ |- _ => inversion H end.
  - apply scalar_binary_inv in RUN as [first [second [FIRST [SECOND OP]]]].
    apply Forall_app; split; [eapply IHcode1|eapply IHcode2]; eauto.
Qed.

Lemma double_licensed_values ge locals temps memory loads :
  Forall (fun input => typeof input = memory_double_type) loads ->
  Forall (fun input => exists observed, eval_expr ge locals temps memory input observed) loads ->
  exists values, Forall2 (fun input value => typeof input = memory_double_type /\
    eval_expr ge locals temps memory input value) loads values.
Proof.
  intros TYPES LICENSED; revert TYPES; induction LICENSED; intro TYPES.
  - exists []; constructor.
  - inversion TYPES; subst; destruct H as [value EVAL].
    destruct (IHLICENSED ltac:(assumption)) as [values RECEIPTS].
    exists (value::values); constructor; auto.
Qed.

Definition double_memory_location_receipt ge locals temps memory code location :=
  typeof code = memory_double_type /\ location_chunk location = Mfloat64 /\
  0 <= location_offset location /\ location_offset location+8 <= Ptrofs.modulus /\
  eval_lvalue ge locals temps memory code (location_block location)
    (Ptrofs.repr (location_offset location)) Full.

Lemma double_location_loadv location memory :
  location_chunk location = Mfloat64 -> 0 <= location_offset location ->
  location_offset location+8 <= Ptrofs.modulus ->
  Mem.loadv Mfloat64 memory (Vptr (location_block location) (Ptrofs.repr (location_offset location))) =
  location_load location memory.
Proof.
  intros CHUNK LOWER UPPER; unfold location_load; rewrite CHUNK; cbn [Mem.loadv].
  rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
  destruct (zle (location_offset location+size_chunk Mfloat64) Ptrofs.modulus); [reflexivity|].
  change (size_chunk Mfloat64) with 8 in *; lia.
Qed.

Lemma double_memory_read_forward ge locals temps memory code location value :
  double_memory_location_receipt ge locals temps memory code location ->
  location_load location memory = Some value ->
  eval_expr ge locals temps memory code value.
Proof.
  intros [TYPE [CHUNK [LOWER [UPPER LVALUE]]]] LOAD.
  eapply eval_Elvalue; [exact LVALUE|].
  rewrite TYPE; apply deref_loc_value with (chunk := Mfloat64); [reflexivity|].
  rewrite double_location_loadv by assumption; exact LOAD.
Qed.

Lemma double_memory_read_inverse ge locals temps memory code location value :
  double_memory_location_receipt ge locals temps memory code location ->
  eval_expr ge locals temps memory code value -> location_load location memory = Some value.
Proof.
  intros [TYPE [CHUNK [LOWER [UPPER LVALUE]]]] RUN.
  pose proof (proj2 (memory_expression_lvalue_unique ge locals temps memory)
    code _ _ _ LVALUE) as UNIQUE.
  inversion LVALUE; subst; inversion RUN; subst;
    match goal with ACTUAL : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
      destruct (UNIQUE _ _ _ ACTUAL) as [BLOCK [OFFSET BITS]]; subst end;
    match goal with READ : deref_loc _ _ _ _ _ _ |- _ =>
      rewrite TYPE in READ; inversion READ; subst; try discriminate end;
    match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end;
    match goal with LOAD : Mem.loadv _ _ _ = Some _ |- _ =>
      rewrite double_location_loadv in LOAD by assumption; exact LOAD end.
Qed.

Lemma double_memory_reads_types ge locals temps memory loads locations :
  Forall2 (double_memory_location_receipt ge locals temps memory) loads locations ->
  Forall (fun input => typeof input = memory_double_type) loads.
Proof. intro RECEIPTS; induction RECEIPTS; constructor; [exact (proj1 H)|exact IHRECEIPTS]. Qed.

Lemma double_memory_reads_forward ge locals temps memory loads locations values :
  Forall2 (double_memory_location_receipt ge locals temps memory) loads locations ->
  load_locations locations memory = Some values ->
  Forall2 (fun input value => typeof input = memory_double_type /\
    eval_expr ge locals temps memory input value) loads values.
Proof.
  intro RECEIPTS; revert values; induction RECEIPTS; intros values LOAD; cbn [load_locations] in LOAD.
  - inversion LOAD; constructor.
  - destruct (location_load y memory) as [value|] eqn:VALUE; try discriminate.
    destruct (load_locations l' memory) as [rest|] eqn:REST; try discriminate.
    inversion LOAD; subst values; constructor.
    + split; [exact (proj1 H)|eapply double_memory_read_forward; eauto].
    + eapply IHRECEIPTS; reflexivity.
Qed.

Lemma double_memory_reads_inverse ge locals temps memory loads locations values :
  Forall2 (double_memory_location_receipt ge locals temps memory) loads locations ->
  Forall2 (fun input value => typeof input = memory_double_type /\
    eval_expr ge locals temps memory input value) loads values ->
  load_locations locations memory = Some values.
Proof.
  intro RECEIPTS; revert values; induction RECEIPTS; intros values READS; inversion READS; subst; cbn [load_locations].
  - reflexivity.
  - match goal with
    HEAD : _ /\ eval_expr _ _ _ _ x _, TAIL : Forall2 _ l _ |- _ =>
      rewrite (double_memory_read_inverse H (proj2 HEAD)), (IHRECEIPTS _ TAIL); reflexivity
    end.
Qed.

Lemma double_location_storev location memory value :
  location_chunk location = Mfloat64 -> 0 <= location_offset location ->
  location_offset location+8 <= Ptrofs.modulus ->
  Mem.storev Mfloat64 memory (Vptr (location_block location) (Ptrofs.repr (location_offset location))) value =
  Mem.store Mfloat64 memory (location_block location) (location_offset location) value.
Proof.
  intros CHUNK LOWER UPPER; cbn [Mem.storev].
  rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
  destruct (zle (location_offset location+size_chunk Mfloat64) Ptrofs.modulus); [reflexivity|].
  change (size_chunk Mfloat64) with 8 in *; lia.
Qed.

Theorem double_assignment_lowered_execution fe ge locals temps memory lhs rhs loads expression locations write final :
  Forall2 (double_memory_location_receipt ge locals temps memory) loads locations ->
  double_memory_location_receipt ge locals temps memory lhs write ->
  double_value_code loads expression = Some rhs ->
  memory_action_run (MemoryAction locations write (fun values => compute_double_assignment values expression)) memory final ->
  exec_stmt fe ge locals temps memory (Sassign lhs rhs) E0 temps final Out_normal.
Proof.
  intros READS [TYPE [CHUNK [LOWER [UPPER LVALUE]]]] CODE [values [value [LOAD [COMPUTE STORE]]]].
  destruct (@compute_double_assignment_result values expression value COMPUTE) as [VALUE [number FLOAT]].
  pose proof (double_memory_reads_forward READS LOAD) as RECEIPTS.
  pose proof (double_memory_reads_types READS) as TYPES.
  pose proof (@double_value_code_type loads expression rhs TYPES CODE) as RHS.
  eapply exec_Sassign with (loc:=location_block write) (ofs:=Ptrofs.repr (location_offset write))
    (bf:=Full) (v:=value) (v2:=value).
  - exact LVALUE.
  - eapply double_value_code_execution; eauto.
  - rewrite RHS,TYPE,FLOAT; reflexivity.
  - rewrite TYPE; apply assign_loc_value with (chunk:=Mfloat64); [reflexivity|].
    rewrite double_location_storev by assumption.
    change (Mem.store (location_chunk write) memory (location_block write) (location_offset write) value = Some final) in STORE.
    rewrite CHUNK in STORE; exact STORE.
Qed.

Theorem double_assignment_source_decode fe ge locals temps memory lhs rhs expression locations write trace final_temps final outcome :
  Forall2 (double_memory_location_receipt ge locals temps memory) (double_source_reads rhs) locations ->
  double_memory_location_receipt ge locals temps memory lhs write ->
  double_value_code (double_source_reads rhs) expression = Some rhs ->
  exec_stmt fe ge locals temps memory (Sassign lhs rhs) trace final_temps final outcome ->
  trace=E0 /\ final_temps=temps /\ outcome=Out_normal /\
  memory_action_run (MemoryAction locations write (fun values => compute_double_assignment values expression)) memory final.
Proof.
  intros READS [TYPE [CHUNK [LOWER [UPPER LVALUE]]]] CODE RUN.
  pose proof (double_memory_reads_types READS) as TYPES.
  pose proof (@double_value_code_type (double_source_reads rhs) expression rhs TYPES CODE) as RHS.
  inversion RUN; subst; repeat split; try reflexivity.
  pose proof (double_source_reads_licensed H2) as LICENSED;
  destruct (double_licensed_values TYPES LICENSED) as [values RECEIPTS].
  rewrite RHS,TYPE in H6.
  destruct (@double_cast_exact memory v2 v H6) as [number [INPUT OUTPUT]].
  subst v2 v.
  exists values,(Vfloat number); split.
  - eapply double_memory_reads_inverse; eauto.
  - split.
    + change (compute_double_assignment values expression = Some (Vfloat number)).
      unfold compute_double_assignment;
      rewrite (@double_value_source_decode ge locals final_temps memory
        (double_source_reads rhs) values expression rhs (Vfloat number) RECEIPTS CODE H2); reflexivity.
    + match goal with ACTUAL : eval_lvalue _ _ _ _ lhs _ _ _ |- _ =>
    destruct (proj2 (memory_expression_lvalue_unique ge locals final_temps memory)
      lhs _ _ _ LVALUE _ _ _ ACTUAL) as [BLOCK [OFFSET BITS]]; subst end.
  match goal with ASSIGN : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    rewrite TYPE in ASSIGN; inversion ASSIGN; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  change (Mem.store (location_chunk write) memory (location_block write) (location_offset write) (Vfloat number) = Some final).
  rewrite CHUNK.
  match goal with STORE : Mem.storev _ _ _ _ = Some _ |- _ =>
    rewrite double_location_storev in STORE by assumption; exact STORE end.
Qed.

Print Assumptions double_source_reads_licensed.
Print Assumptions double_memory_reads_forward.
Print Assumptions double_memory_reads_inverse.
Print Assumptions DoubleAssignmentInstr.bc_condition_implie_permutbility.
Print Assumptions double_assignment_lowered_execution.
Print Assumptions double_assignment_source_decode.
