From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers Maps Coqlib.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From polcert.src Require Import PolyBase.
From polcert.lib Require Import Linalg.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryValueInstr GuardMemoryDoubleValue
  GuardMemoryDynamicTensorLayout GuardMemoryDoubleLocations GuardMemoryDoubleAssignment GuardMemoryDoubleAffineLong.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Actual global-array code for arbitrary tensor rank. Layouts describe the
    declared C array dimensions. No memory load or successful floating result
    is assumed by the static certificate. *)
Fixpoint double_tensor_type dimensions :=
  match dimensions with [] => memory_double_type
  | dimension::rest => Tarray (double_tensor_type rest) dimension noattr end.
Fixpoint double_tensor_lvalue_code current dimensions coordinates : option expr :=
  match dimensions,coordinates with
  | [],[] => Some current
  | _::rest,coordinate::tail => double_tensor_lvalue_code
      (Ederef (Ebinop Oadd current coordinate (Tpointer (double_tensor_type rest) noattr))
        (double_tensor_type rest)) rest tail
  | _,_ => None end.
Lemma double_tensor_size cenv dimensions : Forall (fun dimension => 0<dimension) dimensions ->
  sizeof cenv (double_tensor_type dimensions)=8*tensor_volume dimensions.
Proof.
  intro POSITIVE; induction POSITIVE; cbn [double_tensor_type tensor_volume sizeof].
  - reflexivity.
  - rewrite IHPOSITIVE,Z.max_r by lia; ring.
Qed.
Lemma double_tensor_lvalue_type dimensions : forall current coordinates code,
  typeof current=double_tensor_type dimensions ->
  double_tensor_lvalue_code current dimensions coordinates=Some code -> typeof code=memory_double_type.
Proof.
  induction dimensions; intros current coordinates code TYPE CODE; destruct coordinates; cbn in CODE;
    try discriminate.
  - inversion CODE; subst; exact TYPE.
  - eapply IHdimensions; [|exact CODE]; reflexivity.
Qed.
Lemma double_tensor_lvalue_execution dimensions : forall ge locals temps memory current codes coordinates block base index code,
  typeof current=double_tensor_type dimensions ->
  eval_lvalue ge locals temps memory current block (Ptrofs.repr base) Full ->
  Forall2 (fun code value => typeof code=memory_long_type /\
    eval_expr ge locals temps memory code (Vlong (Int64.repr value))) codes coordinates ->
  tensor_index dimensions coordinates=Some index ->
  double_tensor_lvalue_code current dimensions codes=Some code ->
  eval_lvalue ge locals temps memory code block (Ptrofs.repr (base+8*index)) Full.
Proof.
  induction dimensions as [|dimension rest IH]; intros ge locals temps memory current codes coordinates
    block base index code TYPE ADDRESS OPERANDS INDEX CODE;
    destruct coordinates as [|coordinate tail]; cbn [tensor_index] in INDEX; try discriminate.
  - inversion OPERANDS; subst codes; cbn [double_tensor_lvalue_code] in CODE.
    inversion CODE; subst code; inversion INDEX; subst index.
    replace (base+8*0) with base by ring; exact ADDRESS.
  - inversion OPERANDS as [|head value codes' coordinates' [CTYPE COORDINATE] TAIL]; subst codes coordinates'.
    destruct ((0<=?coordinate)&&(coordinate<?dimension)) eqn:RANGE; try discriminate.
    destruct (tensor_index rest tail) as [suffix|] eqn:SUFFIX; try discriminate.
    inversion INDEX; subst index.
    cbn [double_tensor_lvalue_code] in CODE.
    assert (NEXT : eval_lvalue ge locals temps memory
      (Ederef (Ebinop Oadd current head (Tpointer (double_tensor_type rest) noattr)) (double_tensor_type rest))
      block (Ptrofs.repr (base+8*coordinate*tensor_volume rest)) Full).
    { apply eval_Ederef; eapply eval_Ebinop with
        (v1:=Vptr block (Ptrofs.repr base)) (v2:=Vlong (Int64.repr coordinate)).
      - eapply eval_Elvalue; [exact ADDRESS|].
        rewrite TYPE; apply deref_loc_reference; reflexivity.
      - exact COORDINATE.
      - rewrite TYPE,CTYPE; cbn [double_tensor_type sem_binary_operation classify_add typeconv].
        change (Some (Vptr block (Ptrofs.add (Ptrofs.repr base)
          (Ptrofs.mul (Ptrofs.repr (sizeof ge (double_tensor_type rest)))
            (Ptrofs.of_int64 (Int64.repr coordinate)))))=
          Some (Vptr block (Ptrofs.repr (base+8*coordinate*tensor_volume rest)))).
        rewrite double_tensor_size by (eapply tensor_index_positive_dimensions; exact SUFFIX).
        rewrite double_pointer_long_repr,double_pointer_multiply,double_pointer_add.
        replace (8*tensor_volume rest*coordinate) with (8*coordinate*tensor_volume rest) by ring.
        reflexivity. }
    pose proof (@IH ge locals temps memory
      (Ederef (Ebinop Oadd current head (Tpointer (double_tensor_type rest) noattr)) (double_tensor_type rest)) codes' tail block
      (base+8*coordinate*tensor_volume rest) suffix code eq_refl NEXT TAIL SUFFIX CODE) as RESULT.
    replace (base+8*(coordinate*tensor_volume rest+suffix)) with
      (base+8*coordinate*tensor_volume rest+8*suffix) by ring; exact RESULT.
Qed.

Definition double_tensor_static (ge : genv) (locals : env) (layouts : PTree.t (list Z)) :=
  forall array dimensions, layouts ! array=Some dimensions ->
    locals ! array=None /\ 8*tensor_volume dimensions<=Ptrofs.modulus.
Definition double_lower_access (layouts : PTree.t (list Z)) codes (access : AccessFunction) :=
  match layouts ! (fst access) with
  | Some dimensions => double_tensor_lvalue_code
    (Evar (fst access) (double_tensor_type dimensions)) dimensions (map (double_long_affine codes) (snd access))
  | None => None end.
Fixpoint double_lower_reads layouts codes accesses :=
  match accesses with
  | [] => Some []
  | access::rest => match double_lower_access layouts codes access,double_lower_reads layouts codes rest with
    | Some code,Some tail => Some (code::tail) | _,_ => None end end.
Definition double_lower_instruction layouts (instruction : DoubleAssignmentInstr.t) codes :=
  match double_lower_access layouts codes (value_instruction_write instruction),
    double_lower_reads layouts codes (value_instruction_reads instruction) with
  | Some lhs,Some loads => match double_value_code loads (value_instruction_code instruction) with
    | Some rhs => Some (Sassign lhs rhs) | None => None end
  | _,_ => None end.

Theorem double_lower_access_receipt ge locals temps memory layouts codes values access location code :
  double_tensor_static ge locals layouts ->
  Forall2 (double_ranged_operand ge locals temps memory) codes values ->
  double_lower_access layouts codes access=Some code ->
  global_double_locations ge layouts (exact_cell access values)=Some location ->
  double_memory_location_receipt ge locals temps memory code location.
Proof.
  intros STATIC OPERANDS CODE RESOLVE; destruct access as [array rows].
  unfold double_lower_access in CODE; cbn [fst snd] in CODE.
  unfold global_double_locations in RESOLVE; cbn [exact_cell arr_id arr_index fst snd] in RESOLVE.
  destruct (Genv.find_symbol ge array) as [block|] eqn:SYMBOL; try discriminate.
  destruct (layouts ! array) as [dimensions|] eqn:LAYOUT; try discriminate.
  destruct (tensor_index dimensions (affine_product rows values)) as [index|] eqn:INDEX; try discriminate.
  inversion RESOLVE; subst location.
  destruct (STATIC array dimensions LAYOUT) as [LOCAL SPAN].
  pose proof (@tensor_index_bounds dimensions _ index INDEX) as RANGE.
  unfold double_memory_location_receipt; split.
  - eapply double_tensor_lvalue_type; [|exact CODE]; reflexivity.
  - split; [reflexivity|]; split; [cbn; lia|]; split.
    + cbn; nia.
    + replace (8*index) with (0+8*index) by ring.
      eapply (@double_tensor_lvalue_execution dimensions ge locals temps memory
        (Evar array (double_tensor_type dimensions)) (map (double_long_affine codes) rows)
        (affine_product rows values) block 0 index code); [reflexivity| | |exact INDEX|exact CODE].
      * change (eval_lvalue ge locals temps memory (Evar array (double_tensor_type dimensions)) block Ptrofs.zero Full).
        apply eval_Evar_global; assumption.
      * apply double_long_affines_execution; exact OPERANDS.
Qed.
Lemma double_lower_reads_receipts ge locals temps memory layouts codes values accesses locations loads :
  double_tensor_static ge locals layouts ->
  Forall2 (double_ranged_operand ge locals temps memory) codes values ->
  double_lower_reads layouts codes accesses=Some loads ->
  resolve_cells (map (fun access => exact_cell access values) accesses) (global_double_locations ge layouts)=Some locations ->
  Forall2 (double_memory_location_receipt ge locals temps memory) loads locations.
Proof.
  intros STATIC OPERANDS; revert locations loads; induction accesses as [|access rest IH];
    intros locations loads CODE RESOLVE; cbn [double_lower_reads] in CODE; cbn [map resolve_cells] in RESOLVE.
  - inversion CODE; inversion RESOLVE; constructor.
  - destruct (double_lower_access layouts codes access) as [code|] eqn:ACCESS; try discriminate.
    destruct (double_lower_reads layouts codes rest) as [tail|] eqn:REST; try discriminate.
    destruct (global_double_locations ge layouts (exact_cell access values)) as [location|] eqn:LOCATION; try discriminate.
    destruct (resolve_cells (map (fun access => exact_cell access values) rest) (global_double_locations ge layouts))
      as [remaining|] eqn:REMAINING; try discriminate.
    inversion CODE; inversion RESOLVE; subst loads locations; constructor.
    + eapply double_lower_access_receipt; eauto.
    + eapply IH; eauto.
Qed.
Definition double_tensor_view ge layouts state memory :=
  runtime_locations state=global_double_locations ge layouts /\ runtime_memory state=memory.
Theorem double_tensor_instruction_execution fe ge locals temps memory layouts codes values instruction code
  source target writes reads :
  double_tensor_static ge locals layouts ->
  double_lower_instruction layouts instruction codes=Some code ->
  Forall2 (double_ranged_operand ge locals temps memory) codes values ->
  DoubleAssignmentInstr.instr_semantics instruction values writes reads source target ->
  double_tensor_view ge layouts source memory ->
  exists final, double_tensor_view ge layouts target final /\
    exec_stmt fe ge locals temps memory code E0 temps final Out_normal.
Proof.
  intros STATIC CODE OPERANDS [_ [READS [write [actual_reads [WRITE [READ [REG RUN]]]]]]] [LOCATIONS MEMORY].
  subst reads; rewrite LOCATIONS in WRITE,READ; rewrite MEMORY in RUN.
  unfold double_lower_instruction in CODE.
  destruct (double_lower_access layouts codes (value_instruction_write instruction)) as [lhs|] eqn:LHS; try discriminate.
  destruct (double_lower_reads layouts codes (value_instruction_reads instruction)) as [loads|] eqn:LOADS; try discriminate.
  destruct (double_value_code loads (value_instruction_code instruction)) as [rhs|] eqn:RHS; try discriminate.
  inversion CODE; subst code.
  exists (runtime_memory target); split.
  - split; [rewrite REG; exact LOCATIONS|reflexivity].
  - eapply double_assignment_lowered_execution.
    + eapply double_lower_reads_receipts; eauto.
    + eapply double_lower_access_receipt; eauto.
    + exact RHS.
    + exact RUN.
Qed.

Print Assumptions double_tensor_size.
Print Assumptions double_tensor_lvalue_execution.
Print Assumptions double_lower_access_receipt.
Print Assumptions double_tensor_instruction_execution.
