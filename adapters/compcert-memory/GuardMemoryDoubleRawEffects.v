From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightGlobalScope ClightRegionProgress.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleTensorBackend
  GuardMemoryDoubleSourceAccess GuardMemoryLongSourceAffine GuardMemoryDoubleAffineSourceAccess
  GuardMemoryDoubleAssignmentFactory GuardMemoryDoubleSourceInstruction GuardMemoryValueInstr.
Import ListNotations.
Set Implicit Arguments.

(** These effects are recovered from successful *source* execution, without
    accepting a guard, decoding a mathematical cell, or bounding coordinates.
    Pointer-offset wrap does not change the block of a global array. *)
Lemma decoded_long_source_index_type controls code row :
  decode_long_source_index controls code=Some row -> typeof code=memory_long_type.
Proof.
  unfold decode_long_source_index; destruct (describe_long_source_affine code) as [expression|] eqn:DESCRIBE;
    try discriminate; intro ENCODE.
  rewrite (@describe_long_source_affine_exact code expression DESCRIBE); apply long_source_affine_type.
Qed.
Lemma decoded_long_source_indices_types controls codes rows :
  decode_long_source_indices controls codes=Some rows -> Forall (fun code=>typeof code=memory_long_type) codes.
Proof.
  revert rows; induction codes as [|code rest IH]; intros rows DECODE; cbn [decode_long_source_indices] in DECODE.
  - constructor.
  - destruct (decode_long_source_index controls code) as [row|] eqn:HEAD; try discriminate.
    destruct (decode_long_source_indices controls rest) as [tail|] eqn:TAIL; try discriminate.
    constructor; [eapply decoded_long_source_index_type; exact HEAD|eapply IH; reflexivity].
Qed.

Definition double_raw_lvalue_form code := match code with Evar _ _ | Ederef _ _=>True | _=>False end.
Lemma double_raw_array_value ge locals temps memory code element count attr value :
  double_raw_lvalue_form code -> typeof code=Tarray element count attr ->
  eval_expr ge locals temps memory code value ->
  exists block offset, value=Vptr block offset /\ eval_lvalue ge locals temps memory code block offset Full.
Proof.
  intros FORM TYPE RUN; destruct code; cbn [double_raw_lvalue_form] in FORM; try contradiction;
    inversion RUN; subst;
    match goal with
    | ADDRESS : eval_lvalue _ _ _ _ _ _ _ ?bf |- _ =>
        assert (FIELD : bf=Full) by (inversion ADDRESS; reflexivity); subst bf
    end;
    match goal with
    | LOAD : deref_loc _ _ _ _ _ _ |- _ => inversion LOAD; subst
    end; try (match goal with
      | ACCESS : access_mode (typeof _) = _ |- _ => rewrite TYPE in ACCESS; discriminate
      end); eauto.
Qed.

Lemma double_raw_tensor_lvalue_origin dimensions : forall ge locals temps memory current codes code root,
  double_raw_lvalue_form current -> typeof current=double_tensor_type dimensions ->
  (forall block offset field, eval_lvalue ge locals temps memory current block offset field -> block=root /\ field=Full) ->
  Forall (fun coordinate=>typeof coordinate=memory_long_type) codes ->
  double_tensor_lvalue_code current dimensions codes=Some code ->
  forall block offset field, eval_lvalue ge locals temps memory code block offset field -> block=root /\ field=Full.
Proof.
  induction dimensions as [|count rest IH]; intros ge locals temps memory current codes code root FORM TYPE ORIGIN TYPES CODE;
    destruct codes as [|coordinate tail]; cbn [double_tensor_lvalue_code] in CODE; try discriminate.
  - inversion CODE; subst code; exact ORIGIN.
  - inversion TYPES as [|head remaining HEAD TAIL]; subst head remaining.
    eapply (@IH ge locals temps memory
      (Ederef (Ebinop Oadd current coordinate (Tpointer (double_tensor_type rest) noattr)) (double_tensor_type rest))
      tail code root); [exact I|reflexivity| |exact TAIL|exact CODE].
    intros block offset field ADDRESS; inversion ADDRESS; subst.
    match goal with RUN : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ => inversion RUN; subst end;
      try (match goal with BAD : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion BAD end).
    match goal with LEFT : eval_expr _ _ _ _ current ?value |- _ =>
      destruct (@double_raw_array_value ge locals temps memory current (double_tensor_type rest) count noattr value
        FORM TYPE LEFT) as [base [ofs [VALUE BASE]]]; subst value
    end.
    match goal with OP : sem_binary_operation _ Oadd _ _ _ _ _ = _ |- _ =>
      rewrite TYPE,HEAD in OP; cbv beta iota zeta delta [double_tensor_type memory_long_type
        sem_binary_operation sem_add sem_add_ptr_long classify_add typeconv remove_attributes change_attributes] in OP;
      match goal with RIGHT : eval_expr _ _ _ _ coordinate ?right |- _ => destruct right end;
      try discriminate; inversion OP; subst
    end.
    split; [exact (proj1 (ORIGIN _ _ _ BASE))|reflexivity].
Qed.

Theorem decoded_double_affine_source_lvalue_origin controls source access ge locals temps memory root block offset field :
  decode_double_affine_source_access controls source=Some access ->
  double_global_binding ge locals (fst (double_affine_source_function access)) root ->
  eval_lvalue ge locals temps memory source block offset field -> block=root /\ field=Full.
Proof.
  unfold decode_double_affine_source_access; destruct (describe_double_source_access source) as [raw|] eqn:RAW;
    try discriminate.
  destruct (decode_long_source_indices controls (double_source_coordinates raw)) as [rows|] eqn:ROWS; try discriminate.
  intros DECODE BIND RUN; inversion DECODE; subst access; cbn [double_affine_source_function fst] in BIND.
  pose proof (@describe_double_source_access_exact source raw RAW) as CODE.
  unfold double_source_access_code in CODE.
  eapply (@double_raw_tensor_lvalue_origin (double_source_dimensions raw) ge locals temps memory
    (Evar (double_source_array raw) (double_tensor_type (double_source_dimensions raw)))
    (double_source_coordinates raw) source root); [exact I|reflexivity| | |exact CODE|exact RUN].
  - intros actual ofs bf ADDRESS; destruct BIND as [LOCAL SYMBOL]; inversion ADDRESS; subst; split; congruence.
  - eapply decoded_long_source_indices_types; exact ROWS.
Qed.

Theorem checked_double_source_raw_store p controls source description fe ge locals temps memory trace after final outcome :
  checked_double_source_instruction p controls source=Some description ->
  preserving_globals (globalenv p) ge ->
  locals_avoid [fst (double_affine_source_function (double_source_write description))] locals ->
  exec_stmt fe ge locals temps memory source trace after final outcome ->
  exists block offset value,
    Genv.find_symbol ge (fst (double_affine_source_function (double_source_write description)))=Some block /\
    Mem.store Mfloat64 memory block offset value=Some final /\ trace=E0 /\ after=temps /\ outcome=Out_normal.
Proof.
  intros CHECK GLOBAL LOCAL RUN.
  destruct (@checked_double_source_instruction_sound p controls source description CHECK) as [ASSIGN [WRITE _]].
  destruct (@decoded_double_assignment_shape source (double_source_assignment description) ASSIGN) as [rhs [SHAPE TYPE]].
  destruct (@checked_double_affine_source_access_sound p controls
    (double_assignment_target (double_source_assignment description)) (double_source_write description) WRITE)
    as [DECODE STATIC].
  unfold decode_double_affine_source_access in DECODE.
  destruct (describe_double_source_access (double_assignment_target (double_source_assignment description))) as [raw|] eqn:RAW;
    try discriminate.
  destruct (decode_long_source_indices controls (double_source_coordinates raw)) as [rows|] eqn:ROWS; try discriminate.
  injection DECODE as EXACT; rewrite <- EXACT in STATIC,LOCAL |- *.
  cbn [double_affine_source_metadata double_affine_source_function double_affine_source_dimensions fst] in STATIC,LOCAL.
  change (double_source_access_static_check p raw=true) in STATIC.
  destruct (@double_source_access_static_sound p raw ge locals STATIC GLOBAL LOCAL) as [root [BIND _]].
  assert (ACCESS : decode_double_affine_source_access controls
    (double_assignment_target (double_source_assignment description))=Some (DoubleAffineSourceAccess
      (double_source_array raw,rows) (double_source_dimensions raw))).
  { unfold decode_double_affine_source_access; rewrite RAW,ROWS; reflexivity. }
  rewrite SHAPE in RUN; inversion RUN; subst.
  match goal with ADDRESS : eval_lvalue ge locals ?actual memory _ ?actualblock _ ?actualfield |- _ =>
    destruct (@decoded_double_affine_source_lvalue_origin controls _ _ ge locals actual memory root _ _ _
      ACCESS BIND ADDRESS) as [BLOCK FIELD]; subst actualblock actualfield
  end.
  match goal with STORE : assign_loc _ _ _ _ _ _ _ _ |- _ => rewrite TYPE in STORE; inversion STORE; subst end;
    try discriminate.
  match goal with ACCESS : access_mode _=By_value ?chunk |- _ =>
    change (By_value Mfloat64=By_value chunk) in ACCESS; injection ACCESS as CHUNK; subst chunk
  end.
  exists root,(Ptrofs.unsigned ofs),v; split; [exact (proj2 BIND)|].
  match goal with STORE : Mem.storev _ _ _ _ = _ |- _ => cbn [Mem.storev] in STORE end.
  match goal with STORE : (if ?test then _ else _)=Some _ |- _ => destruct test in STORE; try discriminate end.
  repeat split; auto.
Qed.

Theorem checked_double_source_raw_preserves_header p controls source description fe ge locals temps memory trace after final outcome
  header header_block chunk offset :
  checked_double_source_instruction p controls source=Some description ->
  preserving_globals (globalenv p) ge ->
  locals_avoid [fst (double_affine_source_function (double_source_write description))] locals ->
  Genv.find_symbol ge header=Some header_block ->
  fst (double_affine_source_function (double_source_write description))<>header ->
  exec_stmt fe ge locals temps memory source trace after final outcome ->
  Mem.load chunk final header_block offset=Mem.load chunk memory header_block offset.
Proof.
  intros CHECK GLOBAL LOCAL HEADER DIFFERENT RUN.
  destruct (@checked_double_source_raw_store p controls source description fe ge locals temps memory trace after final outcome
    CHECK GLOBAL LOCAL RUN) as [block [ofs [value [SYMBOL [STORE _]]]]].
  eapply Mem.load_store_other; [exact STORE|].
  left; intro SAME; subst block; apply DIFFERENT.
  eapply Genv.genv_vars_inj; eassumption.
Qed.

Print Assumptions decoded_long_source_index_type.
Print Assumptions decoded_long_source_indices_types.
Print Assumptions double_raw_array_value.
Print Assumptions double_raw_tensor_lvalue_origin.
Print Assumptions decoded_double_affine_source_lvalue_origin.
Print Assumptions checked_double_source_raw_store.
Print Assumptions checked_double_source_raw_preserves_header.
