From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightPureExpr ClightRectangularStore ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryAffineSourceExpressions
  GuardMemoryAffineAccessExpressions GuardMemoryAffineAccess GuardMemoryOffsetAccessRanges.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Scalar computations retain the source access expressions.  They can read
    any finite number of affine cells; the instruction backend later lowers
    the same checked accesses using candidate iterators. *)
Fixpoint memory_compile_source_value row column accesses value : option expr :=
  match value with
  | ConstantValue z => Some (rect_constant z)
  | ParameterValue n => match n with
      | O => Some (Etempvar row type_int32s)
      | S O => Some (Etempvar column type_int32s)
      | _ => None end
  | LoadedValue n => option_map memory_access_code (nth_error accesses n)
  | AddValue first second | SubValue first second | MulValue first second =>
      match memory_compile_source_value row column accesses first,
        memory_compile_source_value row column accesses second with
      | Some lhs,Some rhs => Some (Ebinop
          (match value with AddValue _ _ => Oadd | SubValue _ _ => Osub | _ => Omul end)
          lhs rhs type_int32s)
      | _,_ => None end
  end.
Fixpoint memory_source_value_read_positions value : list nat :=
  match value with
  | LoadedValue n => [n]
  | AddValue first second | SubValue first second | MulValue first second =>
      memory_source_value_read_positions first ++ memory_source_value_read_positions second
  | _ => [] end.
Definition memory_source_value_reads_check (accesses : list memory_affine_access) value :=
  forallb (fun index => existsb (Nat.eqb index) (memory_source_value_read_positions value))
    (seq 0 (length accesses)).
Lemma memory_source_value_reads_check_sound accesses value :
  memory_source_value_reads_check accesses value = true ->
  forall index access, nth_error accesses index = Some access ->
    In index (memory_source_value_read_positions value).
Proof.
  unfold memory_source_value_reads_check; intros CHECK index access LOOKUP.
  assert (MEMBER : In index (seq 0 (length accesses))).
  { apply in_seq; split; [lia|]. apply nth_error_Some; rewrite LOOKUP; discriminate. }
  apply forallb_forall with (x := index) in CHECK; [|exact MEMBER].
  apply existsb_exists in CHECK as [position [FOUND EQUAL]].
  apply Nat.eqb_eq in EQUAL; subst; exact FOUND.
Qed.
Lemma memory_compile_source_value_type row column accesses value code :
  memory_compile_source_value row column accesses value = Some code -> typeof code = type_int32s.
Proof.
  destruct value; cbn [memory_compile_source_value]; intro COMPILE.
  - inversion COMPILE; apply rect_constant_type.
  - destruct n as [|[|n]]; inversion COMPILE; reflexivity.
  - destruct (nth_error accesses n); inversion COMPILE; reflexivity.
  - destruct (memory_compile_source_value row column accesses value1),
      (memory_compile_source_value row column accesses value2); inversion COMPILE; reflexivity.
  - destruct (memory_compile_source_value row column accesses value1),
      (memory_compile_source_value row column accesses value2); inversion COMPILE; reflexivity.
  - destruct (memory_compile_source_value row column accesses value1),
      (memory_compile_source_value row column accesses value2); inversion COMPILE; reflexivity.
Qed.
Definition memory_source_access_loaded ge locals i j memory access value :=
  exists block, rect_array_binding (memory_access_shape access) ge locals (memory_access_array access) block /\
    Mem.load Mint32 memory block (4*memory_index_value (memory_access_index access) i j) = Some value.
Lemma memory_source_access_loaded_unique ge locals i j memory access first second :
  memory_source_access_loaded ge locals i j memory access first ->
  memory_source_access_loaded ge locals i j memory access second -> first = second.
Proof.
  intros [b1 [B1 L1]] [b2 [B2 L2]].
  assert (b1=b2) by (eapply rect_array_binding_unique; eassumption); subst; congruence.
Qed.
Lemma memory_source_values_lookup ge locals i j memory accesses loaded index access :
  Forall2 (memory_source_access_loaded ge locals i j memory) accesses loaded ->
  nth_error accesses index = Some access ->
  exists value, nth_error loaded index = Some value /\ memory_source_access_loaded ge locals i j memory access value.
Proof.
  intro RELATED; revert index access; induction RELATED; intros [|index] access LOOKUP;
    cbn in LOOKUP; try discriminate.
  - inversion LOOKUP; subst; eexists; split; [reflexivity|eassumption].
  - destruct (IHRELATED _ _ LOOKUP) as [value [VALUE LOAD]]; exists value; split; [exact VALUE|exact LOAD].
Qed.
Lemma memory_source_value_read_inverse base row column accesses value code ge locals temps memory i j result :
  row <> column -> Forall (memory_offset_access_valid base row column) accesses ->
  0 <= i < rectangle_outer_limit base -> 0 <= j < rectangle_stride base ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  memory_compile_source_value row column accesses value = Some code ->
  eval_expr ge locals temps memory code (Vint result) ->
  forall index, In index (memory_source_value_read_positions value) ->
  exists access word, nth_error accesses index = Some access /\
    memory_source_access_loaded ge locals i j memory access (Vint word).
Proof.
  intros DISTINCT CERT I J ROW COLUMN; revert code result.
  induction value; intros code result COMPILE RUN index MEMBER; cbn [memory_source_value_read_positions] in MEMBER;
    try contradiction.
  { cbn in MEMBER; destruct MEMBER as [<-|[]].
    cbn [memory_compile_source_value] in COMPILE.
    destruct (nth_error accesses n) as [access|] eqn:LOOKUP; [|discriminate].
    inversion COMPILE; subst code.
    pose proof (nth_error_In _ _ LOOKUP) as AMEMBER.
    apply Forall_forall with (x := access) in CERT; [|exact AMEMBER].
    destruct CERT as [VALID [ENCODE BOUND]].
    destruct (@memory_affine_access_load_inverse (memory_access_shape access) (memory_access_array access)
      (memory_access_expression access) row column (memory_access_index access) ge locals temps memory i j (Vint result)
      VALID DISTINCT ENCODE ROW COLUMN (BOUND i j I J) RUN) as [block [ARRAY LOAD]].
    exists access,result; split; [reflexivity|exists block; auto]. }
  all: cbn [memory_compile_source_value] in COMPILE;
    destruct (memory_compile_source_value row column accesses value1) as [first|] eqn:FIRST; [|discriminate];
    destruct (memory_compile_source_value row column accesses value2) as [second|] eqn:SECOND; [|discriminate];
    inversion COMPILE; subst code;
    apply scalar_binary_inv in RUN as [a [b [A [B OP]]]];
    rewrite (@memory_compile_source_value_type row column accesses value1 first FIRST),
      (@memory_compile_source_value_type row column accesses value2 second SECOND) in OP;
    match type of OP with sem_binary_operation _ ?operation _ _ _ _ _ = _ =>
      destruct (@memory_source_binary_words ge operation a b memory result ltac:(auto) OP) as [x [y [-> ->]]] end;
    apply in_app_or in MEMBER as [MEMBER|MEMBER];
    [eapply IHvalue1|eapply IHvalue2]; eauto.
Qed.
Theorem memory_source_value_loads_exist base row column accesses value code ge locals temps memory i j result :
  row <> column -> Forall (memory_offset_access_valid base row column) accesses ->
  0 <= i < rectangle_outer_limit base -> 0 <= j < rectangle_stride base ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  memory_source_value_reads_check accesses value = true ->
  memory_compile_source_value row column accesses value = Some code ->
  eval_expr ge locals temps memory code (Vint result) ->
  exists loaded, Forall2 (memory_source_access_loaded ge locals i j memory) accesses loaded.
Proof.
  intros DISTINCT CERT I J ROW COLUMN CHECK COMPILE RUN.
  assert (LOADS : forall access, In access accesses -> exists word,
    memory_source_access_loaded ge locals i j memory access (Vint word)).
  { intros access MEMBER; apply In_nth_error in MEMBER as [index LOOKUP].
    pose proof (@memory_source_value_reads_check_sound accesses value CHECK index access LOOKUP) as REFERENCED.
    destruct (@memory_source_value_read_inverse base row column accesses value code ge locals temps memory i j result
      DISTINCT CERT I J ROW COLUMN COMPILE RUN index REFERENCED) as [same [word [SAME LOAD]]].
    assert (same=access) by congruence; subst; eauto. }
  clear CERT CHECK COMPILE RUN; induction accesses as [|access accesses IH].
  - exists []; constructor.
  - destruct (LOADS access ltac:(cbn; auto)) as [word LOAD].
    destruct (IH ltac:(intros a M; apply LOADS; cbn; auto)) as [loaded REST].
    exists (Vint word::loaded); constructor; assumption.
Qed.
Print Assumptions memory_source_value_loads_exist.

Theorem memory_source_value_evaluation_inverse base row column accesses value code loaded ge locals temps memory i j result :
  row <> column -> Forall (memory_offset_access_valid base row column) accesses ->
  0 <= i < rectangle_outer_limit base -> 0 <= j < rectangle_stride base ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  Forall2 (memory_source_access_loaded ge locals i j memory) accesses loaded ->
  memory_compile_source_value row column accesses value = Some code ->
  eval_expr ge locals temps memory code (Vint result) ->
  evaluate_value [i;j] loaded value = Some (Vint result).
Proof.
  intros DISTINCT CERT I J ROW COLUMN LOADS; revert code result.
  induction value; intros code result COMPILE RUN.
  { cbn in COMPILE; inversion COMPILE; subst code.
    pose proof (@pure_scalar_determinate (rect_constant z)
      (memory_source_affine_pure (MemorySourceConstant z)) ge locals temps memory _ _
      RUN (@rect_constant_evaluation ge locals temps memory z)) as SAME.
    cbn [evaluate_value]; rewrite SAME; reflexivity. }
  { cbn in COMPILE; destruct n as [|[|n]]; try discriminate;
      inversion COMPILE; subst code; apply scalar_temp_inv in RUN;
      cbn [evaluate_value nth_error]; [rewrite ROW in RUN|rewrite COLUMN in RUN]; congruence. }
  { cbn [memory_compile_source_value] in COMPILE.
    destruct (nth_error accesses n) as [access|] eqn:LOOKUP; [|discriminate].
    inversion COMPILE; subst code.
    destruct (@memory_source_values_lookup ge locals i j memory accesses loaded n access LOADS LOOKUP)
      as [actual [VALUE LOAD]].
    pose proof (nth_error_In _ _ LOOKUP) as MEMBER.
    apply Forall_forall with (x := access) in CERT; [|exact MEMBER].
    destruct CERT as [VALID [ENCODE BOUND]].
    destruct (@memory_affine_access_load_inverse (memory_access_shape access) (memory_access_array access)
      (memory_access_expression access) row column (memory_access_index access) ge locals temps memory i j (Vint result)
      VALID DISTINCT ENCODE ROW COLUMN (BOUND i j I J) RUN) as [block [ARRAY ACTUAL]].
    assert (SAME : actual = Vint result).
    { eapply memory_source_access_loaded_unique; [exact LOAD|exists block; auto]. }
    cbn [evaluate_value]; rewrite <- SAME; exact VALUE. }
  all: cbn [memory_compile_source_value] in COMPILE;
    destruct (memory_compile_source_value row column accesses value1) as [first|] eqn:FIRST; [|discriminate];
    destruct (memory_compile_source_value row column accesses value2) as [second|] eqn:SECOND; [|discriminate];
    inversion COMPILE; subst code;
    apply scalar_binary_inv in RUN as [a [b [A [B OP]]]];
    rewrite (@memory_compile_source_value_type row column accesses value1 first FIRST),
      (@memory_compile_source_value_type row column accesses value2 second SECOND) in OP;
    match type of OP with sem_binary_operation _ ?operation _ _ _ _ _ = _ =>
      destruct (@memory_source_binary_words ge operation a b memory result ltac:(auto) OP) as [x [y [-> ->]]] end;
    cbn [evaluate_value]; rewrite (IHvalue1 first x eq_refl A),(IHvalue2 second y eq_refl B); exact OP.
Qed.
Print Assumptions memory_source_value_evaluation_inverse.
