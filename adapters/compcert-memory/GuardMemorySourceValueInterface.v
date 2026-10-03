From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightPureExpr ClightRectangularStore ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryArrayBackend GuardMemoryFlatArrayBackend
  GuardMemoryAffineSourceExpressions GuardMemoryNarySourceValues.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_source_reads_check (read_codes : list expr) value :=
  forallb (fun index => existsb (Nat.eqb index) (memory_nary_source_value_read_positions value))
    (seq 0 (length read_codes)).
Lemma memory_source_reads_check_sound read_codes value : memory_source_reads_check read_codes value = true ->
  forall index code, nth_error read_codes index = Some code -> In index (memory_nary_source_value_read_positions value).
Proof.
  unfold memory_source_reads_check; intros CHECK index code LOOKUP.
  assert (MEMBER : In index (seq 0 (length read_codes))).
  { apply in_seq; split; [lia|]. apply nth_error_Some; rewrite LOOKUP; discriminate. }
  apply forallb_forall with (x := index) in CHECK; [|exact MEMBER].
  apply existsb_exists in CHECK as [position [FOUND EQUAL]].
  apply Nat.eqb_eq in EQUAL; subst; exact FOUND.
Qed.
Lemma memory_source_flat_type codes reads value code :
  Forall (fun code => typeof code = type_int32s) codes ->
  Forall (fun code => typeof code = type_int32s) reads ->
  compile_flat_value codes reads value = Some code -> typeof code = type_int32s.
Proof.
  intros CODES READS; destruct value; cbn [compile_flat_value]; intro COMPILE.
  - inversion COMPILE; apply rect_constant_type.
  - apply Forall_forall with (x := code) in CODES; [exact CODES|apply nth_error_In in COMPILE; exact COMPILE].
  - apply Forall_forall with (x := code) in READS; [exact READS|apply nth_error_In in COMPILE; exact COMPILE].
  - destruct (compile_flat_value codes reads value1),(compile_flat_value codes reads value2); inversion COMPILE; reflexivity.
  - destruct (compile_flat_value codes reads value1),(compile_flat_value codes reads value2); inversion COMPILE; reflexivity.
  - destruct (compile_flat_value codes reads value1),(compile_flat_value codes reads value2); inversion COMPILE; reflexivity.
Qed.
Lemma memory_related_values_exist {A B} (relation : A -> B -> Prop) xs :
  (forall x, In x xs -> exists y, relation x y) -> exists ys, Forall2 relation xs ys.
Proof.
  induction xs as [|x xs IH]; intro VALUES.
  - exists []; constructor.
  - destruct (VALUES x ltac:(cbn; auto)) as [y HEAD].
    destruct (IH ltac:(intros value MEMBER; apply VALUES; cbn; auto)) as [ys TAIL].
    exists (y::ys); constructor; assumption.
Qed.

Section READ_INTERFACE.
Variable ge : genv.
Variable locals : env.
Variable temps : temp_env.
Variable memory : mem.
Variable codes reads : list expr.
Variable relation : expr -> val -> Prop.
Hypothesis CODE_TYPES : Forall (fun code => typeof code = type_int32s) codes.
Hypothesis READ_TYPES : Forall (fun code => typeof code = type_int32s) reads.
Hypothesis READ_INVERSE : forall code word, In code reads ->
  eval_expr ge locals temps memory code (Vint word) -> relation code (Vint word).
Hypothesis READ_UNIQUE : forall code first second, relation code first -> relation code second -> first = second.

Lemma memory_source_value_read_inverse value : forall code result,
  compile_flat_value codes reads value = Some code -> eval_expr ge locals temps memory code (Vint result) ->
  forall index, In index (memory_nary_source_value_read_positions value) ->
  exists read word, nth_error reads index = Some read /\ relation read (Vint word).
Proof.
  induction value; intros code result COMPILE RUN index MEMBER;
    cbn [memory_nary_source_value_read_positions] in MEMBER; try contradiction.
  { cbn in MEMBER; destruct MEMBER as [<-|[]].
    cbn [compile_flat_value] in COMPILE; exists code,result; split; [exact COMPILE|].
    apply READ_INVERSE; [apply nth_error_In in COMPILE; exact COMPILE|exact RUN]. }
  all: cbn [compile_flat_value] in COMPILE;
    destruct (compile_flat_value codes reads value1) as [first|] eqn:FIRST; [|discriminate];
    destruct (compile_flat_value codes reads value2) as [second|] eqn:SECOND; [|discriminate];
    inversion COMPILE; subst code;
    apply scalar_binary_inv in RUN as [a [b [A [B OP]]]];
    rewrite (@memory_source_flat_type codes reads value1 first CODE_TYPES READ_TYPES FIRST),
      (@memory_source_flat_type codes reads value2 second CODE_TYPES READ_TYPES SECOND) in OP;
    match type of OP with sem_binary_operation _ ?operation _ _ _ _ _ = _ =>
      destruct (@memory_source_binary_words ge operation a b memory result ltac:(auto) OP) as [x [y [-> ->]]] end;
    apply in_app_or in MEMBER as [MEMBER|MEMBER];
    [eapply IHvalue1|eapply IHvalue2]; eauto.
Qed.
Lemma memory_source_value_reads_exist value code result : memory_source_reads_check reads value = true ->
  compile_flat_value codes reads value = Some code -> eval_expr ge locals temps memory code (Vint result) ->
  exists loaded, Forall2 relation reads loaded.
Proof.
  intros CHECK COMPILE RUN.
  assert (LOADS : forall read, In read reads -> exists word, relation read (Vint word)).
  { intros read MEMBER; apply In_nth_error in MEMBER as [index LOOKUP].
    pose proof (@memory_source_reads_check_sound reads value CHECK index read LOOKUP) as REFERENCED.
    destruct (@memory_source_value_read_inverse value code result COMPILE RUN index REFERENCED)
      as [same [word [SAME LOAD]]]; assert (same=read) by congruence; subst; eauto. }
  apply memory_related_values_exist; intros read MEMBER.
  destruct (LOADS read MEMBER) as [word LOAD]; exists (Vint word); exact LOAD.
Qed.

Lemma memory_source_value_evaluation_inverse parameters loaded value :
  Forall pure_scalar codes -> Forall2 (MemoryBody.operand_view ge locals temps memory) codes parameters ->
  Forall2 relation reads loaded -> forall code result,
  compile_flat_value codes reads value = Some code -> eval_expr ge locals temps memory code (Vint result) ->
  evaluate_value parameters loaded value = Some (Vint result).
Proof.
  intros PURE OPERANDS LOADS; induction value; intros code result COMPILE RUN.
  { cbn in COMPILE; inversion COMPILE; subst code.
    pose proof (@pure_scalar_determinate (rect_constant z)
      (memory_source_affine_pure (MemorySourceConstant z)) ge locals temps memory _ _
      RUN (@rect_constant_evaluation ge locals temps memory z)) as SAME.
    cbn [evaluate_value]; rewrite SAME; reflexivity. }
  { cbn [compile_flat_value] in COMPILE.
    assert (INDEX : (n < length codes)%nat) by (apply nth_error_Some; rewrite COMPILE; discriminate).
    assert (LENGTH : length codes = length parameters) by (apply Forall2_length in OPERANDS; exact OPERANDS).
    destruct (nth_error parameters n) as [parameter|] eqn:PARAMETER.
    2: { apply nth_error_None in PARAMETER; lia. }
    destruct (@flat_forall2_nth _ _ _ _ _ OPERANDS n code parameter COMPILE PARAMETER) as [TYPE EVAL].
    pose proof (nth_error_In _ _ COMPILE) as MEMBER; apply Forall_forall with (x := code) in PURE; [|exact MEMBER].
    pose proof (@pure_scalar_determinate code PURE ge locals temps memory _ _ RUN EVAL) as SAME.
    cbn [evaluate_value]; rewrite PARAMETER; exact (f_equal (@Some val) (eq_sym SAME)). }
  { cbn [compile_flat_value] in COMPILE.
    assert (INDEX : (n < length reads)%nat) by (apply nth_error_Some; rewrite COMPILE; discriminate).
    assert (LENGTH : length reads = length loaded) by (apply Forall2_length in LOADS; exact LOADS).
    destruct (nth_error loaded n) as [actual|] eqn:VALUE.
    2: { apply nth_error_None in VALUE; lia. }
    pose proof (@flat_forall2_nth _ _ _ _ _ LOADS n code actual COMPILE VALUE) as LOAD.
    assert (ACTUAL : relation code (Vint result)) by (apply READ_INVERSE; [apply nth_error_In in COMPILE; exact COMPILE|exact RUN]).
    assert (SAME : actual = Vint result) by (eapply READ_UNIQUE; eassumption).
    cbn [evaluate_value]; rewrite <- SAME; exact VALUE. }
  all: cbn [compile_flat_value] in COMPILE;
    destruct (compile_flat_value codes reads value1) as [first|] eqn:FIRST; [|discriminate];
    destruct (compile_flat_value codes reads value2) as [second|] eqn:SECOND; [|discriminate];
    inversion COMPILE; subst code;
    apply scalar_binary_inv in RUN as [a [b [A [B OP]]]];
    rewrite (@memory_source_flat_type codes reads value1 first CODE_TYPES READ_TYPES FIRST),
      (@memory_source_flat_type codes reads value2 second CODE_TYPES READ_TYPES SECOND) in OP;
    match type of OP with sem_binary_operation _ ?operation _ _ _ _ _ = _ =>
      destruct (@memory_source_binary_words ge operation a b memory result ltac:(auto) OP) as [x [y [-> ->]]] end;
    cbn [evaluate_value]; rewrite (IHvalue1 first x eq_refl A),(IHvalue2 second y eq_refl B); exact OP.
Qed.
Theorem memory_source_value_inverse parameters value code result :
  Forall pure_scalar codes -> Forall2 (MemoryBody.operand_view ge locals temps memory) codes parameters ->
  memory_source_reads_check reads value = true -> compile_flat_value codes reads value = Some code ->
  eval_expr ge locals temps memory code (Vint result) ->
  exists loaded, Forall2 relation reads loaded /\ evaluate_value parameters loaded value = Some (Vint result).
Proof.
  intros PURE OPERANDS CHECK COMPILE RUN.
  destruct (@memory_source_value_reads_exist value code result CHECK COMPILE RUN) as [loaded LOADS].
  exists loaded; split; [exact LOADS|eapply memory_source_value_evaluation_inverse; eassumption].
Qed.
End READ_INTERFACE.
Print Assumptions memory_source_value_inverse.
