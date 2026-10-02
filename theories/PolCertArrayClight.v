From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Csem Clight ClightBigstep.
From polcert.src Require Import PolyBase CTy CState CInstr.
From polcert.polygen Require Import Loop.
From Guard Require Import PolCertMemoryModel ClightCondition ClightGuard ClightTempFrame.
From GuardPolCert Require Import PolCertNestedClight.
Import ListNotations.
Open Scope Z_scope.
Set Implicit Arguments.

(** A concrete first array backend. It accepts local, ordinary, signed-32
    arrays, one-dimensional constant/operand indices, and integer expression
    trees. Unsupported shapes return None. Bounds are checked in the compiler;
    an actual source access supplies its in-bounds index at execution time. *)
Module PolCertArrayClight (Names : C_INSTR_NAMES).
Module I := CInstr Names.
Module L := Loop I.
Module N := PolCertNestedClightFor I L.
Module B := N.B.

Definition array_type count := Tarray type_int32s count noattr.

Fixpoint array_count (specs : list (ident * Z)) id : option Z :=
  match specs with
  | [] => None
  | (name, count) :: rest => if Pos.eqb name id then Some count else array_count rest id
  end.

Definition array_environment specs (locals : Clight.env) :=
  forall id count, array_count specs id = Some count ->
    exists block, locals ! id = Some (block, array_type count).

Definition array_bound_ok count :=
  (0 <? count) && (count <=? Int.max_signed) && (4 * count <=? Ptrofs.max_unsigned).

Lemma array_bound_ok_sound count : array_bound_ok count = true ->
  0 < count /\ count <= Int.max_signed /\ 4 * count <= Ptrofs.max_unsigned.
Proof.
  unfold array_bound_ok; rewrite !andb_true_iff, Z.ltb_lt, !Z.leb_le; tauto.
Qed.

Definition lower_index (codes : list Clight.expr) (index : I.ma_expr) : option Clight.expr :=
  match index with
  | I.MAval value =>
      if (Int.min_signed <=? value) && (value <=? Int.max_signed)
      then Some (Econst_int (Int.repr value) type_int32s) else None
  | I.MAvarz position =>
      match nth_error codes position with
      | Some code => if type_eq (typeof code) type_int32s then Some code else None
      | None => None end
  | _ => None end.

Definition array_lvalue id count index :=
  Ederef (Ebinop Oadd (Evar id (array_type count)) index
    (Tpointer type_int32s noattr)) type_int32s.

Definition lower_access specs codes (access : I.arr_access) : option Clight.expr :=
  match access with
  | I.Aarr id (I.MAsingleton index) _ =>
      match array_count specs id, lower_index codes index with
      | Some count, Some code =>
          if array_bound_ok count then Some (array_lvalue id count code) else None
      | _, _ => None end
  | _ => None end.

Lemma lower_access_type specs codes access code :
  lower_access specs codes access = Some code -> typeof code = type_int32s.
Proof.
  destruct access as [id ty | id [index|first rest] ty]; cbn [lower_access]; try discriminate.
  destruct (array_count specs id); try discriminate.
  destruct (lower_index codes index); try discriminate.
  destruct (array_bound_ok z); try discriminate.
  intro CODE; inversion CODE; reflexivity.
Qed.

Lemma operand_at ge locals codes values le memory position code value :
  Forall2 (B.operand_view ge locals le memory) codes values ->
  nth_error codes position = Some code -> nth_error values position = Some value ->
  B.operand_view ge locals le memory code value.
Proof.
  intros OPERANDS; revert position code value.
  induction OPERANDS; intros [|position] code value CODE VALUE; cbn in *; try discriminate.
  - inversion CODE; inversion VALUE; subst; assumption.
  - eapply IHOPERANDS; eauto.
Qed.

Lemma lower_index_correct ge locals le memory codes values index code value :
  lower_index codes index = Some code ->
  Forall2 (B.operand_view ge locals le memory) codes values ->
  I.eval_maexpr index values value ->
  typeof code = type_int32s /\
    Clight.eval_expr ge locals le memory code (Vint (Int.repr value)).
Proof.
  intros CODE OPERANDS EVAL. destruct index; cbn [lower_index] in CODE; try discriminate.
  - destruct ((Int.min_signed <=? v) && (v <=? Int.max_signed)); try discriminate.
    inversion CODE; subst code. inversion EVAL; subst; split; [reflexivity | constructor].
  - destruct (nth_error codes n) as [operand|] eqn:LOOKUP; try discriminate.
    destruct (type_eq (typeof operand) type_int32s); try discriminate.
    inversion CODE; subst code. inversion EVAL; subst.
    eapply operand_at; eauto.
Qed.

Lemma singleton_offset count index offset :
  CState.calc_offset (CTy.arr_type_intro CTy.int32s [count]) [index] = Some offset ->
  0 < count /\ 0 <= index < count /\ offset = 4 * index.
Proof.
  change ((if ((count >? 0) && true) && ((index >=? 0) && true)
    then if count <=? index then None else Some (4 * index)
    else None) = Some offset ->
    0 < count /\ 0 <= index < count /\ offset = 4 * index).
  destruct (count >? 0) eqn:COUNT; cbn -[Z.geb Z.leb Z.mul]; try discriminate.
  destruct (index >=? 0) eqn:INDEX; cbn -[Z.leb Z.mul]; try discriminate.
  destruct (count <=? index) eqn:BOUND; try discriminate.
  intro OFFSET. inversion OFFSET; subst.
  apply Z.gtb_lt in COUNT; apply Z.geb_le in INDEX; apply Z.leb_gt in BOUND.
  repeat split; lia.
Qed.

Lemma pointer_index ge block count index memory :
  0 <= index < count -> array_bound_ok count = true ->
  sem_binary_operation ge Oadd (Vptr block Ptrofs.zero) (array_type count)
    (Vint (Int.repr index)) type_int32s memory =
    Some (Vptr block (Ptrofs.repr (4 * index))) /\
  Ptrofs.unsigned (Ptrofs.repr (4 * index)) = 4 * index.
Proof.
  intros INDEX BOUND. destruct (array_bound_ok_sound count BOUND) as [POS [LIMIT OFFSET]].
  assert (SIGNED : Int.min_signed <= index <= Int.max_signed).
  { change (-2147483648 <= index <= 2147483647). change (count <= 2147483647) in LIMIT; lia. }
  split.
  - change (Some (Vptr block (Ptrofs.add Ptrofs.zero
      (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.repr (Int.signed (Int.repr index)))))) =
      Some (Vptr block (Ptrofs.repr (4 * index)))).
    rewrite Int.signed_repr by exact SIGNED.
    rewrite Ptrofs.add_zero_l. unfold Ptrofs.mul.
    rewrite !Ptrofs.unsigned_repr by lia. reflexivity.
  - apply Ptrofs.unsigned_repr; lia.
Qed.

Lemma array_lvalue_correct ge locals le memory id count index code block :
  locals ! id = Some (block, array_type count) -> typeof code = type_int32s ->
  Clight.eval_expr ge locals le memory code (Vint (Int.repr index)) ->
  0 <= index < count -> array_bound_ok count = true ->
  Clight.eval_lvalue ge locals le memory (array_lvalue id count code)
    block (Ptrofs.repr (4 * index)) Full.
Proof.
  intros LOCAL TYPE EVAL INDEX BOUND. unfold array_lvalue.
  apply eval_Ederef. eapply eval_Ebinop; [|exact EVAL|].
  - eapply eval_Elvalue; [apply eval_Evar_local; exact LOCAL |].
    apply deref_loc_reference; reflexivity.
  - cbn [typeof]. rewrite TYPE.
    apply (proj1 (@pointer_index ge block count index memory INDEX BOUND)).
Qed.

Lemma lower_access_correct specs codes values access cell code source_ge ge locals
  le memory block ty arrayty offset :
  array_environment specs locals -> lower_access specs codes access = Some code ->
  Forall2 (B.operand_view ge locals le memory) codes values ->
  I.access_cell access values cell ->
  CState.get_var_loc_type (source_ge, locals, memory) cell.(arr_id) = Some (block, ty) ->
  CTy.of_compcert_arrtype ty = Some arrayty ->
  CState.calc_offset arrayty cell.(arr_index) = Some offset ->
  Clight.eval_lvalue ge locals le memory code block (Ptrofs.repr offset) Full /\
    Ptrofs.unsigned (Ptrofs.repr offset) = offset /\
    offset + size_chunk Mint32 <= Ptrofs.modulus.
Proof.
  intros ENV CODE OPERANDS ACCESS LOOKUP ARRAY OFFSET.
  destruct access as [id bty | id indices bty]; cbn [lower_access] in CODE; try discriminate.
  destruct indices as [index | first rest]; try discriminate.
  destruct (array_count specs id) as [count|] eqn:COUNT; try discriminate.
  destruct (lower_index codes index) as [indexcode|] eqn:INDEXCODE; try discriminate.
  destruct (array_bound_ok count) eqn:BOUND; try discriminate.
  inversion CODE; subst code.
  inversion ACCESS; subst; try discriminate.
  match goal with EQ : I.Aarr _ _ _ = I.Aarr _ _ _ |- _ => inversion EQ; subst end.
  match goal with EVAL : I.eval_maexpr_list (I.MAsingleton _) _ _ |- _ =>
    inversion EVAL; subst end.
  destruct (ENV _ _ COUNT) as [actual_block LOCAL].
  cbn [CState.get_var_loc_type arr_id] in LOOKUP; rewrite LOCAL in LOOKUP.
  inversion LOOKUP; subst block ty.
  cbn [CTy.of_compcert_arrtype CTy.base_of_compcert_arrtype
    CTy.collect_compcert_arrtype_bounds array_type] in ARRAY.
  inversion ARRAY; subst arrayty.
  cbn [arr_index] in OFFSET.
  destruct (@singleton_offset count _ _ OFFSET) as [POS [RANGE OFS]]; subst offset.
  match goal with EVAL : I.eval_maexpr index values ?value |- _ =>
    destruct (@lower_index_correct ge locals le memory codes values index indexcode value
      INDEXCODE OPERANDS EVAL) as [TYPE EVALUATE]
  end.
  split.
  - eapply array_lvalue_correct; eauto.
  - split.
    + exact (proj2 (@pointer_index ge actual_block count v memory RANGE BOUND)).
    + destruct (array_bound_ok_sound count BOUND) as [_ [_ EXTENT]].
      change (4 * v + 4 <= Ptrofs.modulus).
      unfold Ptrofs.max_unsigned in EXTENT; lia.
Qed.

Lemma lower_read_correct specs codes values access cell code source_ge ge locals
  le memory source value :
  array_environment specs locals -> lower_access specs codes access = Some code ->
  Forall2 (B.operand_view ge locals le memory) codes values ->
  I.access_cell access values cell ->
  concrete_memory_view source_ge locals source memory ->
  CState.read_cell cell CTy.int32s value source ->
  typeof code = type_int32s /\ Clight.eval_expr ge locals le memory code value.
Proof.
  intros ENV CODE OPERANDS ACCESS VIEW READ.
  split; [eapply lower_access_type; eauto |].
  pose proof (@concrete_read_normalize source_ge locals source memory cell CTy.int32s value
    VIEW READ) as NORMAL.
  inversion NORMAL; subst.
  match goal with EQ : (source_ge, locals, memory) = (?ge0, ?locals0, ?memory0) |- _ =>
    inversion EQ; subst ge0 locals0 memory0 end.
  match goal with
  | LOOKUP : CState.get_var_loc_type _ _ = Some (?block, ?ty),
    ARRAY : CTy.of_compcert_arrtype ?ty = Some ?aty,
    OFFSET : CState.calc_offset ?aty _ = Some ?ofs |- _ =>
    destruct (@lower_access_correct specs codes values access _ code source_ge ge locals le
      memory block ty aty ofs ENV CODE OPERANDS ACCESS LOOKUP ARRAY OFFSET)
      as [LV [UNSIGNED EXTENT]]
  end.
  eapply eval_Elvalue; [exact LV |].
  rewrite (@lower_access_type specs codes access code CODE).
  eapply deref_loc_value with (chunk := Mint32);
    [reflexivity |].
  cbn [Mem.loadv]; rewrite UNSIGNED.
  match goal with MODE : CTy.basetype_access_mode CTy.int32s = By_value ?chunk |- _ =>
    cbn in MODE; inversion MODE; subst
  end.
  destruct (Coqlib.zle (ofs + size_chunk Mint32) Ptrofs.modulus);
    [assumption | lia].
Qed.

Fixpoint lower_expr specs codes (expression : I.expr) : option Clight.expr :=
  match expression with
  | I.Eval (Vint value) _ => Some (Econst_int value type_int32s)
  | I.Eval _ _ => None
  | I.Evarz position _ => match nth_error codes position with
      Some code => if type_eq (typeof code) type_int32s then Some code else None
    | None => None end
  | I.Eaccess access _ => lower_access specs codes access
  | I.Eunop Oabsfloat _ _ => None
  | I.Eunop op expression _ => match lower_expr specs codes expression with
      Some code => Some (Eunop op code type_int32s) | None => None end
  | I.Ebinop op lhs rhs _ =>
      match lower_expr specs codes lhs, lower_expr specs codes rhs with
      Some a, Some b => Some (Ebinop op a b type_int32s) | _, _ => None end
  end.

Lemma integer_unary_memory op value first second :
  sem_unary_operation op value type_int32s first =
  sem_unary_operation op value type_int32s second.
Proof. destruct op; reflexivity. Qed.

Lemma integer_binary_environment op left right first_ce second_ce first second :
  sem_binary_operation first_ce op left type_int32s right type_int32s first =
  sem_binary_operation second_ce op left type_int32s right type_int32s second.
Proof. destruct op; reflexivity. Qed.

Lemma basetype_type (ty : CTy.basetype) : CTy.basetype_to_compcert_type ty = type_int32s.
Proof. destruct ty; reflexivity. Qed.

Lemma lower_expr_correct specs codes values expression reads source value :
  I.eval_expr expression values reads source value ->
  forall source_ge ge locals le memory code,
  array_environment specs locals -> lower_expr specs codes expression = Some code ->
  Forall2 (B.operand_view ge locals le memory) codes values ->
  concrete_memory_view source_ge locals source memory ->
  typeof code = type_int32s /\ Clight.eval_expr ge locals le memory code value.
Proof.
  intro RUN. induction RUN; intros source_ge target_ge locals le memory code
    ENV CODE OPERANDS VIEW; cbn [lower_expr] in CODE.
  - destruct v; try discriminate. inversion CODE; subst; split; [reflexivity | constructor].
  - destruct (nth_error codes n) as [operand|] eqn:LOOKUP; try discriminate.
    destruct (type_eq (typeof operand) type_int32s); try discriminate.
    inversion CODE; subst. eapply operand_at; eauto.
  - eapply lower_read_correct; eauto. destruct ty; assumption.
  - destruct op; try discriminate;
      destruct (lower_expr specs codes r) as [operand|] eqn:OPERAND; try discriminate;
      inversion CODE; subst code;
      destruct (IHRUN _ _ _ _ _ _ ENV eq_refl OPERANDS VIEW) as [TYPE EVAL].
    all: split; [reflexivity | eapply eval_Eunop; [exact EVAL |]].
    all: rewrite TYPE; rewrite <- (integer_unary_memory _ _ m memory);
      match goal with SEM : sem_unary_operation _ _ _ _ = Some _ |- _ =>
        rewrite basetype_type in SEM; exact SEM end.
  - destruct (lower_expr specs codes r1) as [left|] eqn:LEFT; try discriminate.
    destruct (lower_expr specs codes r2) as [right|] eqn:RIGHT; try discriminate.
    inversion CODE; subst code.
    destruct (IHRUN1 _ _ _ _ _ _ ENV eq_refl OPERANDS VIEW) as [TYPE1 EVAL1].
    destruct (IHRUN2 _ _ _ _ _ _ ENV eq_refl OPERANDS VIEW) as [TYPE2 EVAL2].
    split; [reflexivity |]. eapply eval_Ebinop; [exact EVAL1 | exact EVAL2 |].
    rewrite TYPE1, TYPE2;
      rewrite <- (integer_binary_environment op v1 v2 ge target_ge m memory).
    match goal with SEM : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
      rewrite !basetype_type in SEM; exact SEM end.
Qed.

Lemma integer_unary_result op value memory result :
  op <> Oabsfloat -> sem_unary_operation op value type_int32s memory = Some result ->
  exists word, result = Vint word.
Proof.
  destruct op; intro OP; try contradiction; destruct value;
    cbn [sem_unary_operation sem_notbool bool_val classify_bool typeconv type_int32s
      sem_notint classify_notint sem_neg classify_neg] in *; try discriminate;
    intro RESULT; inversion RESULT; subst; eauto.
  unfold Val.of_bool.
  repeat match goal with |- context [if ?test then _ else _] => destruct test end;
    eexists; reflexivity.
Qed.

Lemma integer_binary_result op left right ce memory result :
  sem_binary_operation ce op left type_int32s right type_int32s memory = Some result ->
  exists word, result = Vint word.
Proof.
  destruct op.
  all: destruct left; destruct right.
  all: cbv beta iota zeta delta [sem_binary_operation sem_add sem_sub classify_add classify_sub
      sem_mul sem_div sem_mod sem_and sem_or sem_xor sem_shl sem_shr sem_shift
      classify_shift sem_cmp classify_cmp sem_binarith classify_binarith binarith_type
      sem_cast classify_cast type_int32s typeconv cast_int_int Val.of_bool] in *.
  all: try discriminate.
  all: repeat match goal with |- context [if ?test then _ else _] => destruct test end.
  all: try discriminate.
  all: intro RESULT.
  all: inversion RESULT.
  all: subst.
  all: eexists; reflexivity.
Qed.

(** An uninitialized read is represented by Vundef in CInstr, whose assignment
    relation does not perform Clight's C cast. Successful integer operations
    certify a Vint result. A direct read/copy needs a separate definedness
    certificate and is conservatively refused by this first backend. *)
Definition result_defined expression :=
  match expression with I.Eaccess _ _ => false | _ => true end.

Lemma lower_result_defined specs codes expression values reads source value code :
  lower_expr specs codes expression = Some code -> result_defined expression = true ->
  I.eval_expr expression values reads source value -> exists word, value = Vint word.
Proof.
  intros CODE DEFINED RUN. destruct expression; cbn [result_defined lower_expr] in *.
  - destruct v; try discriminate. inversion RUN; subst; eauto.
  - inversion RUN; subst; eauto.
  - discriminate.
  - destruct op; try discriminate; inversion RUN; subst;
      match goal with SEM : sem_unary_operation ?operation ?operand _ ?memory0 = Some ?output |- _ =>
        rewrite basetype_type in SEM;
        eapply (@integer_unary_result operation operand memory0 output);
          [discriminate | exact SEM]
      end.
  - inversion RUN; subst.
    match goal with SEM : sem_binary_operation ?ce ?operation ?lhs _ ?rhs _ ?memory0 = Some ?output |- _ =>
      rewrite !basetype_type in SEM;
      eapply (@integer_binary_result operation lhs rhs ce memory0 output); exact SEM end.
Qed.

Definition lower_instruction specs (instruction : I.t) codes : option statement :=
  match instruction with
  | I.Iskip => Some Sskip
  | I.Iassign access expression =>
      if result_defined expression then
        match lower_access specs codes access, lower_expr specs codes expression with
        Some lhs, Some rhs => Some (Sassign lhs rhs) | _, _ => None end
      else None end.

Section EXECUTION.
Variable function_entry : Clight.genv -> Clight.function -> list val -> mem ->
  Clight.env -> temp_env -> mem -> Prop.
Variable source_ge : Csem.genv.
Variable ge : Clight.genv.
Variable locals : Clight.env.
Variable specs : list (ident * Z).
Hypothesis ENV : array_environment specs locals.

Theorem concrete_instruction_execution instruction codes values code le memory source target writes reads :
  lower_instruction specs instruction codes = Some code ->
  Forall2 (B.operand_view ge locals le memory) codes values ->
  I.instr_semantics instruction values writes reads source target ->
  concrete_memory_view source_ge locals source memory ->
  exists memory', concrete_memory_view source_ge locals target memory' /\
    exec_stmt function_entry ge locals le memory code E0 le memory' Out_normal.
Proof.
  intros CODE OPERANDS RUN VIEW. destruct instruction as [|access expression];
    cbn [lower_instruction] in CODE.
  - inversion CODE; subst. inversion RUN; subst.
    exists memory; split; [eapply memory_view_state_eq; eauto | constructor].
  - destruct (result_defined expression) eqn:DEFINED; try discriminate.
    destruct (lower_access specs codes access) as [left|] eqn:LEFT; try discriminate.
    destruct (lower_expr specs codes expression) as [right|] eqn:RIGHT; try discriminate.
    inversion CODE; subst code. inversion RUN; subst.
    match goal with EXPR : I.eval_expr expression values _ source ?value |- _ =>
      destruct (@lower_expr_correct specs codes values expression _ source value EXPR
        source_ge ge locals le memory right ENV RIGHT OPERANDS VIEW) as [RTYPE EVAL];
      destruct (@lower_result_defined specs codes expression values _ source value right
        RIGHT DEFINED EXPR) as [word VALUE]; subst value
    end.
    assert (WRITE : CState.write_cell wcell (I.typeof_access access) (Vint word)
      (source_ge, locals, memory) target).
    { eapply CState.write_cell_stable_under_eq; [exact VIEW | apply CState.eq_refl | eassumption]. }
    destruct (@concrete_write_normalize source_ge locals memory target wcell
      (I.typeof_access access) (Vint word) WRITE)
      as [memory' [block [ty [arrayty [offset [chunk
        [LOOKUP [ARRAY [BASE [OFFSET [MODE [STORE RESULT]]]]]]]]]]]].
    match goal with ACCESS : I.access_cell access values wcell |- _ =>
      destruct (@lower_access_correct specs codes values access wcell left source_ge ge locals
        le memory block ty arrayty offset ENV LEFT OPERANDS ACCESS LOOKUP ARRAY OFFSET)
        as [LV [UNSIGNED EXTENT]]
    end.
    exists memory'; split; [exact RESULT |].
    eapply exec_Sassign with (v2 := Vint word) (v := Vint word); [exact LV | exact EVAL | |].
    + rewrite RTYPE, (@lower_access_type specs codes access left LEFT); reflexivity.
    + rewrite (@lower_access_type specs codes access left LEFT).
      eapply assign_loc_value with (chunk := Mint32); [reflexivity |].
      cbn [Mem.storev]; rewrite UNSIGNED.
      destruct (I.typeof_access access); cbn in MODE; inversion MODE; subst.
      destruct (Coqlib.zle (offset + size_chunk Mint32) Ptrofs.modulus);
        [exact STORE | lia].
Qed.

Definition concrete_backend : B.instruction_backend function_entry ge locals
    (concrete_memory_view source_ge locals) :=
  @B.InstructionBackend function_entry ge locals (concrete_memory_view source_ge locals)
    (lower_instruction specs) concrete_instruction_execution.

End EXECUTION.

Definition compile_array_nested specs := N.checked_compile_nested_raw (lower_instruction specs).

Theorem compile_array_nested_steps temps p source_ge locals specs layout bounds live pool st
  code env le source target memory f k :
  array_environment specs locals ->
  compile_array_nested specs layout bounds live pool st = Some code ->
  N.A.typed_view layout env le ->
  decision_run (Entry (globalenv p) locals le memory) (N.G.range_guard layout bounds) true ->
  L.loop_semantics st env source target -> concrete_memory_view source_ge locals source memory ->
  exists le' memory', concrete_memory_view source_ge locals target memory' /\
    temp_agree (layout ++ live) le le' /\
    star (ClightGuard.adapter_step temps) (globalenv p)
      (State f code k locals le memory) E0 (State f Sskip k locals le' memory').
Proof.
  intros ENV CODE VIEW GUARD RUN MEMORY.
  pose (backend := @concrete_backend (fun ge => ClightGuard.adapter_entry temps ge)
    source_ge (globalenv p) locals specs ENV).
  change (N.checked_compile_nested backend layout bounds live pool st = Some code) in CODE.
  eapply N.checked_compile_nested_steps; eauto.
Qed.

Goal True. idtac "GUARDCERT_MEMORY_BASELINE_BEGIN". exact Logic.I. Qed.
Print Assumptions ClightBigstep.exec_stmt_steps.
Print Assumptions I.bc_condition_implie_permutbility.
Print Assumptions CState.read_cell_stable_under_eq.
Goal True. idtac "GUARDCERT_MEMORY_ADAPTER_BEGIN". exact Logic.I. Qed.
Print Assumptions concrete_instruction_execution.
Print Assumptions compile_array_nested_steps.
Goal True. idtac "GUARDCERT_MEMORY_ASSUMPTIONS_END". exact Logic.I. Qed.

End PolCertArrayClight.
