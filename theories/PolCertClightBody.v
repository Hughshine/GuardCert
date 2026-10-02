From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From polcert.polygen Require Import InstrTy Loop.
From Guard Require Import PolCertLoopGuard ClightCondition PolCertCountedClight.
Import ListNotations.
Set Implicit Arguments.

(** Instruction implementations supply their own language/state semantics.
    The adapter knows how to lower affine operands and structured control,
    without assuming a concrete interpretation of I.State or memory cells. *)
Module PolCertClightBodyFor (I : INSTR) (M : LOOP_MODEL I).
Module C := PolCertCountedClightFor I M.
Module A := C.A.
Module G := C.G.
Module L := M.

Section BACKEND.
Variable function_entry : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable view : I.State.t -> mem -> Prop.

Definition operand_view le m (code : expr) (value : Z) :=
  typeof code = type_int32s /\ eval_expr ge locals le m code (Vint (Int.repr value)).

Record instruction_backend := InstructionBackend {
  lower_instruction : I.t -> list expr -> option statement;
  instruction_execution : forall i codes values code le m source target writes reads,
    lower_instruction i codes = Some code -> Forall2 (operand_view le m) codes values ->
    I.instr_semantics i values writes reads source target -> view source m ->
    exists m', view target m' /\
      exec_stmt function_entry ge locals le m code E0 le m' Out_normal
}.

Variable backend : instruction_backend.

Fixpoint compile_operands layout bounds (es : list L.expr) : option (list expr) :=
  match es with
  | [] => Some []
  | e :: rest =>
      match A.compile_expr layout bounds e, compile_operands layout bounds rest with
      | Some (code, _), Some codes => Some (code :: codes)
      | _, _ => None end
  end.

Lemma compile_operands_correct es : forall layout bounds codes env le m,
  compile_operands layout bounds es = Some codes ->
  A.env_within bounds env -> A.typed_view layout env le ->
  Forall2 (operand_view le m) codes (map (L.eval_expr env) es).
Proof.
  induction es as [|e es IH]; intros layout bounds codes env le m COMPILE WITHIN VIEW;
    cbn [compile_operands] in COMPILE.
  - inversion COMPILE; constructor.
  - destruct (A.compile_expr layout bounds e) as [[code b]|] eqn:CODE; try discriminate.
    destruct (compile_operands layout bounds es) as [rest|] eqn:REST; try discriminate.
    inversion COMPILE; subst. constructor.
    + destruct (A.compile_expr_sound e CODE WITHIN VIEW) as [TYPE [_ [_ EVAL]]].
      split; auto.
    + eapply IH; eauto.
Qed.

Fixpoint compile_body layout bounds (st : L.stmt) : option statement :=
  match st with
  | L.Instr i es =>
      match compile_operands layout bounds es with
      | Some codes => lower_instruction backend i codes | None => None end
  | L.Seq sts => compile_body_list layout bounds sts
  | L.Guard t body =>
      match A.lower_test layout bounds t, compile_body layout bounds body with
      | Some tree, Some code => Some (tree_statement tree code Sskip)
      | _, _ => None end
  | L.Loop _ _ _ => None
  end
with compile_body_list layout bounds (sts : L.stmt_list) : option statement :=
  match sts with
  | L.SNil => Some Sskip
  | L.SCons body rest =>
      match compile_body layout bounds body, compile_body_list layout bounds rest with
      | Some code, Some codes => Some (Ssequence code codes) | _, _ => None end
  end.

Theorem compile_body_correct st env source target :
  L.loop_semantics st env source target -> forall layout bounds code le m,
  compile_body layout bounds st = Some code ->
  A.env_within bounds env -> A.typed_view layout env le -> view source m ->
  exists m', view target m' /\
    exec_stmt function_entry ge locals le m code E0 le m' Out_normal.
Proof.
  intro RUN. induction RUN; intros layout bounds code le m COMPILE WITHIN VIEW MEMORY;
    cbn [compile_body compile_body_list] in COMPILE.
  - destruct (compile_operands layout bounds es) as [codes|] eqn:CODES; try discriminate.
    eapply instruction_execution; eauto. eapply compile_operands_correct; eauto.
  - inversion COMPILE; subst code. exists m; split; auto; constructor.
  - destruct (compile_body layout bounds st) as [first|] eqn:FIRST; try discriminate.
    destruct (compile_body_list layout bounds sts) as [rest|] eqn:REST; try discriminate.
    inversion COMPILE; subst code.
    destruct (IHRUN1 _ _ _ _ _ FIRST WITHIN VIEW MEMORY) as [middle [V1 EXEC1]].
    destruct (IHRUN2 _ _ _ _ _ REST WITHIN VIEW V1) as [final [V2 EXEC2]].
    exists final; split; auto.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); eauto.
  - destruct (A.lower_test layout bounds t) as [tree|] eqn:TREE; try discriminate.
    destruct (compile_body layout bounds st) as [body|] eqn:BODY; try discriminate.
    inversion COMPILE; subst code.
    destruct (IHRUN _ _ _ _ _ BODY WITHIN VIEW MEMORY) as [final [V EXEC]].
    exists final; split; auto.
    eapply decision_fragment_run with (b := true); [|exact EXEC].
    match goal with CHECK : L.eval_test env t = true |- _ => rewrite <- CHECK end.
    eapply A.lower_test_correct; eauto.
  - destruct (A.lower_test layout bounds t) as [tree|] eqn:TREE; try discriminate.
    destruct (compile_body layout bounds st) as [body|] eqn:BODY; try discriminate.
    inversion COMPILE; subst code. exists m; split; auto.
    eapply decision_fragment_run with (b := false); [|constructor].
    match goal with CHECK : L.eval_test env t = false |- _ => rewrite <- CHECK end.
    eapply A.lower_test_correct; eauto.
  - discriminate.
Qed.

Definition compile_single_loop layout bounds iterator bound lower upper body : option statement :=
  if C.header_fresh layout iterator bound then
  match A.compile_expr layout bounds lower, A.compile_expr layout bounds upper with
  | Some (lo, li), Some (hi, ui) =>
      match compile_body (iterator :: layout)
        (A.Interval (A.lower li) (A.upper ui) :: bounds) body with
      | Some code => Some (ClightCountedLoop.initialized_counted_loop iterator bound lo hi code)
      | None => None end
  | _, _ => None end else None.

Theorem compile_single_loop_correct layout bounds iterator bound lower upper body
  generated env le source target m0 :
  compile_single_loop layout bounds iterator bound lower upper body = Some generated ->
  A.typed_view layout env le ->
  decision_run (Entry ge locals le m0) (G.range_guard layout bounds) true ->
  L.loop_semantics (L.Loop lower upper body) env source target -> view source m0 ->
  exists m1, view target m1 /\
    exec_stmt function_entry ge locals le m0 generated E0
      (ClightCountedLoop.counter_temps iterator
        (PTree.set bound (Vint (Int.repr (L.eval_expr env upper))) le)
        (Z.max (L.eval_expr env lower) (L.eval_expr env upper))) m1 Out_normal.
Proof.
  intros COMPILE VIEW GUARD SOURCE MEMORY.
  unfold compile_single_loop in COMPILE.
  destruct (C.header_fresh layout iterator bound) eqn:FRESH; try discriminate.
  destruct (A.compile_expr layout bounds lower) as [[lo li]|] eqn:LOWER; try discriminate.
  destruct (A.compile_expr layout bounds upper) as [[hi ui]|] eqn:UPPER; try discriminate.
  destruct (compile_body (iterator :: layout)
    (A.Interval (A.lower li) (A.upper ui) :: bounds) body) as [code|] eqn:BODY;
    try discriminate.
  inversion COMPILE; subst generated.
  destruct (C.header_fresh_sound FRESH) as [DISTINCT [ITER_FRESH BOUND_FRESH]].
  assert (WITHIN : A.env_within bounds env).
  { eapply G.range_guard_sound with (layout := layout) (s := Entry ge locals le m0);
      exact VIEW || exact GUARD. }
  destruct (A.compile_expr_sound lower LOWER WITHIN VIEW) as [_ [_ [LO _]]].
  destruct (A.compile_expr_sound upper UPPER WITHIN VIEW) as [_ [_ [HI _]]].
  eapply C.compile_loop_header_correct; eauto.
  - unfold C.compile_loop_header; rewrite FRESH, LOWER, UPPER; reflexivity.
  - intros x s0 s1 m RANGE FLOOR CEILING RUN V.
    eapply compile_body_correct; [exact RUN | exact BODY | | | exact V].
    + apply A.env_within_cons; [unfold A.contains; cbn; unfold A.contains in LO, HI; lia | exact WITHIN].
    + unfold ClightCountedLoop.counter_temps. apply A.typed_view_cons; auto.
      apply A.typed_view_set_fresh; assumption.
Qed.

End BACKEND.
End PolCertClightBodyFor.

Module PolCertClightBody (I : INSTR).
Module ConcreteLoop := Loop I.
Include PolCertClightBodyFor I ConcreteLoop.

Print Assumptions compile_body_correct.
Print Assumptions compile_single_loop_correct.

End PolCertClightBody.
