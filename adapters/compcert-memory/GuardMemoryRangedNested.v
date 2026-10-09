From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From polcert.lib Require Import Misc.
From polcert.polygen Require Import InstrTy Loop.
From Guard Require Import PolCertLoopGuard PolCertClightBody PolCertCountedClight
  PolCertNestedClight ClightCondition ClightCountedLoop ClightTempFrame ClightFramedLoop.
Import ListNotations.
Open Scope Z_scope.
Set Implicit Arguments.

(** A successor of FramedNestedClightFor retaining the signed range already
    proved by affine compilation. This permits exact I32-to-I64 operand casts
    in a double/global-array backend without assuming that repr is injective. *)
Module RangedNestedClightFor (I : INSTR) (M : LOOP_MODEL I).
Module N := PolCertNestedClightFor I M.
Module B := N.B.
Module C := N.C.
Module A := N.A.
Module G := N.G.
Module L := M.

Section BACKEND.
Variable function_entry : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable view : I.State.t -> mem -> Prop.
Variable protected : list ident.
Variable capability : temp_env -> Prop.
Hypothesis capability_frame : forall before after,
  temp_agree protected before after -> capability before -> capability after.

Definition ranged_operand le m code value :=
  B.operand_view ge locals le m code value /\ signed_range value.
Lemma compile_operands_ranged es : forall layout bounds codes env le m,
  B.compile_operands layout bounds es = Some codes ->
  A.env_within bounds env -> A.typed_view layout env le ->
  Forall2 (ranged_operand le m) codes (map (L.eval_expr env) es).
Proof.
  induction es as [|expression rest IH]; intros layout bounds codes env le m COMPILE WITHIN VIEW;
    cbn [B.compile_operands] in COMPILE.
  - inversion COMPILE; constructor.
  - destruct (A.compile_expr layout bounds expression) as [[code bound]|] eqn:CODE; try discriminate.
    destruct (B.compile_operands layout bounds rest) as [tail|] eqn:REST; try discriminate.
    inversion COMPILE; subst; constructor.
    + destruct (A.compile_expr_sound expression CODE WITHIN VIEW) as [TYPE [RANGE [_ EVAL]]].
      split; [split; [exact TYPE|exact (EVAL ge locals m)]|exact RANGE].
    + eapply IH; eauto.
Qed.

Record instruction_backend := RangedInstructionBackend {
  lower_instruction : I.t -> list expr -> option statement;
  instruction_execution : forall i codes values code le m source target writes reads,
    lower_instruction i codes = Some code -> Forall2 (ranged_operand le m) codes values ->
    I.instr_semantics i values writes reads source target -> view source m -> capability le ->
    exists m', view target m' /\
      exec_stmt function_entry ge locals le m code E0 le m' Out_normal
}.
Variable backend : instruction_backend.
Definition compile_nested := N.compile_nested_raw (lower_instruction backend).
Definition compile_nested_list := N.compile_nested_list_raw (lower_instruction backend).

Definition nested_contract (st : L.stmt) := forall layout bounds pool code env le source target m0 live,
  compile_nested layout bounds pool st = Some code -> scratch_free pool (layout ++ live) ->
  A.env_within bounds env -> A.typed_view layout env le ->
  L.loop_semantics st env source target -> view source m0 -> capability le ->
  (forall identifier, In identifier protected -> In identifier live) ->
  exists le1 m1, view target m1 /\ temp_agree (layout ++ live) le le1 /\
    exec_stmt function_entry ge locals le m0 code E0 le1 m1 Out_normal.
Definition nested_list_contract (sts : L.stmt_list) :=
  forall layout bounds pool code env le source target m0 live,
  compile_nested_list layout bounds pool sts = Some code -> scratch_free pool (layout ++ live) ->
  A.env_within bounds env -> A.typed_view layout env le ->
  L.loop_semantics (L.Seq sts) env source target -> view source m0 -> capability le ->
  (forall identifier, In identifier protected -> In identifier live) ->
  exists le1 m1, view target m1 /\ temp_agree (layout ++ live) le le1 /\
    exec_stmt function_entry ge locals le m0 code E0 le1 m1 Out_normal.

Theorem compile_nested_contracts :
  (forall st, nested_contract st) /\ (forall sts, nested_list_contract sts).
Proof.
  apply N.nested_stmt_list_ind.
  - intros lower upper body IH layout bounds pool code env le source target m0 live
      COMPILE FREE WITHIN VIEW SOURCE MEMORY CAPABILITY PROTECTED.
    cbn [compile_nested N.compile_nested_raw N.compile_nested_list_raw] in COMPILE.
    fold compile_nested compile_nested_list in COMPILE.
    destruct pool as [|[iterator bound] rest]; try discriminate.
    destruct (C.header_fresh layout iterator bound) eqn:FRESH; try discriminate.
    destruct (A.compile_expr layout bounds lower) as [[lo li]|] eqn:LOWER; try discriminate.
    destruct (A.compile_expr layout bounds upper) as [[hi ui]|] eqn:UPPER; try discriminate.
    destruct (compile_nested (iterator :: layout)
      (A.Interval (A.lower li) (A.upper ui) :: bounds) rest body) as [generated|] eqn:BODY;
      try discriminate.
    inversion COMPILE; subst code.
    destruct (@scratch_free_head iterator bound rest (layout ++ live) FREE)
      as [DISTINCT [ITER_FRESH [BOUND_FRESH REST_FREE]]].
    assert (ITER_LAYOUT : ~ In iterator layout).
    { intro IN; apply ITER_FRESH; apply in_or_app; auto. }
    assert (BOUND_LAYOUT : ~ In bound layout).
    { intro IN; apply BOUND_FRESH; apply in_or_app; auto. }
    destruct (A.compile_expr_sound lower LOWER WITHIN VIEW) as [_ [RL [LO ELOWER]]].
    destruct (A.compile_expr_sound upper UPPER WITHIN VIEW) as [_ [RU [HI EUPPER]]].
    set (initial := counter_temps iterator
      (PTree.set bound (Vint (Int.repr (L.eval_expr env upper))) le) (L.eval_expr env lower)).
    assert (INITIAL_FRAME : temp_agree (layout ++ live) le initial).
    { unfold initial, counter_temps. eapply temp_agree_trans;
        [apply temp_agree_set; exact BOUND_FRESH | apply temp_agree_set; exact ITER_FRESH]. }
    assert (INITIAL_ITER : initial ! iterator = Some (Vint (Int.repr (L.eval_expr env lower)))).
    { unfold initial, counter_temps; apply PTree.gss. }
    assert (INITIAL_BOUND : initial ! bound = Some (Vint (Int.repr (L.eval_expr env upper)))).
    { unfold initial, counter_temps; rewrite PTree.gso by congruence; apply PTree.gss. }
    assert (NESTED : forall x s0 s1 temps m, signed_range x -> L.eval_expr env lower <= x ->
      x < L.eval_expr env upper -> L.loop_semantics body (x :: env) s0 s1 -> view s0 m ->
      temp_agree (layout ++ live) le temps ->
      temps ! iterator = Some (Vint (Int.repr x)) ->
      temps ! bound = Some (Vint (Int.repr (L.eval_expr env upper))) ->
      exists temps' m', view s1 m' /\
        temp_agree (iterator :: bound :: layout ++ live) temps temps' /\
        exec_stmt function_entry ge locals temps m generated E0 temps' m' Out_normal).
    { intros x s0 s1 temps m RX FLOOR CEILING RUN V FRAME ITER BOUND.
      assert (PARAMS : A.typed_view layout env temps).
      { eapply N.typed_view_frame; [|exact FRAME | exact VIEW].
        intros id IN; apply in_or_app; auto. }
      assert (INPUT : A.typed_view (iterator :: layout) (x :: env) temps).
      { rewrite <- (@counter_temps_same iterator temps x ITER).
        apply A.typed_view_cons; auto. }
      assert (RFREE : scratch_free rest ((iterator :: layout) ++ bound :: live)).
      { eapply scratch_free_weaken; [|exact REST_FREE].
        intros id IN; cbn in IN |- *; rewrite in_app_iff in IN |- *;
          cbn in IN |- *; tauto. }
      assert (CAP_TEMPS : capability temps).
      { eapply capability_frame; [|exact CAPABILITY].
        eapply temp_agree_weaken; [|exact FRAME].
        intros identifier MEMBER; apply in_or_app; right; apply PROTECTED; exact MEMBER. }
      assert (PROTECTED_INNER : forall identifier, In identifier protected -> In identifier (bound :: live)).
      { intros identifier MEMBER; right; apply PROTECTED; exact MEMBER. }
      destruct (IH (iterator :: layout) (A.Interval (A.lower li) (A.upper ui) :: bounds)
        rest generated (x :: env) temps s0 s1 m (bound :: live) BODY RFREE)
        as [temps' [m' [V' [PUBLIC EXEC]]]]; auto.
      - apply A.env_within_cons; [unfold A.contains in *; cbn; lia | exact WITHIN].
      - exists temps', m'; repeat split; auto.
        eapply temp_agree_weaken; [|exact PUBLIC].
        intros id IN; cbn in IN |- *; rewrite in_app_iff in IN |- *;
          cbn in IN |- *; tauto. }
    destruct (@N.loop_framed_clight function_entry ge locals view iterator bound generated (layout ++ live) le env lower upper
      body source target initial m0 DISTINCT ITER_FRESH RL RU INITIAL_ITER INITIAL_BOUND
      INITIAL_FRAME NESTED SOURCE MEMORY) as [le1 [m1 [V [FRAME EXEC]]]].
    exists le1, m1; repeat split; auto.
    + eapply temp_agree_trans; eauto.
    + eapply initialized_counted_loop_run; [exact (EUPPER ge locals m0) | | exact EXEC].
      assert (PARAM_BOUND : A.typed_view layout env
        (PTree.set bound (Vint (Int.repr (L.eval_expr env upper))) le)).
      { apply A.typed_view_set_fresh; assumption. }
      destruct (A.compile_expr_sound lower LOWER WITHIN PARAM_BOUND) as [_ [_ [_ EVAL]]].
      exact (EVAL ge locals m0).
  - intros i operands layout bounds pool code env le source target m0 live
      COMPILE FREE WITHIN VIEW SOURCE MEMORY CAPABILITY PROTECTED.
    cbn [compile_nested N.compile_nested_raw N.compile_nested_list_raw] in COMPILE.
    fold compile_nested compile_nested_list in COMPILE.
    destruct (B.compile_operands layout bounds operands) as [codes|] eqn:OPERANDS; try discriminate.
    inversion SOURCE; subst.
    destruct (@instruction_execution backend i codes
      (map (L.eval_expr env) operands) code le m0 source target wcs rcs COMPILE)
      as [m1 [V EXEC]]; eauto using compile_operands_ranged.
    exists le, m1; auto using temp_agree_refl.
  - intros sts IH layout bounds pool code env le source target m0 live
      COMPILE FREE WITHIN VIEW SOURCE MEMORY CAPABILITY PROTECTED.
    eapply IH; eauto.
  - intros test body IH layout bounds pool code env le source target m0 live
      COMPILE FREE WITHIN VIEW SOURCE MEMORY CAPABILITY PROTECTED.
    cbn [compile_nested N.compile_nested_raw N.compile_nested_list_raw] in COMPILE.
    fold compile_nested compile_nested_list in COMPILE.
    destruct (A.lower_test layout bounds test) as [tree|] eqn:TEST; try discriminate.
    destruct (compile_nested layout bounds pool body) as [generated|] eqn:BODY; try discriminate.
    inversion COMPILE; subst code. inversion SOURCE; subst.
    + match goal with RUN : L.loop_semantics body env source target |- _ =>
        destruct (IH _ _ _ _ _ _ _ _ _ live BODY FREE WITHIN VIEW RUN MEMORY CAPABILITY PROTECTED)
          as [le1 [m1 [V [FRAME EXEC]]]] end.
      exists le1, m1; repeat split; auto.
      eapply decision_fragment_run with (b := true); [|exact EXEC].
      match goal with ACCEPT : L.eval_test env test = true |- _ => rewrite <- ACCEPT end.
      eapply A.lower_test_correct; eauto.
    + exists le, m0; repeat split; auto using temp_agree_refl.
      eapply decision_fragment_run with (b := false); [|constructor].
      match goal with REFUSE : L.eval_test env test = false |- _ => rewrite <- REFUSE end.
      eapply A.lower_test_correct; eauto.
  - intros layout bounds pool code env le source target m0 live
      COMPILE FREE WITHIN VIEW SOURCE MEMORY CAPABILITY PROTECTED.
    inversion COMPILE; subst code. inversion SOURCE; subst target.
    exists le, m0; repeat split; auto using temp_agree_refl; constructor.
  - intros st IH rest IHR layout bounds pool code env le source target m0 live
      COMPILE FREE WITHIN VIEW SOURCE MEMORY CAPABILITY PROTECTED.
    cbn [compile_nested_list N.compile_nested_raw N.compile_nested_list_raw] in COMPILE.
    fold (N.compile_nested_raw (lower_instruction backend))
      (N.compile_nested_list_raw (lower_instruction backend)) in COMPILE.
    fold compile_nested compile_nested_list in COMPILE.
    destruct (compile_nested layout bounds pool st) as [first|] eqn:FIRST; try discriminate.
    destruct (compile_nested_list layout bounds pool rest) as [remaining|] eqn:REST; try discriminate.
    inversion COMPILE; subst code. inversion SOURCE; subst.
    match goal with RUN : L.loop_semantics st env source ?next |- _ =>
      destruct (IH _ _ _ _ _ _ _ _ _ live FIRST FREE WITHIN VIEW RUN MEMORY CAPABILITY PROTECTED)
        as [middle [m1 [V1 [FRAME1 EXEC1]]]] end.
    assert (VIEW1 : A.typed_view layout env middle).
    { eapply N.typed_view_frame; [|exact FRAME1 | exact VIEW].
      intros id IN; apply in_or_app; auto. }
    assert (CAP_MIDDLE : capability middle).
    { eapply capability_frame; [|exact CAPABILITY].
      eapply temp_agree_weaken; [|exact FRAME1].
      intros identifier MEMBER; apply in_or_app; right; apply PROTECTED; exact MEMBER. }
    match goal with RUN : L.loop_semantics (L.Seq rest) env ?next target |- _ =>
      destruct (IHR _ _ _ _ _ _ _ _ _ live REST FREE WITHIN VIEW1 RUN V1 CAP_MIDDLE PROTECTED)
        as [final [m2 [V2 [FRAME2 EXEC2]]]] end.
    exists final, m2; repeat split; auto.
    + eapply temp_agree_trans; eauto.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); eauto.
Qed.

Theorem compile_nested_correct st : nested_contract st.
Proof. apply compile_nested_contracts. Qed.

Definition checked_compile_nested layout bounds live pool st :=
  if N.scratch_check pool (layout ++ protected ++ live)
  then compile_nested layout bounds pool st else None.
Theorem checked_compile_nested_correct layout bounds live pool st code env le source target m0 :
  checked_compile_nested layout bounds live pool st = Some code ->
  A.typed_view layout env le ->
  decision_run (Entry ge locals le m0) (G.range_guard layout bounds) true ->
  L.loop_semantics st env source target -> view source m0 -> capability le ->
  exists le1 m1, view target m1 /\ capability le1 /\
    temp_agree (layout ++ protected ++ live) le le1 /\
    exec_stmt function_entry ge locals le m0 code E0 le1 m1 Out_normal.
Proof.
  unfold checked_compile_nested; intros COMPILE VIEW GUARD SOURCE MEMORY CAPABILITY.
  destruct (N.scratch_check pool (layout ++ protected ++ live)) eqn:FRESH; try discriminate.
  assert (WITHIN : A.env_within bounds env).
  { eapply G.range_guard_sound with (layout := layout) (s := Entry ge locals le m0);
      exact VIEW || exact GUARD. }
  destruct (@compile_nested_correct st layout bounds pool code env le source target m0
    (protected++live) COMPILE (N.scratch_check_sound pool _ FRESH)
    WITHIN VIEW SOURCE MEMORY CAPABILITY
    ltac:(intros identifier MEMBER; apply in_or_app; left; exact MEMBER))
    as [le1 [m1 [TARGET [FRAME RUN]]]].
  exists le1,m1; repeat split; auto.
  eapply capability_frame; [|exact CAPABILITY].
  eapply temp_agree_weaken; [|exact FRAME].
  intros identifier MEMBER; apply in_or_app; right; apply in_or_app; left; exact MEMBER.
Qed.
End BACKEND.
Print Assumptions compile_operands_ranged.
Print Assumptions compile_nested_correct.
Print Assumptions checked_compile_nested_correct.
End RangedNestedClightFor.
