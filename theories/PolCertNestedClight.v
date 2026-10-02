From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From polcert.lib Require Import Misc.
From polcert.polygen Require Import InstrTy Loop.
From Guard Require Import PolCertLoopGuard PolCertClightBody PolCertCountedClight
  ClightCondition ClightCountedLoop ClightTempFrame ClightFramedLoop.
Import ListNotations.
Open Scope Z_scope.
Set Implicit Arguments.

Fixpoint scratch_names (pool : list (ident * ident)) : list ident :=
  match pool with [] => [] | (iterator, bound) :: rest => iterator :: bound :: scratch_names rest end.

Definition scratch_free pool live :=
  NoDup (scratch_names pool) /\ forall id, In id (scratch_names pool) -> ~ In id live.

Lemma scratch_free_weaken pool small big :
  (forall id, In id small -> In id big) -> scratch_free pool big -> scratch_free pool small.
Proof. intros SUB [NODUP FREE]; split; auto. intros id IN LIVE; eapply FREE; eauto. Qed.

Lemma scratch_free_head iterator bound rest live : scratch_free ((iterator, bound) :: rest) live ->
  iterator <> bound /\ ~ In iterator live /\ ~ In bound live /\
    scratch_free rest (iterator :: bound :: live).
Proof.
  intros [NODUP FREE]; cbn in *.
  inversion NODUP as [|a l ITER NODUP']; subst.
  inversion NODUP' as [|a l BOUND TAIL]; subst.
  split; [intro EQ; subst; apply ITER; cbn; auto |].
  split; [apply FREE; auto |]. split; [apply FREE; auto |].
  split; [exact TAIL |]. intros id IN; cbn; intros [EQ|[EQ|LIVE]].
  - subst; apply ITER; cbn; auto.
  - subst; apply BOUND; auto.
  - eapply FREE; eauto.
Qed.

Module PolCertNestedClightFor (I : INSTR) (M : LOOP_MODEL I).
Module B := PolCertClightBodyFor I M.
Module C := B.C.
Module A := B.A.
Module G := B.G.
Module L := M.

Lemma typed_view_frame layout env le le' live :
  (forall id, In id layout -> In id live) -> temp_agree live le le' ->
  A.typed_view layout env le -> A.typed_view layout env le'.
Proof.
  intros SUB FRAME VIEW index id INDEX.
  destruct (VIEW _ _ INDEX) as [value [LOOKUP SIGNED]]. exists value; split; auto.
  rewrite FRAME; auto. apply SUB; eapply nth_error_In; eauto.
Qed.

Section LOWERING.
Variable lower_instruction : I.t -> list expr -> option statement.

Fixpoint compile_nested_raw layout bounds pool (st : L.stmt) : option statement :=
  match st with
  | L.Instr i es => match B.compile_operands layout bounds es with
      Some codes => lower_instruction i codes | None => None end
  | L.Seq sts => compile_nested_list_raw layout bounds pool sts
  | L.Guard t body => match A.lower_test layout bounds t,
      compile_nested_raw layout bounds pool body with
      Some tree, Some code => Some (tree_statement tree code Sskip) | _, _ => None end
  | L.Loop lower upper body => match pool with
      [] => None
    | (iterator, bound) :: rest =>
      if C.header_fresh layout iterator bound then
        match A.compile_expr layout bounds lower, A.compile_expr layout bounds upper with
        | Some (lo, li), Some (hi, ui) =>
          match compile_nested_raw (iterator :: layout)
            (A.Interval (A.lower li) (A.upper ui) :: bounds) rest body with
          | Some code => Some (initialized_counted_loop iterator bound lo hi code)
          | None => None end
        | _, _ => None end
      else None end
  end
with compile_nested_list_raw layout bounds pool (sts : L.stmt_list) : option statement :=
  match sts with
  | L.SNil => Some Sskip
  | L.SCons st rest => match compile_nested_raw layout bounds pool st,
      compile_nested_list_raw layout bounds pool rest with
      Some code, Some codes => Some (Ssequence code codes) | _, _ => None end
  end.

End LOWERING.

Section BACKEND.
Variable function_entry : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable view : I.State.t -> mem -> Prop.
Variable backend : B.instruction_backend function_entry ge locals view.

Definition compile_nested := compile_nested_raw (B.lower_instruction backend).
Definition compile_nested_list := compile_nested_list_raw (B.lower_instruction backend).

Lemma loop_framed_clight iterator bound code live base env lower upper body source target le m0 :
  iterator <> bound -> ~ In iterator live -> signed_range (L.eval_expr env lower) ->
  signed_range (L.eval_expr env upper) ->
  le ! iterator = Some (Vint (Int.repr (L.eval_expr env lower))) ->
  le ! bound = Some (Vint (Int.repr (L.eval_expr env upper))) ->
  temp_agree live base le ->
  (forall x s0 s1 temps m, signed_range x -> L.eval_expr env lower <= x -> x < L.eval_expr env upper ->
    L.loop_semantics body (x :: env) s0 s1 -> view s0 m -> temp_agree live base temps ->
    temps ! iterator = Some (Vint (Int.repr x)) ->
    temps ! bound = Some (Vint (Int.repr (L.eval_expr env upper))) ->
    exists temps' m', view s1 m' /\ temp_agree (iterator :: bound :: live) temps temps' /\
      exec_stmt function_entry ge locals temps m code E0 temps' m' Out_normal) ->
  L.loop_semantics (L.Loop lower upper body) env source target -> view source m0 ->
  exists le1 m1, view target m1 /\ temp_agree live le le1 /\
    exec_stmt function_entry ge locals le m0 (counted_loop iterator bound code) E0 le1 m1 Out_normal.
Proof.
  intros DISTINCT FRESH RL RU ITER BOUND FRAME0 BODY SOURCE MEMORY.
  inversion SOURCE; subst.
  destruct (Z_lt_ge_dec (L.eval_expr env lower) (L.eval_expr env upper)) as [LT|EMPTY].
  - assert (LENGTH : L.eval_expr env upper = L.eval_expr env lower +
      Z.of_nat (Z.to_nat (L.eval_expr env upper - L.eval_expr env lower)))
      by (rewrite Z2Nat.id by lia; lia).
    assert (COUNT : counted_iterations (fun x => L.loop_semantics body (x :: env))
      (Z.to_nat (L.eval_expr env upper - L.eval_expr env lower))
      (L.eval_expr env lower) source target).
    { apply (proj1 (@C.range_iterations
        (Z.to_nat (L.eval_expr env upper - L.eval_expr env lower))
        (fun x => L.loop_semantics body (x :: env))
        (L.eval_expr env lower) (L.eval_expr env upper) source target LENGTH)); assumption. }
    destruct (@framed_counted_loop_correct I.State.t
      (fun x => L.loop_semantics body (x :: env)) view function_entry ge locals iterator bound code
      (L.eval_expr env upper) (L.eval_expr env lower) live base DISTINCT FRESH RU BODY
      _ _ _ _ le m0 COUNT LENGTH RL (Z.le_refl _) MEMORY FRAME0 ITER BOUND)
      as [le1 [m1 [V [_ [_ [FRAME EXEC]]]]]].
    exists le1, m1; auto.
  - match goal with ITERATIONS : I.IterSem.iter_semantics _ _ _ _ |- _ =>
      rewrite Zrange_empty in ITERATIONS by lia; inversion ITERATIONS; subst end.
    exists le, m0; repeat split; auto using temp_agree_refl.
    unfold counted_loop; eapply exec_Sloop_stop1 with (out' := Out_break).
    + destruct (@counter_condition_at ge locals le m0 iterator bound
        (L.eval_expr env lower) (L.eval_expr env upper) DISTINCT ITER BOUND RL RU)
        as [value [EV BOOL]].
      assert (CHECK : (L.eval_expr env lower <? L.eval_expr env upper) = false)
        by (apply Z.ltb_ge; lia).
      rewrite CHECK in BOOL. eapply exec_Sifthenelse with (b := false);
        [exact EV | exact BOOL | constructor].
    + constructor.
Qed.

Scheme nested_stmt_ind2 := Induction for L.stmt Sort Prop
with nested_list_ind2 := Induction for L.stmt_list Sort Prop.
Combined Scheme nested_stmt_list_ind from nested_stmt_ind2, nested_list_ind2.

Definition nested_contract (st : L.stmt) := forall layout bounds pool code env le source target m0 live,
  compile_nested layout bounds pool st = Some code -> scratch_free pool (layout ++ live) ->
  A.env_within bounds env -> A.typed_view layout env le ->
  L.loop_semantics st env source target -> view source m0 ->
  exists le1 m1, view target m1 /\ temp_agree (layout ++ live) le le1 /\
    exec_stmt function_entry ge locals le m0 code E0 le1 m1 Out_normal.

Definition nested_list_contract (sts : L.stmt_list) :=
  forall layout bounds pool code env le source target m0 live,
  compile_nested_list layout bounds pool sts = Some code -> scratch_free pool (layout ++ live) ->
  A.env_within bounds env -> A.typed_view layout env le ->
  L.loop_semantics (L.Seq sts) env source target -> view source m0 ->
  exists le1 m1, view target m1 /\ temp_agree (layout ++ live) le le1 /\
    exec_stmt function_entry ge locals le m0 code E0 le1 m1 Out_normal.

Theorem compile_nested_contracts :
  (forall st, nested_contract st) /\ (forall sts, nested_list_contract sts).
Proof.
  apply nested_stmt_list_ind.
  - intros lower upper body IH layout bounds pool code env le source target m0 live
      COMPILE FREE WITHIN VIEW SOURCE MEMORY.
    cbn [compile_nested compile_nested_raw compile_nested_list_raw] in COMPILE.
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
      { eapply typed_view_frame; [|exact FRAME | exact VIEW].
        intros id IN; apply in_or_app; auto. }
      assert (INPUT : A.typed_view (iterator :: layout) (x :: env) temps).
      { rewrite <- (@counter_temps_same iterator temps x ITER).
        apply A.typed_view_cons; auto. }
      assert (RFREE : scratch_free rest ((iterator :: layout) ++ bound :: live)).
      { eapply scratch_free_weaken; [|exact REST_FREE].
        intros id IN; cbn in IN |- *; rewrite in_app_iff in IN |- *;
          cbn in IN |- *; tauto. }
      destruct (IH (iterator :: layout) (A.Interval (A.lower li) (A.upper ui) :: bounds)
        rest generated (x :: env) temps s0 s1 m (bound :: live) BODY RFREE)
        as [temps' [m' [V' [PUBLIC EXEC]]]]; auto.
      - apply A.env_within_cons; [unfold A.contains in *; cbn; lia | exact WITHIN].
      - exists temps', m'; repeat split; auto.
        eapply temp_agree_weaken; [|exact PUBLIC].
        intros id IN; cbn in IN |- *; rewrite in_app_iff in IN |- *;
          cbn in IN |- *; tauto. }
    destruct (@loop_framed_clight iterator bound generated (layout ++ live) le env lower upper
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
      COMPILE FREE WITHIN VIEW SOURCE MEMORY.
    cbn [compile_nested compile_nested_raw compile_nested_list_raw] in COMPILE.
    fold compile_nested compile_nested_list in COMPILE.
    destruct (B.compile_operands layout bounds operands) as [codes|] eqn:OPERANDS; try discriminate.
    inversion SOURCE; subst.
    destruct (@B.instruction_execution function_entry ge locals view backend i codes
      (map (L.eval_expr env) operands) code le m0 source target wcs rcs COMPILE)
      as [m1 [V EXEC]]; eauto using B.compile_operands_correct.
    exists le, m1; auto using temp_agree_refl.
  - intros sts IH layout bounds pool code env le source target m0 live
      COMPILE FREE WITHIN VIEW SOURCE MEMORY.
    eapply IH; eauto.
  - intros test body IH layout bounds pool code env le source target m0 live
      COMPILE FREE WITHIN VIEW SOURCE MEMORY.
    cbn [compile_nested compile_nested_raw compile_nested_list_raw] in COMPILE.
    fold compile_nested compile_nested_list in COMPILE.
    destruct (A.lower_test layout bounds test) as [tree|] eqn:TEST; try discriminate.
    destruct (compile_nested layout bounds pool body) as [generated|] eqn:BODY; try discriminate.
    inversion COMPILE; subst code. inversion SOURCE; subst.
    + match goal with RUN : L.loop_semantics body env source target |- _ =>
        destruct (IH _ _ _ _ _ _ _ _ _ live BODY FREE WITHIN VIEW RUN MEMORY)
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
      COMPILE FREE WITHIN VIEW SOURCE MEMORY.
    inversion COMPILE; subst code. inversion SOURCE; subst target.
    exists le, m0; repeat split; auto using temp_agree_refl; constructor.
  - intros st IH rest IHR layout bounds pool code env le source target m0 live
      COMPILE FREE WITHIN VIEW SOURCE MEMORY.
    cbn [compile_nested_list compile_nested_raw compile_nested_list_raw] in COMPILE.
    fold (compile_nested_raw (B.lower_instruction backend))
      (compile_nested_list_raw (B.lower_instruction backend)) in COMPILE.
    fold compile_nested compile_nested_list in COMPILE.
    destruct (compile_nested layout bounds pool st) as [first|] eqn:FIRST; try discriminate.
    destruct (compile_nested_list layout bounds pool rest) as [remaining|] eqn:REST; try discriminate.
    inversion COMPILE; subst code. inversion SOURCE; subst.
    match goal with RUN : L.loop_semantics st env source ?next |- _ =>
      destruct (IH _ _ _ _ _ _ _ _ _ live FIRST FREE WITHIN VIEW RUN MEMORY)
        as [middle [m1 [V1 [FRAME1 EXEC1]]]] end.
    assert (VIEW1 : A.typed_view layout env middle).
    { eapply typed_view_frame; [|exact FRAME1 | exact VIEW].
      intros id IN; apply in_or_app; auto. }
    match goal with RUN : L.loop_semantics (L.Seq rest) env ?next target |- _ =>
      destruct (IHR _ _ _ _ _ _ _ _ _ live REST FREE WITHIN VIEW1 RUN V1)
        as [final [m2 [V2 [FRAME2 EXEC2]]]] end.
    exists final, m2; repeat split; auto.
    + eapply temp_agree_trans; eauto.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); eauto.
Qed.

Theorem compile_nested_correct st : nested_contract st.
Proof. apply compile_nested_contracts. Qed.

Fixpoint fresh_names names live : bool :=
  match names with [] => true
  | id :: rest => negb (existsb (Pos.eqb id) live) && fresh_names rest (id :: live) end.

Lemma fresh_names_sound names : forall live, fresh_names names live = true ->
  NoDup names /\ forall id, In id names -> ~ In id live.
Proof.
  induction names as [|id names IH]; intros live CHECK; cbn [fresh_names] in CHECK.
  - split; [constructor | intros key IN; contradiction].
  - apply andb_true_iff in CHECK as [HEAD TAIL].
    apply C.missing_ident in HEAD.
    destruct (IH _ TAIL) as [NODUP FREE]. split.
    + constructor; auto. intro IN; apply (FREE id IN); cbn; auto.
    + intros key [EQ|IN]; [subst; exact HEAD |].
      intro LIVE; apply (FREE key IN); cbn; auto.
Qed.

Definition scratch_check pool live := fresh_names (scratch_names pool) live.

Lemma scratch_check_sound pool live : scratch_check pool live = true -> scratch_free pool live.
Proof. apply fresh_names_sound. Qed.

Definition checked_compile_nested layout bounds live pool st :=
  if scratch_check pool (layout ++ live) then compile_nested layout bounds pool st else None.

Theorem checked_compile_nested_correct layout bounds live pool st code env le source target m0 :
  checked_compile_nested layout bounds live pool st = Some code ->
  A.typed_view layout env le ->
  decision_run (Entry ge locals le m0) (G.range_guard layout bounds) true ->
  L.loop_semantics st env source target -> view source m0 ->
  exists le1 m1, view target m1 /\ temp_agree (layout ++ live) le le1 /\
    exec_stmt function_entry ge locals le m0 code E0 le1 m1 Out_normal.
Proof.
  unfold checked_compile_nested; intros COMPILE VIEW GUARD SOURCE MEMORY.
  destruct (scratch_check pool (layout ++ live)) eqn:FRESH; try discriminate.
  eapply compile_nested_correct; eauto using scratch_check_sound.
  eapply G.range_guard_sound with (layout := layout) (s := Entry ge locals le m0);
    exact VIEW || exact GUARD.
Qed.

Example two_layers_compile :
  checked_compile_nested [1%positive] [A.Interval 0 100] []
    [(2%positive, 3%positive); (4%positive, 5%positive)]
    (L.Loop (L.Constant 0) (L.Var 0)
      (L.Loop (L.Constant 0) (L.Sum (L.Var 0) (L.Constant 1)) (L.Seq L.SNil))) =
  Some (initialized_counted_loop 2%positive 3%positive
    (Econst_int Int.zero type_int32s) (Etempvar 1%positive type_int32s)
    (initialized_counted_loop 4%positive 5%positive
      (Econst_int Int.zero type_int32s)
      (Ebinop Oadd (Etempvar 2%positive type_int32s) (Econst_int Int.one type_int32s) type_int32s)
      Sskip)).
Proof. vm_compute; reflexivity. Qed.

Example live_temporary_collision_rejected :
  checked_compile_nested [] [] [2%positive] [(2%positive, 3%positive)]
    (L.Loop (L.Constant 0) (L.Constant 10) (L.Seq L.SNil)) = None.
Proof. vm_compute; reflexivity. Qed.

Example repeated_scratch_rejected :
  scratch_check [(2%positive, 3%positive); (3%positive, 4%positive)] [] = false.
Proof. vm_compute; reflexivity. Qed.

Example insufficient_depth_rejected :
  compile_nested [] [] [(2%positive, 3%positive)]
    (L.Loop (L.Constant 0) (L.Constant 10)
      (L.Loop (L.Constant 0) (L.Constant 10) (L.Seq L.SNil))) = None.
Proof. vm_compute; reflexivity. Qed.

End BACKEND.

Definition checked_compile_nested_raw lower layout bounds live pool st :=
  if scratch_check pool (layout ++ live) then compile_nested_raw lower layout bounds pool st
  else None.

Lemma checked_compile_nested_raw_agrees function_entry ge locals view
  (backend : B.instruction_backend function_entry ge locals view) layout bounds live pool st :
  checked_compile_nested_raw (B.lower_instruction backend) layout bounds live pool st =
    checked_compile_nested backend layout bounds live pool st.
Proof. reflexivity. Qed.

Theorem checked_compile_nested_steps temps p locals (view : I.State.t -> mem -> Prop)
  (backend : B.instruction_backend (fun ge => ClightGuard.adapter_entry temps ge)
    (globalenv p) locals view) layout bounds live pool st code env le source target m0 f k :
  checked_compile_nested backend layout bounds live pool st = Some code ->
  A.typed_view layout env le ->
  decision_run (Entry (globalenv p) locals le m0) (G.range_guard layout bounds) true ->
  L.loop_semantics st env source target -> view source m0 ->
  exists le1 m1, view target m1 /\ temp_agree (layout ++ live) le le1 /\
    Smallstep.star (ClightGuard.adapter_step temps) (globalenv p)
      (State f code k locals le m0) E0 (State f Sskip k locals le1 m1).
Proof.
  intros COMPILE VIEW GUARD SOURCE MEMORY.
  destruct (@checked_compile_nested_correct (fun ge => ClightGuard.adapter_entry temps ge)
    (globalenv p) locals view backend layout bounds live pool st code env le source target m0
    COMPILE VIEW GUARD SOURCE MEMORY) as [le1 [m1 [V [FRAME EXEC]]]].
  exists le1, m1; repeat split; auto. apply normal_fragment_steps; exact EXEC.
Qed.

Print Assumptions compile_nested_correct.
Print Assumptions checked_compile_nested_correct.
Print Assumptions checked_compile_nested_steps.
End PolCertNestedClightFor.
