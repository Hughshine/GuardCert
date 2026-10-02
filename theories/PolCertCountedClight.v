From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events Globalenvs Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From polcert.lib Require Import Misc.
From polcert.polygen Require Import InstrTy Loop.
From Guard Require Import PolCertLoopGuard ClightGuard ClightCondition ClightCountedLoop
  PolCertAffineClight PolCertAffineGuard.
Import ListNotations.
Open Scope Z_scope.
Set Implicit Arguments.

Module PolCertCountedClightFor (I : INSTR) (M : LOOP_MODEL I).
Module L := M.
Module G := PolCertAffineGuardFor I M.
Module A := G.A.

Lemma range_iterations n : forall R lower upper s0 s1,
  upper = lower + Z.of_nat n ->
  (I.IterSem.iter_semantics R (Zrange lower upper) s0 s1 <->
   counted_iterations R n lower s0 s1).
Proof.
  induction n; intros R lower upper s0 s1 LENGTH.
  - cbn in LENGTH. assert (EQ : upper = lower) by lia; clear LENGTH; subst upper.
    rewrite Zrange_empty by lia. split; intro RUN; inversion RUN; subst; constructor.
  - assert (LT : lower < upper) by (rewrite Nat2Z.inj_succ in LENGTH; lia).
    rewrite Zrange_begin by exact LT.
    assert (TAIL : upper = lower + 1 + Z.of_nat n)
      by (rewrite Nat2Z.inj_succ in LENGTH; lia).
    split; intro RUN; inversion RUN; subst.
    + econstructor; eauto. apply (proj1 (IHn _ _ _ _ _ TAIL)); eauto.
    + econstructor; eauto. apply (proj2 (IHn _ _ _ _ _ TAIL)); eauto.
Qed.

Theorem loop_counted_clight function_entry ge locals le iterator bound code
  env lower upper body source target (view : I.State.t -> mem -> Prop) :
  iterator <> bound -> le ! bound = Some (Vint (Int.repr (L.eval_expr env upper))) ->
  signed_range (L.eval_expr env lower) -> signed_range (L.eval_expr env upper) ->
  (forall x s0 s1 m0, signed_range x -> L.eval_expr env lower <= x -> x < L.eval_expr env upper ->
    L.loop_semantics body (x :: env) s0 s1 -> view s0 m0 ->
    exists m1, view s1 m1 /\
      exec_stmt function_entry ge locals (counter_temps iterator le x) m0 code
        E0 (counter_temps iterator le x) m1 Out_normal) ->
  L.loop_semantics (L.Loop lower upper body) env source target ->
  forall m0, view source m0 -> exists m1, view target m1 /\
    exec_stmt function_entry ge locals
      (counter_temps iterator le (L.eval_expr env lower)) m0
      (counted_loop iterator bound code) E0
      (counter_temps iterator le (Z.max (L.eval_expr env lower) (L.eval_expr env upper)))
      m1 Out_normal.
Proof.
  intros DISTINCT BOUND RL RU BODY RUN m0 VIEW. inversion RUN; subst.
  destruct (Z_lt_ge_dec (L.eval_expr env lower) (L.eval_expr env upper)) as [LT|GE].
  - rewrite Z.max_r by lia.
    assert (LENGTH : L.eval_expr env upper = L.eval_expr env lower +
      Z.of_nat (Z.to_nat (L.eval_expr env upper - L.eval_expr env lower)))
      by (rewrite Z2Nat.id by lia; lia).
    assert (COUNT : counted_iterations
      (fun x => L.loop_semantics body (x :: env))
      (Z.to_nat (L.eval_expr env upper - L.eval_expr env lower))
      (L.eval_expr env lower) source target).
    { apply (proj1 (@range_iterations
        (Z.to_nat (L.eval_expr env upper - L.eval_expr env lower))
        (fun x => L.loop_semantics body (x :: env))
        (L.eval_expr env lower) (L.eval_expr env upper) source target LENGTH));
        assumption. }
    eapply counted_loop_correct with (floor := L.eval_expr env lower); eauto; [exact BODY | lia].
  - match goal with ITER : I.IterSem.iter_semantics _ _ _ _ |- _ =>
      rewrite Zrange_empty in ITER by lia; inversion ITER; subst end.
    rewrite Z.max_l by lia. exists m0; split; auto. unfold counted_loop.
    eapply exec_Sloop_stop1 with (out' := Out_break).
    + destruct (counter_condition_run ge locals le m0 DISTINCT BOUND RL RU)
        as [v [EV BOOL]].
      assert (FALSE : (L.eval_expr env lower <? L.eval_expr env upper) = false)
        by (apply Z.ltb_ge; lia).
      rewrite FALSE in BOOL. eapply exec_Sifthenelse; eauto; constructor.
    + constructor.
Qed.

Definition header_fresh (layout : list ident) (iterator bound : ident) :=
  negb (Pos.eqb iterator bound) && negb (existsb (Pos.eqb iterator) layout) &&
    negb (existsb (Pos.eqb bound) layout).

Lemma missing_ident id layout : negb (existsb (Pos.eqb id) layout) = true ->
  ~ In id layout.
Proof.
  intros MISS IN. apply negb_true_iff in MISS.
  assert (PRESENT : existsb (Pos.eqb id) layout = true).
  { apply existsb_exists. exists id; split; auto. apply Pos.eqb_refl. }
  congruence.
Qed.

Lemma header_fresh_sound layout iterator bound : header_fresh layout iterator bound = true ->
  iterator <> bound /\ ~ In iterator layout /\ ~ In bound layout.
Proof.
  unfold header_fresh. repeat rewrite andb_true_iff.
  intros [[DISTINCT ITER] BOUND]. apply negb_true_iff in DISTINCT.
  apply Pos.eqb_neq in DISTINCT. repeat split; auto; eapply missing_ident; eauto.
Qed.

Arguments header_fresh_sound {layout iterator bound} _.

Definition compile_loop_header layout bounds iterator bound lower upper body :
  option statement :=
  if header_fresh layout iterator bound then
  match A.compile_expr layout bounds lower, A.compile_expr layout bounds upper with
  | Some (lo, _), Some (hi, _) =>
      Some (initialized_counted_loop iterator bound lo hi body)
  | _, _ => None end else None.

Theorem compile_loop_header_correct function_entry ge locals le iterator bound code
  layout bounds env lower upper body generated source target (view : I.State.t -> mem -> Prop) m0 :
  compile_loop_header layout bounds iterator bound lower upper code = Some generated ->
  A.typed_view layout env le ->
  decision_run (Entry ge locals le m0) (G.range_guard layout bounds) true ->
  (forall x s0 s1 m0, signed_range x -> L.eval_expr env lower <= x -> x < L.eval_expr env upper ->
    L.loop_semantics body (x :: env) s0 s1 -> view s0 m0 ->
    exists m1, view s1 m1 /\
      exec_stmt function_entry ge locals
        (counter_temps iterator (PTree.set bound (Vint (Int.repr (L.eval_expr env upper))) le) x)
        m0 code E0
        (counter_temps iterator (PTree.set bound (Vint (Int.repr (L.eval_expr env upper))) le) x)
        m1 Out_normal) ->
  L.loop_semantics (L.Loop lower upper body) env source target ->
  view source m0 -> exists m1, view target m1 /\
    exec_stmt function_entry ge locals le m0 generated E0
      (counter_temps iterator (PTree.set bound (Vint (Int.repr (L.eval_expr env upper))) le)
        (Z.max (L.eval_expr env lower) (L.eval_expr env upper))) m1 Out_normal.
Proof.
  intros COMPILE VIEW GUARD BODY RUN MEMORY.
  unfold compile_loop_header in COMPILE.
  destruct (header_fresh layout iterator bound) eqn:FRESH; try discriminate.
  destruct (A.compile_expr layout bounds lower) as [[lo li]|] eqn:LOWER;
    try discriminate.
  destruct (A.compile_expr layout bounds upper) as [[hi ui]|] eqn:UPPER;
    try discriminate.
  inversion COMPILE; subst generated.
  destruct (header_fresh_sound FRESH) as [DISTINCT [ITER_FRESH BOUND_FRESH]].
  assert (WITHIN : A.env_within bounds env).
  { eapply G.range_guard_sound with (layout := layout) (s := Entry ge locals le m0);
      exact VIEW || exact GUARD. }
  destruct (A.compile_expr_sound lower LOWER WITHIN VIEW) as [_ [RL [_ ELOWER]]].
  destruct (A.compile_expr_sound upper UPPER WITHIN VIEW) as [_ [RU [_ EUPPER]]].
  assert (VIEW' : A.typed_view layout env
    (PTree.set bound (Vint (Int.repr (L.eval_expr env upper))) le)).
  { apply A.typed_view_set_fresh; assumption. }
  destruct (A.compile_expr_sound lower LOWER WITHIN VIEW') as [_ [_ [_ ELOWER']]].
  assert (LOOP : exists m1, view target m1 /\
    exec_stmt function_entry ge locals
      (counter_temps iterator (PTree.set bound (Vint (Int.repr (L.eval_expr env upper))) le)
        (L.eval_expr env lower)) m0 (counted_loop iterator bound code) E0
      (counter_temps iterator (PTree.set bound (Vint (Int.repr (L.eval_expr env upper))) le)
        (Z.max (L.eval_expr env lower) (L.eval_expr env upper))) m1 Out_normal).
  { eapply loop_counted_clight; eauto. apply PTree.gss. }
  destruct LOOP as [m1 [FINAL EXEC]]. exists m1; split; auto.
  eapply initialized_counted_loop_run; eauto.
Qed.

Example aliased_header_temporaries_refused : header_fresh [1%positive] 2%positive 2%positive = false.
Proof. reflexivity. Qed.

Example iterator_overwrites_parameter_refused : header_fresh [1%positive] 1%positive 2%positive = false.
Proof. reflexivity. Qed.

Example affine_loop_header :
  compile_loop_header [1%positive] [A.Interval 0 100] 2%positive 3%positive
    (L.Constant 0) (L.Sum (L.Var 0) (L.Constant 1)) Sskip =
  Some (initialized_counted_loop 2%positive 3%positive
    (Econst_int Int.zero type_int32s)
    (Ebinop Oadd (Etempvar 1%positive type_int32s)
      (Econst_int Int.one type_int32s) type_int32s) Sskip).
Proof. vm_compute; reflexivity. Qed.

Theorem empty_body_loop_lowering function_entry ge locals le iterator bound
  layout bounds env lower upper generated (view : I.State.t -> mem -> Prop) source target m0 :
  compile_loop_header layout bounds iterator bound lower upper Sskip = Some generated ->
  A.typed_view layout env le ->
  decision_run (Entry ge locals le m0) (G.range_guard layout bounds) true ->
  L.loop_semantics (L.Loop lower upper (L.Seq L.SNil)) env source target ->
  view source m0 -> exists m1, view target m1 /\
    exec_stmt function_entry ge locals le m0 generated E0
      (counter_temps iterator (PTree.set bound (Vint (Int.repr (L.eval_expr env upper))) le)
        (Z.max (L.eval_expr env lower) (L.eval_expr env upper))) m1 Out_normal.
Proof.
  intros COMPILE VIEW GUARD SOURCE MEMORY.
  eapply compile_loop_header_correct; eauto.
  intros x s0 s1 m RX LO LT EMPTY V. inversion EMPTY; subst.
  exists m; split; auto; constructor.
Qed.

Theorem compile_loop_header_steps temps p locals le iterator bound code
  layout bounds env lower upper body generated source target (view : I.State.t -> mem -> Prop)
  m0 f k :
  compile_loop_header layout bounds iterator bound lower upper code = Some generated ->
  A.typed_view layout env le ->
  decision_run (Entry (globalenv p) locals le m0) (G.range_guard layout bounds) true ->
  (forall x s0 s1 m, signed_range x -> L.eval_expr env lower <= x -> x < L.eval_expr env upper ->
    L.loop_semantics body (x :: env) s0 s1 -> view s0 m ->
    exists m1, view s1 m1 /\
      exec_stmt (fun ge => adapter_entry temps ge) (globalenv p) locals
        (counter_temps iterator (PTree.set bound (Vint (Int.repr (L.eval_expr env upper))) le) x)
        m code E0
        (counter_temps iterator (PTree.set bound (Vint (Int.repr (L.eval_expr env upper))) le) x)
        m1 Out_normal) ->
  L.loop_semantics (L.Loop lower upper body) env source target -> view source m0 ->
  exists m1, view target m1 /\
    star (adapter_step temps) (globalenv p)
      (State f generated k locals le m0) E0
      (State f Sskip k locals
        (counter_temps iterator (PTree.set bound (Vint (Int.repr (L.eval_expr env upper))) le)
          (Z.max (L.eval_expr env lower) (L.eval_expr env upper))) m1).
Proof.
  intros COMPILE VIEW GUARD BODY SOURCE MEMORY.
  destruct (@compile_loop_header_correct (fun ge => adapter_entry temps ge)
    (globalenv p) locals le iterator bound code layout bounds env lower upper
    body generated source target view m0 COMPILE VIEW GUARD BODY SOURCE MEMORY)
    as [m1 [FINAL EXEC]]. exists m1; split; auto.
  apply normal_fragment_steps; exact EXEC.
Qed.

End PolCertCountedClightFor.

Module PolCertCountedClight (I : INSTR).
Module ConcreteLoop := Loop I.
Include PolCertCountedClightFor I ConcreteLoop.

Print Assumptions range_iterations.
Print Assumptions loop_counted_clight.
Print Assumptions compile_loop_header_correct.
Print Assumptions empty_body_loop_lowering.
Print Assumptions compile_loop_header_steps.

End PolCertCountedClight.
