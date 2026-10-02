From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events Globalenvs Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition.
Open Scope Z_scope.
Set Implicit Arguments.

(** The backend owns iterator/bound temporaries. A body implementation keeps
    those temporaries intact; here the first instance keeps every temporary.
    Mathematical loop bodies and their state relation remain parameters. *)
Definition counter_temps (iterator : ident) (le : temp_env) (x : Z) : temp_env :=
  PTree.set iterator (Vint (Int.repr x)) le.

Definition counter_condition (iterator bound : ident) :=
  Ebinop Olt (Etempvar iterator type_int32s) (Etempvar bound type_int32s) type_int32s.

Definition counter_increment (iterator : ident) :=
  Sset iterator (Ebinop Oadd (Etempvar iterator type_int32s)
    (Econst_int Int.one type_int32s) type_int32s).

Definition counted_loop (iterator bound : ident) (body : statement) :=
  Sloop (Sifthenelse (counter_condition iterator bound) body Sbreak)
    (counter_increment iterator).

Definition signed_range z := Int.min_signed <= z <= Int.max_signed.

Lemma counter_condition_run ge e le m iterator bound x upper :
  iterator <> bound -> le ! bound = Some (Vint (Int.repr upper)) ->
  signed_range x -> signed_range upper ->
  expression_test (counter_condition iterator bound)
    (Entry ge e (counter_temps iterator le x) m) (x <? upper).
Proof.
  intros DISTINCT BOUND RX RU. unfold expression_test.
  cbn [entry_ge entry_env entry_temps entry_memory].
  exists (Val.of_bool (x <? upper)); split.
  - eapply eval_Ebinop.
    + constructor. unfold counter_temps; apply PTree.gss.
    + constructor. unfold counter_temps; rewrite PTree.gso by congruence; exact BOUND.
    + change (Some (Val.of_bool (Int.lt (Int.repr x) (Int.repr upper))) =
        Some (Val.of_bool (x <? upper))).
      unfold Int.lt. rewrite !Int.signed_repr by assumption.
      destruct (zlt x upper) as [LT|GE].
      * assert ((x <? upper) = true) by (apply Z.ltb_lt; exact LT).
        rewrite H; reflexivity.
      * assert ((x <? upper) = false) by (apply Z.ltb_ge; lia).
        rewrite H; reflexivity.
  - destruct (x <? upper); reflexivity.
Qed.

Lemma normal_fragment_steps temps p locals le m code le' m' f k :
  exec_stmt (fun ge => adapter_entry temps ge) (globalenv p) locals le m
    code E0 le' m' Out_normal ->
  star (adapter_step temps) (globalenv p)
    (State f code k locals le m) E0 (State f Sskip k locals le' m').
Proof.
  intro RUN.
  destruct (@exec_stmt_steps (fun ge => adapter_entry temps ge) p
    locals le m code E0 le' m' Out_normal RUN f k) as [final [STEPS OUT]].
  inversion OUT; subst; exact STEPS.
Qed.

Lemma counter_increment_run function_entry ge e le m iterator x :
  signed_range x ->
  exec_stmt function_entry ge e (counter_temps iterator le x) m
    (counter_increment iterator) E0 (counter_temps iterator le (x + 1)) m Out_normal.
Proof.
  intro RANGE. unfold counter_increment.
  replace (counter_temps iterator le (x + 1)) with
    (PTree.set iterator (Vint (Int.repr (x + 1))) (counter_temps iterator le x))
    by (unfold counter_temps; rewrite PTree.set2; reflexivity).
  constructor. eapply eval_Ebinop.
  - constructor. unfold counter_temps; apply PTree.gss.
  - constructor.
  - change (Some (Vint (Int.add (Int.repr x) Int.one)) =
      Some (Vint (Int.repr (x + 1)))).
    rewrite Int.add_signed, Int.signed_repr by exact RANGE.
    change (Int.signed Int.one) with 1; reflexivity.
Qed.

Inductive counted_iterations {S : Type} (body : Z -> S -> S -> Prop) :
  nat -> Z -> S -> S -> Prop :=
| iterations_done : forall x s, counted_iterations body 0 x s s
| iterations_next : forall n x s0 s1 s2,
    body x s0 s1 -> counted_iterations body n (x + 1) s1 s2 ->
    counted_iterations body (Nat.succ n) x s0 s2.

Theorem counted_loop_correct {S : Type} (body_sem : Z -> S -> S -> Prop)
  (view : S -> mem -> Prop) function_entry ge e le iterator bound body upper floor :
  iterator <> bound -> le ! bound = Some (Vint (Int.repr upper)) ->
  signed_range upper ->
  (forall x s0 s1 m0, signed_range x -> floor <= x -> x < upper -> body_sem x s0 s1 ->
    view s0 m0 -> exists m1, view s1 m1 /\
      exec_stmt function_entry ge e (counter_temps iterator le x) m0 body
        E0 (counter_temps iterator le x) m1 Out_normal) ->
  forall n x s0 s1 m0, counted_iterations body_sem n x s0 s1 ->
    upper = x + Z.of_nat n -> signed_range x -> floor <= x -> view s0 m0 ->
    exists m1, view s1 m1 /\
      exec_stmt function_entry ge e (counter_temps iterator le x) m0
        (counted_loop iterator bound body) E0
        (counter_temps iterator le upper) m1 Out_normal.
Proof.
  intros DISTINCT BOUND RU BODY n x s0 s1 m0 RUN.
  revert m0; induction RUN; intros m0 LENGTH RX FLOOR VIEW.
  - cbn in LENGTH. assert (EQ : upper = x) by lia; clear LENGTH; subst upper.
    exists m0; split; auto. unfold counted_loop.
    eapply exec_Sloop_stop1 with (out' := Out_break).
    + destruct (counter_condition_run ge e le m0 DISTINCT BOUND RX RU) as [v [EV BOOL]].
      rewrite Z.ltb_irrefl in BOOL. eapply exec_Sifthenelse; eauto. constructor.
    + constructor.
  - assert (LT : x < upper) by (rewrite Nat2Z.inj_succ in LENGTH; lia).
    assert (RX' : signed_range (x + 1)) by (unfold signed_range in *; lia).
    destruct (BODY x s0 s1 m0 RX FLOOR LT H VIEW) as [m1 [V1 STEP]].
    destruct (IHRUN m1) as [m2 [V2 TAIL]]; auto;
      [rewrite Nat2Z.inj_succ in LENGTH; lia | lia |].
    exists m2; split; auto. unfold counted_loop.
    eapply exec_Sloop_loop with (out1 := Out_normal)
      (t1 := E0) (t2 := E0) (t3 := E0).
    + destruct (counter_condition_run ge e le m0 DISTINCT BOUND RX RU) as [v [EV BOOL]].
      assert (LTB : (x <? upper) = true) by (apply Z.ltb_lt; exact LT).
      rewrite LTB in BOOL. eapply exec_Sifthenelse; eauto.
    + constructor.
    + apply counter_increment_run; exact RX.
    + exact TAIL.
Qed.

Print Assumptions counted_loop_correct.

Definition initialized_counted_loop iterator bound lower upper body :=
  Ssequence (Sset bound upper)
    (Ssequence (Sset iterator lower) (counted_loop iterator bound body)).

Lemma initialized_counted_loop_run function_entry ge e le m iterator bound
  lower upper body lo hi le' m' :
  eval_expr ge e le m upper (Vint (Int.repr hi)) ->
  eval_expr ge e (PTree.set bound (Vint (Int.repr hi)) le) m lower (Vint (Int.repr lo)) ->
  exec_stmt function_entry ge e
    (counter_temps iterator (PTree.set bound (Vint (Int.repr hi)) le) lo) m
    (counted_loop iterator bound body) E0 le' m' Out_normal ->
  exec_stmt function_entry ge e le m
    (initialized_counted_loop iterator bound lower upper body) E0 le' m' Out_normal.
Proof.
  intros UPPER LOWER LOOP. unfold initialized_counted_loop.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor; exact UPPER |].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor; exact LOWER | exact LOOP].
Qed.
