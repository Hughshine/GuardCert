From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Misc.
From polcert.polygen Require Import InstrTy Loop.
From Guard Require Import PolCertLoopGuard PolCertAffineClight PolCertFloorMembership.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A checked postpass above the semantic kernel.  The polyhedral checker may
    validate an affine enclosure with a membership guard.  This service removes
    the inactive suffix without asking that checker to extract division bounds.
    Machine lowering still checks every expression in the resulting program. *)
Module PolCertGuardedLoopTighteningFor (I : INSTR) (M : LOOP_MODEL I).
Module L := M.
Module A := PolCertAffineClightFor I M.
Module IS := I.IterSem.

Fixpoint remove_binder (e : L.expr) : option L.expr :=
  match e with
  | L.Constant z => Some (L.Constant z)
  | L.Var O => None
  | L.Var (S n) => Some (L.Var n)
  | L.Sum a b => match remove_binder a,remove_binder b with
      Some a,Some b=>Some (L.Sum a b) | _,_=>None end
  | L.Mult k a => option_map (L.Mult k) (remove_binder a)
  | L.Div a k => option_map (fun a=>L.Div a k) (remove_binder a)
  | _=>None end.
Lemma remove_binder_sound e : forall result x env,
  remove_binder e=Some result -> L.eval_expr (x::env) e=L.eval_expr env result.
Proof.
  induction e; intros result x env EQ; cbn [remove_binder] in EQ; try discriminate.
  - inversion EQ; reflexivity.
  - destruct (remove_binder e1) as [a|] eqn:E1;
      destruct (remove_binder e2) as [b|] eqn:E2; try discriminate.
    inversion EQ; subst; cbn [L.eval_expr]; rewrite (IHe1 _ _ _ eq_refl),(IHe2 _ _ _ eq_refl); reflexivity.
  - destruct (remove_binder e) as [a|] eqn:E; try discriminate.
    inversion EQ; subst; cbn [L.eval_expr]; rewrite (IHe _ _ _ eq_refl); reflexivity.
  - destruct (remove_binder e) as [a|] eqn:E; try discriminate.
    inversion EQ; subst; cbn [L.eval_expr]; rewrite (IHe _ _ _ eq_refl); reflexivity.
  - destruct n; try discriminate; inversion EQ; reflexivity.
Qed.

Definition successor_shape (e : L.expr) : bool :=
  match e with L.Sum (L.Var O) (L.Constant one)=>Z.eqb one 1 | _=>false end.
Lemma successor_shape_sound e x env : successor_shape e=true ->
  L.eval_expr (x::env) e=x+1.
Proof.
  destruct e; cbn [successor_shape]; try discriminate.
  destruct e1; try discriminate; destruct n; try discriminate.
  destruct e2; try discriminate; intro EQ; apply Z.eqb_eq in EQ; subst; reflexivity.
Qed.
Definition upper_factor (e : L.expr) : option Z :=
  if successor_shape e then Some 1 else
  match e with L.Mult factor operand=>
    if (0<?factor) && successor_shape operand then Some factor else None
  | _=>None end.
Lemma upper_factor_sound e factor x env : upper_factor e=Some factor ->
  0<factor /\ L.eval_expr (x::env) e=factor*(x+1).
Proof.
  unfold upper_factor; destruct (successor_shape e) eqn:SUCCESSOR.
  - intro EQ; inversion EQ; subst; split; [lia|rewrite (successor_shape_sound _ _ _ SUCCESSOR); lia].
  - destruct e; try discriminate.
    destruct ((0<?z) && successor_shape e) eqn:CHECK; try discriminate.
    intro EQ; inversion EQ; subst; apply andb_true_iff in CHECK as [POSITIVE SHAPE].
    apply Z.ltb_lt in POSITIVE; split; auto.
    cbn [L.eval_expr]; rewrite (successor_shape_sound _ _ _ SHAPE); reflexivity.
Qed.

Fixpoint guard_upper (test : L.test) : option L.expr :=
  match test with
  | L.LE lhs rhs=>match upper_factor lhs,remove_binder rhs with
      Some factor,Some numerator=>Some (L.Div numerator factor) | _,_=>None end
  | L.And first second=>match guard_upper first with Some bound=>Some bound
      | None=>guard_upper second end
  | _=>None end.
Lemma guard_upper_sound test : forall bound x env,
  guard_upper test=Some bound -> L.eval_test (x::env) test=true ->
  x<L.eval_expr env bound.
Proof.
  induction test; intros bound x env EQ ACCEPT; cbn [guard_upper] in EQ; try discriminate.
  - destruct (upper_factor e) as [factor|] eqn:FACTOR;
      destruct (remove_binder e0) as [numerator|] eqn:NUMERATOR; try discriminate.
    inversion EQ; subst; cbn [L.eval_test] in ACCEPT; apply Z.leb_le in ACCEPT.
    destruct (@upper_factor_sound e factor x env FACTOR) as [POSITIVE VALUE].
    rewrite VALUE,(@remove_binder_sound e0 numerator x env NUMERATOR) in ACCEPT.
    cbn [L.eval_expr]; apply (proj2 (@lt_floor_cleared (L.eval_expr env numerator) factor x POSITIVE)); exact ACCEPT.
  - apply andb_true_iff in ACCEPT as [LEFT RIGHT].
    destruct (guard_upper test1) as [candidate|] eqn:LEFT_BOUND.
    + inversion EQ; subst; eapply IHtest1; eauto.
    + eapply IHtest2; eauto.
Qed.

Definition tightened_upper bounds upper body :=
  match body with
  | L.Guard test _=>match guard_upper test,A.analyze bounds upper with
    | Some bound,Some original=>match A.analyze bounds bound with
      | Some proposed=>if A.upper proposed<=?A.lower original then bound else upper
      | None=>upper end
    | _,_=>upper end
  | _=>upper end.
Lemma tightened_upper_sound bounds upper body env : A.env_within bounds env ->
  L.eval_expr env (tightened_upper bounds upper body)<=L.eval_expr env upper /\
  forall x before after, x<L.eval_expr env upper ->
    L.eval_expr env (tightened_upper bounds upper body)<=x ->
    L.loop_semantics body (x::env) before after -> before=after.
Proof.
  intro WITHIN; unfold tightened_upper.
  destruct body; try (split; [lia|intros; lia]).
  destruct (guard_upper t) as [bound|] eqn:BOUND;
    destruct (A.analyze bounds upper) as [original|] eqn:ORIGINAL;
    try (split; [lia|intros; lia]).
  destruct (A.analyze bounds bound) as [proposed|] eqn:PROPOSED;
    try (split; [lia|intros; lia]).
  destruct (A.upper proposed<=?A.lower original) eqn:ORDER;
    [|split; [lia|intros; lia]].
  apply Z.leb_le in ORDER.
  destruct (A.analyze_sound _ ORIGINAL WITHIN) as [ORIGINAL_RANGE _].
  destruct (A.analyze_sound _ PROPOSED WITHIN) as [PROPOSED_RANGE _].
  unfold A.contains in *; split; [lia|].
  intros x before after OLD NEW RUN; inversion RUN; subst; auto.
  exfalso; match goal with ACCEPT : L.eval_test _ _=true |- _=>
    pose proof (@guard_upper_sound t bound x env BOUND ACCEPT); lia end.
Qed.

Lemma iter_filter (P : Z -> I.State.t -> I.State.t -> Prop) keep xs before after :
  (forall x a b, In x xs -> keep x=false -> P x a b -> a=b) ->
  IS.iter_semantics P xs before after -> IS.iter_semantics P (filter keep xs) before after.
Proof.
  intros QUIET RUN; induction RUN.
  - constructor.
  - cbn [filter]; destruct (keep x) eqn:KEEP.
    + econstructor; [exact H|apply IHRUN; intros; eapply QUIET; eauto; right; assumption].
    + assert (st1=st2) by (eapply QUIET; eauto; left; reflexivity).
      subst st2; apply IHRUN; intros; eapply QUIET; eauto; right; assumption.
Qed.
Lemma filter_false xs (keep : Z -> bool) :
  (forall x, In x xs -> keep x=false) -> filter keep xs=[].
Proof.
  induction xs; intro ALL; cbn; auto.
  rewrite (ALL a ltac:(left; reflexivity)); apply IHxs; intros; apply ALL; right; assumption.
Qed.
Lemma filter_Zrange lower upper original : upper<=original ->
  filter (fun x=>x<?upper) (Zrange lower original)=Zrange lower upper.
Proof.
  remember (length (Zrange lower original)) as fuel eqn:LENGTH.
  revert lower upper original LENGTH.
  induction fuel using lt_wf_ind; intros lower upper original LENGTH ORDER.
  destruct (Z_lt_ge_dec lower original) as [ACTIVE|EMPTY].
  - rewrite Zrange_begin by exact ACTIVE.
    destruct (Z_lt_ge_dec lower upper) as [ACTIVE_NEW|EMPTY_NEW].
    + rewrite (Zrange_begin lower upper ACTIVE_NEW); cbn [filter].
      assert ((lower<?upper)=true) as KEEP by (apply Z.ltb_lt; exact ACTIVE_NEW).
      rewrite KEEP; f_equal.
      eapply (H (length (Zrange (lower+1) original)));
        [rewrite Zrange_begin in LENGTH by exact ACTIVE; cbn in LENGTH; lia|reflexivity|exact ORDER].
    + rewrite (Zrange_empty lower upper ltac:(lia)); apply filter_false; intros x MEMBER.
      cbn in MEMBER; destruct MEMBER as [<-|MEMBER]; [apply Z.ltb_ge; lia|].
      apply Zrange_in in MEMBER; apply Z.ltb_ge; lia.
  - rewrite !Zrange_empty by lia; reflexivity.
Qed.

Fixpoint tighten bounds (statement : L.stmt) : L.stmt :=
  match statement with
  | L.Loop lower upper body=>match A.analyze bounds lower,A.analyze bounds upper with
    | Some lo,Some hi=>L.Loop lower (tightened_upper bounds upper body)
        (tighten (A.Interval (A.lower lo) (A.upper hi)::bounds) body)
    | _,_=>statement end
  | L.Guard test body=>L.Guard test (tighten bounds body)
  | L.Seq sequence=>L.Seq (tighten_list bounds sequence)
  | _=>statement end
with tighten_list bounds (sequence : L.stmt_list) : L.stmt_list :=
  match sequence with L.SNil=>L.SNil
  | L.SCons head tail=>L.SCons (tighten bounds head) (tighten_list bounds tail) end.

Scheme tightening_stmt_ind := Induction for L.stmt Sort Prop
with tightening_list_ind := Induction for L.stmt_list Sort Prop.
Combined Scheme tightening_ind from tightening_stmt_ind,tightening_list_ind.
Theorem tighten_sound :
  (forall statement bounds env before after, A.env_within bounds env ->
    L.loop_semantics statement env before after ->
    L.loop_semantics (tighten bounds statement) env before after) /\
  (forall sequence bounds env before after, A.env_within bounds env ->
    L.loop_semantics (L.Seq sequence) env before after ->
    L.loop_semantics (L.Seq (tighten_list bounds sequence)) env before after).
Proof.
  apply tightening_ind; intros.
  - cbn [tighten]; destruct (A.analyze bounds e) as [lo|] eqn:LOWER;
      destruct (A.analyze bounds e0) as [hi|] eqn:UPPER; try assumption.
    destruct (@tightened_upper_sound bounds e0 s env H0) as [ORDER QUIET].
    inversion H1; subst; apply L.LLoop.
    rewrite <- (@filter_Zrange (L.eval_expr env e) (L.eval_expr env (tightened_upper bounds e0 s))
      (L.eval_expr env e0) ORDER).
    eapply IS.iter_semantics_map.
    + intros x a b MEMBER BODY; apply filter_In in MEMBER as [MEMBER KEEP].
      apply Zrange_in in MEMBER; apply H; [|exact BODY].
      apply A.env_within_cons; [|exact H0].
      destruct (A.analyze_sound _ LOWER H0) as [LO _].
      destruct (A.analyze_sound _ UPPER H0) as [HI _].
      unfold A.contains in *; cbn; lia.
    + eapply iter_filter; [|eassumption].
      intros x a b MEMBER REFUSE BODY; apply Zrange_in in MEMBER; apply Z.ltb_ge in REFUSE.
      eapply QUIET; eauto; lia.
  - cbn [tighten]; assumption.
  - cbn [tighten]; eauto.
  - cbn [tighten]; inversion H1; subst.
    + apply L.LGuardTrue; [eapply H; eauto|assumption].
    + apply L.LGuardFalse; assumption.
  - cbn [tighten_list]; assumption.
  - cbn [tighten_list]; inversion H2; subst; eapply L.LSeq; [eapply H|eapply H0]; eauto.
Qed.
Corollary tighten_execution statement bounds env before after :
  A.env_within bounds env -> L.loop_semantics statement env before after ->
  L.loop_semantics (tighten bounds statement) env before after.
Proof. apply tighten_sound. Qed.
End PolCertGuardedLoopTighteningFor.
