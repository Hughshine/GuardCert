From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Misc.
From polcert.polygen Require Import InstrTy Loop.
From Guard Require Import PolCertLoopGuard PolCertAffineClight PolCertGuardedLoopTightening.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A domain postpass above the kernel. It derives a sufficient quiet suffix
    from all guarded bodies, then selects a runtime upper bound using existing
    guard syntax. The selected result is consumed by actual machine lowering. *)
Module PolCertGuardedBodyPruningFor (I : INSTR) (M : LOOP_MODEL I).
Module L := M.
Module A := PolCertAffineClightFor I M.
Module T := PolCertGuardedLoopTighteningFor I M.
Module IS := I.IterSem.

Fixpoint quiet_bounds (body : L.stmt) : option (list L.expr) :=
  match body with
  | L.Guard test body=>match quiet_bounds body with
    | Some bounds=>Some bounds
    | None=>option_map (fun bound=>[bound]) (T.guard_upper test) end
  | L.Seq sequence=>quiet_list_bounds sequence
  | _=>None end
with quiet_list_bounds (sequence : L.stmt_list) : option (list L.expr) :=
  match sequence with
  | L.SNil=>Some []
  | L.SCons first rest=>match quiet_bounds first,quiet_list_bounds rest with
    | Some first,Some rest=>Some (first++rest) | _,_=>None end end.

Scheme pruning_stmt_ind := Induction for L.stmt Sort Prop
with pruning_list_ind := Induction for L.stmt_list Sort Prop.
Combined Scheme pruning_ind from pruning_stmt_ind,pruning_list_ind.

Theorem quiet_bounds_sound :
  (forall body bounds x env before after,
    quiet_bounds body=Some bounds ->
    Forall (fun bound=>L.eval_expr env bound<=x) bounds ->
    L.loop_semantics body (x::env) before after -> before=after) /\
  (forall sequence bounds x env before after,
    quiet_list_bounds sequence=Some bounds ->
    Forall (fun bound=>L.eval_expr env bound<=x) bounds ->
    L.loop_semantics (L.Seq sequence) (x::env) before after -> before=after).
Proof.
  apply pruning_ind; intros; cbn [quiet_bounds quiet_list_bounds] in *; try discriminate.
  - eapply H; eauto.
  - destruct (quiet_bounds s) as [choices|] eqn:CHOICES.
    + inversion H0; subst choices; inversion H2; subst; auto; eapply H; eauto.
    + destruct (T.guard_upper t) as [bound|] eqn:BOUND; cbn in H0; try discriminate.
      inversion H0; subst bounds; inversion H1; subst.
      inversion H2; subst; auto.
      exfalso; match goal with ACCEPT : L.eval_test _ _=true |- _=>
        pose proof (@T.guard_upper_sound t bound x env BOUND ACCEPT); lia end.
  - inversion H1; reflexivity.
  - destruct (quiet_bounds s) as [first|] eqn:FIRST;
      destruct (quiet_list_bounds s0) as [rest|] eqn:REST; try discriminate.
    inversion H1; subst bounds; apply Forall_app in H2 as [LEFT RIGHT].
    inversion H3; subst.
    transitivity mem2; [eapply H|eapply H0]; eauto.
Qed.

Definition expr_eq_dec : forall first second : L.expr, {first=second}+{first<>second}.
Proof. decide equality; apply Z.eq_dec || apply Nat.eq_dec. Defined.

Definition below_original bounds upper choices :=
  match A.analyze bounds upper with
  | None=>false
  | Some original=>forallb (fun choice=>match A.analyze bounds choice with
      | Some range=>A.upper range<=?A.lower original | None=>false end) choices end.
Lemma below_original_sound bounds upper choices env :
  A.env_within bounds env -> below_original bounds upper choices=true ->
  forall choice, In choice choices -> L.eval_expr env choice<=L.eval_expr env upper.
Proof.
  intros WITHIN CHECK choice MEMBER; unfold below_original in CHECK.
  destruct (A.analyze bounds upper) as [original|] eqn:ORIGINAL; try discriminate.
  apply forallb_forall with (x:=choice) in CHECK; [|exact MEMBER].
  destruct (A.analyze bounds choice) as [range|] eqn:RANGE; try discriminate.
  apply Z.leb_le in CHECK.
  destruct (A.analyze_sound _ ORIGINAL WITHIN) as [OLD _].
  destruct (A.analyze_sound _ RANGE WITHIN) as [NEW _].
  unfold A.contains in *; lia.
Qed.

Fixpoint select_bound best rest (continuation : L.expr -> L.stmt) : L.stmt :=
  match rest with
  | []=>continuation best
  | next::rest=>L.Seq
      (L.SCons (L.Guard (L.LE best next) (select_bound next rest continuation))
      (L.SCons (L.Guard (L.Not (L.LE best next)) (select_bound best rest continuation)) L.SNil)) end.
Lemma select_bound_execution best rest continuation env before after :
  (forall choice, In choice (best::rest) ->
    Forall (fun bound=>L.eval_expr env bound<=L.eval_expr env choice) (best::rest) ->
    L.loop_semantics (continuation choice) env before after) ->
  L.loop_semantics (select_bound best rest continuation) env before after.
Proof.
  revert best; induction rest as [|next rest IH]; intros best ALL; cbn [select_bound].
  - apply ALL; [left; reflexivity|constructor; [lia|constructor]].
  - destruct (L.eval_expr env best<=?L.eval_expr env next) eqn:ORDER.
    + apply Z.leb_le in ORDER.
      eapply L.LSeq with (mem2:=after).
      * apply L.LGuardTrue; [apply IH|cbn [L.eval_test]; apply Z.leb_le; exact ORDER].
        intros choice MEMBER MAXIMAL; apply ALL; [right; exact MEMBER|].
        constructor; [|exact MAXIMAL].
        inversion MAXIMAL; lia.
      * eapply L.LSeq with (mem2:=after); [apply L.LGuardFalse|constructor].
        cbn [L.eval_test]; apply Bool.negb_false_iff; apply Z.leb_le; exact ORDER.
    + apply Z.leb_gt in ORDER.
      eapply L.LSeq with (mem2:=before).
      * apply L.LGuardFalse; cbn [L.eval_test]; apply Z.leb_gt; exact ORDER.
      * eapply L.LSeq with (mem2:=after); [|constructor].
        apply L.LGuardTrue; [apply IH|cbn [L.eval_test]; apply Bool.negb_true_iff; apply Z.leb_gt; exact ORDER].
        intros choice MEMBER MAXIMAL; apply ALL.
        -- destruct MEMBER as [<-|MEMBER]; [left; reflexivity|right; right; exact MEMBER].
        -- inversion MAXIMAL; subst; constructor; [assumption|constructor; [lia|assumption]].
Qed.

Lemma shorten_loop_map lower upper selected body target env before after :
  L.eval_expr env selected<=L.eval_expr env upper ->
  (forall x a b, x<L.eval_expr env upper -> L.eval_expr env selected<=x ->
    L.loop_semantics body (x::env) a b -> a=b) ->
  (forall x a b, In x (Zrange (L.eval_expr env lower) (L.eval_expr env upper)) ->
    L.loop_semantics body (x::env) a b -> L.loop_semantics target (x::env) a b) ->
  L.loop_semantics (L.Loop lower upper body) env before after ->
  L.loop_semantics (L.Loop lower selected target) env before after.
Proof.
  intros ORDER QUIET BODY SOURCE; inversion SOURCE; subst; apply L.LLoop.
  rewrite <- (@T.filter_Zrange (L.eval_expr env lower) (L.eval_expr env selected)
    (L.eval_expr env upper) ORDER).
  eapply IS.iter_semantics_map with (P:=fun x=>L.loop_semantics body (x::env)).
  - intros x a b MEMBER RUN; apply filter_In in MEMBER as [MEMBER KEEP]; eapply BODY; eauto.
  - eapply T.iter_filter; [|eassumption].
    intros x a b MEMBER REFUSED RUN; apply Zrange_in in MEMBER; apply Z.ltb_ge in REFUSED.
    eapply QUIET; eauto; lia.
Qed.

Definition prune_loop bounds lower upper body target :=
  match quiet_bounds body with
  | None=>L.Loop lower upper target
  | Some choices=>let choices:=nodup expr_eq_dec choices in
    if below_original bounds upper choices then
      match choices with []=>L.Loop lower upper target
      | best::rest=>select_bound best rest (fun bound=>L.Loop lower bound target) end
    else L.Loop lower upper target end.
Lemma prune_loop_execution bounds lower upper body target env before after :
  A.env_within bounds env ->
  (forall x a b, In x (Zrange (L.eval_expr env lower) (L.eval_expr env upper)) ->
    L.loop_semantics body (x::env) a b -> L.loop_semantics target (x::env) a b) ->
  L.loop_semantics (L.Loop lower upper body) env before after ->
  L.loop_semantics (prune_loop bounds lower upper body target) env before after.
Proof.
  intros WITHIN BODY SOURCE.
  assert (ORIGINAL : L.loop_semantics (L.Loop lower upper target) env before after).
  { inversion SOURCE; subst; apply L.LLoop; eapply IS.iter_semantics_map with (P:=fun x=>L.loop_semantics body (x::env)); [exact BODY|eassumption]. }
  unfold prune_loop; destruct (quiet_bounds body) as [choices|] eqn:CHOICES; [|exact ORIGINAL].
  destruct (below_original bounds upper (nodup expr_eq_dec choices)) eqn:CHECK; [|exact ORIGINAL].
  remember (nodup expr_eq_dec choices) as unique eqn:UNIQUE.
  destruct unique as [|best rest]; [exact ORIGINAL|].
  apply select_bound_execution; intros chosen MEMBER MAXIMAL.
  eapply shorten_loop_map; [| |exact BODY|exact SOURCE].
  - eapply below_original_sound; [exact WITHIN|exact CHECK|exact MEMBER].
  - intros x a b OLD NEW RUN; eapply (proj1 quiet_bounds_sound); [exact CHOICES| |exact RUN].
    apply Forall_forall; intros bound IN.
    assert (IN_UNIQUE : In bound (best::rest)).
    { rewrite UNIQUE; apply nodup_In; exact IN. }
    apply Forall_forall with (x:=bound) in MAXIMAL; [lia|exact IN_UNIQUE].
Qed.

Fixpoint prune bounds (statement : L.stmt) : L.stmt :=
  match statement with
  | L.Loop lower upper body=>match A.analyze bounds lower,A.analyze bounds upper with
    | Some lo,Some hi=>prune_loop bounds lower upper body
        (prune (A.Interval (A.lower lo) (A.upper hi)::bounds) body)
    | _,_=>statement end
  | L.Guard test body=>L.Guard test (prune bounds body)
  | L.Seq sequence=>L.Seq (prune_list bounds sequence)
  | _=>statement end
with prune_list bounds (sequence : L.stmt_list) : L.stmt_list :=
  match sequence with L.SNil=>L.SNil
  | L.SCons head tail=>L.SCons (prune bounds head) (prune_list bounds tail) end.
Theorem prune_sound :
  (forall statement bounds env before after, A.env_within bounds env ->
    L.loop_semantics statement env before after ->
    L.loop_semantics (prune bounds statement) env before after) /\
  (forall sequence bounds env before after, A.env_within bounds env ->
    L.loop_semantics (L.Seq sequence) env before after ->
    L.loop_semantics (L.Seq (prune_list bounds sequence)) env before after).
Proof.
  apply pruning_ind; intros.
  - cbn [prune]; destruct (A.analyze bounds e) as [lo|] eqn:LOWER;
      destruct (A.analyze bounds e0) as [hi|] eqn:UPPER; try assumption.
    eapply prune_loop_execution; [exact H0| |exact H1].
    intros x a b MEMBER RUN; apply H; [|exact RUN].
    apply Zrange_in in MEMBER; apply A.env_within_cons; [|exact H0].
    destruct (A.analyze_sound _ LOWER H0) as [LO _].
    destruct (A.analyze_sound _ UPPER H0) as [HI _].
    unfold A.contains in *; cbn; lia.
  - cbn [prune]; assumption.
  - cbn [prune]; eauto.
  - cbn [prune]; inversion H1; subst.
    + apply L.LGuardTrue; [eapply H; eauto|assumption].
    + apply L.LGuardFalse; assumption.
  - cbn [prune_list]; assumption.
  - cbn [prune_list]; inversion H2; subst; eapply L.LSeq; [eapply H|eapply H0]; eauto.
Qed.
Corollary prune_execution statement bounds env before after :
  A.env_within bounds env -> L.loop_semantics statement env before after ->
  L.loop_semantics (prune bounds statement) env before after.
Proof. apply prune_sound. Qed.
End PolCertGuardedBodyPruningFor.
