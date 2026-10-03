From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Misc.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryPolyhedral GuardMemoryLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Finite traces are proof witnesses, not part of the extracted compiler. *)
Record memory_loop_event := MemoryLoopEvent {
  event_instruction : GuardMemoryInstr.t;
  event_environment : list Z;
  event_arguments : list Z
}.
Definition memory_event_step event before after :=
  exists writes reads, GuardMemoryInstr.instr_semantics
    (event_instruction event) (event_arguments event) writes reads before after.

Fixpoint memory_loop_trace (st : L.stmt) (env : list Z) : list memory_loop_event :=
  match st with
  | L.Instr instruction args => [MemoryLoopEvent instruction env (map (L.eval_expr env) args)]
  | L.Seq sts => memory_loop_list_trace sts env
  | L.Guard test body => if L.eval_test env test then memory_loop_trace body env else []
  | L.Loop lower upper body => flat_map (fun x => memory_loop_trace body (x :: env))
      (Zrange (L.eval_expr env lower) (L.eval_expr env upper))
  end
with memory_loop_list_trace (sts : L.stmt_list) (env : list Z) : list memory_loop_event :=
  match sts with
  | L.SNil => []
  | L.SCons st rest => memory_loop_trace st env ++ memory_loop_list_trace rest env
  end.

Lemma memory_iter_append {A} (step : A -> runtime_state -> runtime_state -> Prop) first :
  forall second before after,
  Iter.iter_semantics step (first ++ second) before after <->
  exists middle, Iter.iter_semantics step first before middle /\
    Iter.iter_semantics step second middle after.
Proof.
  induction first as [|a first IH]; intros second before after; cbn; split.
  - intro RUN; exists before; split; [constructor|exact RUN].
  - intros [middle [HEAD TAIL]]; inversion HEAD; subst; exact TAIL.
  - intro RUN; inversion RUN; subst.
    match goal with TAIL : Iter.iter_semantics _ (first ++ second) ?next after |- _ =>
      apply IH in TAIL as [middle [LEFT RIGHT]] end.
    exists middle; split; [econstructor; eauto|exact RIGHT].
  - intros [middle [HEAD TAIL]]; inversion HEAD; subst; econstructor; [eassumption|].
    apply IH; eauto.
Qed.

Lemma memory_iter_flat_map {A B} (step : B -> runtime_state -> runtime_state -> Prop)
  (events : A -> list B) xs before after :
  Iter.iter_semantics step (flat_map events xs) before after <->
  Iter.iter_semantics (fun x => Iter.iter_semantics step (events x)) xs before after.
Proof.
  revert before after; induction xs as [|x xs IH]; intros before after; cbn; split; intro RUN.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; constructor.
  - apply memory_iter_append in RUN as [middle [HEAD TAIL]].
    econstructor; [exact HEAD|apply IH; exact TAIL].
  - inversion RUN; subst; apply memory_iter_append; eexists; split; [eassumption|apply IH; eassumption].
Qed.

Scheme trace_stmt_ind := Induction for L.stmt Sort Prop
with trace_list_ind := Induction for L.stmt_list Sort Prop.
Combined Scheme trace_stmt_list_ind from trace_stmt_ind, trace_list_ind.

Theorem memory_loop_trace_contracts :
  (forall st env before after, L.loop_semantics st env before after <->
    Iter.iter_semantics memory_event_step (memory_loop_trace st env) before after) /\
  (forall sts env before after, L.loop_semantics (L.Seq sts) env before after <->
    Iter.iter_semantics memory_event_step (memory_loop_list_trace sts env) before after).
Proof.
  apply trace_stmt_list_ind.
  - intros lower upper body IH env before after; cbn; rewrite memory_iter_flat_map.
    split; intro RUN.
    + inversion RUN; subst; eapply Iter.iter_semantics_map; [|eassumption].
      intros; apply IH; assumption.
    + apply L.LLoop; eapply Iter.iter_semantics_map; [|exact RUN].
      intros; apply IH; assumption.
  - intros instruction arguments env before after; cbn; split; intro RUN.
    + inversion RUN; subst; econstructor; [unfold memory_event_step; cbn; eauto|constructor].
    + inversion RUN; subst.
      match goal with NIL : Iter.iter_semantics _ [] _ _ |- _ => inversion NIL; subst end.
      match goal with EVENT : memory_event_step _ _ _ |- _ =>
        destruct EVENT as [writes [reads STEP]] end.
      eapply L.LInstr; exact STEP.
  - intros sts IH; exact IH.
  - intros test body IH env before after; cbn.
    destruct (L.eval_test env test) eqn:TEST; split; intro RUN.
    + inversion RUN; subst; [apply IH; assumption|congruence].
    + apply L.LGuardTrue; [apply IH; exact RUN|exact TEST].
    + inversion RUN; subst; [congruence|constructor].
    + inversion RUN; subst; apply L.LGuardFalse; exact TEST.
  - intros env before after; cbn; split; intro RUN; inversion RUN; subst; constructor.
  - intros st IH sts REST env before after; cbn; rewrite memory_iter_append.
    split; intro RUN.
    + inversion RUN; subst; eexists; split; [apply IH|apply REST]; eassumption.
    + destruct RUN as [middle [FIRST SECOND]]; eapply L.LSeq;
        [apply IH; exact FIRST|apply REST; exact SECOND].
Qed.

Theorem memory_loop_trace_correct st env before after :
  L.loop_semantics st env before after <->
  Iter.iter_semantics memory_event_step (memory_loop_trace st env) before after.
Proof. apply memory_loop_trace_contracts. Qed.

Print Assumptions memory_loop_trace_correct.

Lemma memory_map_flat_map {A B C} (f : B -> C) (g : A -> list B) xs :
  map f (flat_map g xs) = flat_map (fun x => map f (g x)) xs.
Proof. induction xs; cbn; [reflexivity|rewrite map_app, IHxs; reflexivity]. Qed.
Lemma memory_guarded_list {A B} (keep : A -> bool) (f : A -> B) xs :
  flat_map (fun x => if keep x then [f x] else []) xs = map f (filter keep xs).
Proof. induction xs; cbn; [reflexivity|destruct (keep a); cbn; rewrite IHxs; reflexivity]. Qed.

Lemma memory_trace_points events (emit : memory_loop_event -> GuardMemoryIRs.PolyLang.InstrPoint) :
  (forall event before after, In event events ->
    (memory_event_step event before after <->
     GuardMemoryIRs.PolyLang.instr_point_sema (emit event) before after)) ->
  forall before after, Iter.iter_semantics memory_event_step events before after <->
    GuardMemoryIRs.PolyLang.instr_point_list_semantics (map emit events) before after.
Proof.
  induction events as [|event events IH]; intros CORRECT before after; cbn; split; intro RUN.
  - inversion RUN; subst; constructor; reflexivity.
  - inversion RUN; subst; unfold GuardMemoryInstr.State.eq in *; subst; constructor.
  - inversion RUN; subst; econstructor.
    + apply CORRECT; [left; reflexivity|eassumption].
    + apply IH; [intros; apply CORRECT; right; assumption|eassumption].
  - inversion RUN; subst; econstructor.
    + apply CORRECT; [left; reflexivity|eassumption].
    + apply IH; [intros; apply CORRECT; right; assumption|eassumption].
Qed.
