From Stdlib Require Import List Bool ZArith Lia Sorting.Sorted Sorting.Permutation Sorting.SetoidList.
From polcert.lib Require Import Misc Linalg LinalgExt ListExt ImpureAlarmConfig.
From polcert.src Require Import Base PolyBase PointWitness ExtractorFrontend PrepareCodegen SelectionSort.
From polcert.polygen Require Import PolIRs Result.
From Vpl Require Import Impure.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Reuses the established source trace construction with arbitrary POLIRS
    instructions and state. These witnesses are proofs, not runtime instrumentation. *)
Module PolCertSourceTraceFor (IRs : POLIRS).
Module L := IRs.Loop.
Module PL := IRs.PolyLang.
Module Iter := IRs.Instr.IterSem.

(** Finite traces are proof witnesses, not part of the extracted compiler. *)
Record memory_loop_event := MemoryLoopEvent {
  event_instruction : IRs.Instr.t;
  event_environment : list Z;
  event_arguments : list Z
}.
Definition memory_event_step event before after :=
  exists writes reads, IRs.Instr.instr_semantics
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

Lemma memory_iter_append {A} (step : A -> IRs.State.t -> IRs.State.t -> Prop) first :
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

Lemma memory_iter_flat_map {A B} (step : B -> IRs.State.t -> IRs.State.t -> Prop)
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

(** Distinct source sites may execute identical instructions. A static site
    number belongs to the proof witness, not to the runtime instruction. *)
Record indexed_memory_event := IndexedMemoryEvent {
  indexed_event_site : nat;
  indexed_event_payload : memory_loop_event
}.
Fixpoint memory_leaf_count (st : L.stmt) : nat :=
  match st with
  | L.Instr _ _ => 1
  | L.Seq sts => memory_list_leaf_count sts
  | L.Guard _ body | L.Loop _ _ body => memory_leaf_count body
  end
with memory_list_leaf_count (sts : L.stmt_list) : nat :=
  match sts with L.SNil => 0 | L.SCons st rest => (memory_leaf_count st + memory_list_leaf_count rest)%nat end.
Fixpoint indexed_memory_loop_trace (base : nat) (st : L.stmt) (env : list Z) : list indexed_memory_event :=
  match st with
  | L.Instr instruction arguments =>
      [IndexedMemoryEvent base (MemoryLoopEvent instruction env (map (L.eval_expr env) arguments))]
  | L.Seq sts => indexed_memory_list_trace base sts env
  | L.Guard test body => if L.eval_test env test then indexed_memory_loop_trace base body env else []
  | L.Loop lower upper body => flat_map (fun x => indexed_memory_loop_trace base body (x::env))
      (Zrange (L.eval_expr env lower) (L.eval_expr env upper))
  end
with indexed_memory_list_trace (base : nat) (sts : L.stmt_list) (env : list Z) : list indexed_memory_event :=
  match sts with
  | L.SNil => []
  | L.SCons st rest => indexed_memory_loop_trace base st env ++
      indexed_memory_list_trace (base + memory_leaf_count st)%nat rest env
  end.
Definition indexed_memory_event_step event := memory_event_step (indexed_event_payload event).

Theorem indexed_memory_trace_erasure_contracts :
  (forall st base env, map indexed_event_payload (indexed_memory_loop_trace base st env) = memory_loop_trace st env) /\
  (forall sts base env, map indexed_event_payload (indexed_memory_list_trace base sts env) = memory_loop_list_trace sts env).
Proof.
  apply trace_stmt_list_ind.
  - intros lower upper body IH base env; cbn; rewrite memory_map_flat_map.
    apply flat_map_ext; intro x; apply IH.
  - reflexivity.
  - intros sts IH; exact IH.
  - intros test body IH base env; cbn; destruct (L.eval_test env test); [apply IH|reflexivity].
  - reflexivity.
  - intros st IH sts REST base env; cbn; rewrite map_app,IH,REST; reflexivity.
Qed.
Lemma indexed_memory_trace_erasure st base env :
  map indexed_event_payload (indexed_memory_loop_trace base st env) = memory_loop_trace st env.
Proof. apply indexed_memory_trace_erasure_contracts. Qed.

Lemma memory_iter_map_equivalence {A B} (f : A -> B)
  (step : A -> IRs.State.t -> IRs.State.t -> Prop) (mapped : B -> IRs.State.t -> IRs.State.t -> Prop) xs :
  (forall x first final, step x first final <-> mapped (f x) first final) ->
  forall before after, Iter.iter_semantics step xs before after <-> Iter.iter_semantics mapped (map f xs) before after.
Proof.
  intro STEP; induction xs; intros before after; cbn; split; intro RUN; inversion RUN; subst; constructor ||
    (econstructor; [apply STEP; eassumption|apply IHxs; eassumption]).
Qed.
Theorem indexed_memory_loop_execution st base env before after :
  L.loop_semantics st env before after <->
  Iter.iter_semantics indexed_memory_event_step (indexed_memory_loop_trace base st env) before after.
Proof.
  rewrite memory_loop_trace_correct,<-(@indexed_memory_trace_erasure st base env).
  symmetry; apply memory_iter_map_equivalence; intros; reflexivity.
Qed.

Theorem indexed_memory_site_bounds_contracts :
  (forall st base env event, In event (indexed_memory_loop_trace base st env) ->
    (base <= indexed_event_site event < base + memory_leaf_count st)%nat) /\
  (forall sts base env event, In event (indexed_memory_list_trace base sts env) ->
    (base <= indexed_event_site event < base + memory_list_leaf_count sts)%nat).
Proof.
  apply trace_stmt_list_ind.
  - intros lower upper body IH base env event MEMBER; cbn in MEMBER |- *.
    apply in_flat_map in MEMBER as [x [_ MEMBER]]; eapply IH; exact MEMBER.
  - intros instruction arguments base env event MEMBER; cbn in MEMBER |- *.
    destruct MEMBER as [<-|ABSENT]; [cbn; lia|contradiction].
  - intros sts IH; exact IH.
  - intros test body IH base env event MEMBER; cbn in MEMBER |- *.
    destruct (L.eval_test env test); [eapply IH; exact MEMBER|contradiction].
  - intros base env event MEMBER; contradiction.
  - intros st IH sts REST base env event MEMBER; cbn in MEMBER |- *.
    apply in_app_or in MEMBER as [MEMBER|MEMBER].
    + pose proof (IH base env event MEMBER); lia.
    + pose proof (REST (base+memory_leaf_count st)%nat env event MEMBER); lia.
Qed.
Print Assumptions indexed_memory_loop_execution.
Print Assumptions indexed_memory_site_bounds_contracts.

Lemma indexed_memory_trace_points_forward events (emit : indexed_memory_event -> PL.InstrPoint) :
  (forall event before after, In event events ->
    indexed_memory_event_step event before after -> PL.instr_point_sema (emit event) before after) ->
  forall before after, Iter.iter_semantics indexed_memory_event_step events before after ->
    PL.instr_point_list_semantics (map emit events) before after.
Proof.
  induction events as [|event events IH]; intros CORRECT before after RUN; cbn.
  - inversion RUN; subst; constructor; apply IRs.State.eq_refl.
  - inversion RUN; subst; econstructor.
    + apply CORRECT; [left; reflexivity|eassumption].
    + eapply IH.
      * intros tail_event first final MEMBER STEP.
        apply CORRECT; [right; exact MEMBER|exact STEP].
      * eassumption.
Qed.
Print Assumptions indexed_memory_trace_points_forward.
End PolCertSourceTraceFor.
