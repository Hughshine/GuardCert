From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Misc.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryPolyhedral
  GuardMemoryLoops GuardMemoryLoopTrace.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

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
  (step : A -> runtime_state -> runtime_state -> Prop) (mapped : B -> runtime_state -> runtime_state -> Prop) xs :
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
