From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Misc.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryLoopTrace GuardMemoryIndexedTrace
  GuardMemoryExtractorTrace.
Import ListNotations.
Set Implicit Arguments.

Definition memory_event_key event :=
  (indexed_event_site event,event_environment (indexed_event_payload event)).

Lemma memory_nodup_map_reflect {A B C} (f : A -> B) (key : A -> C) xs :
  (forall first second, f first = f second -> key first = key second) ->
  NoDup (map key xs) -> NoDup (map f xs).
Proof.
  intros REFLECT; induction xs as [|first xs IH]; cbn; intro UNIQUE; inversion UNIQUE; subst; constructor.
  - intro MEMBER; apply in_map_iff in MEMBER as [second [SAME MEMBER]].
    match goal with ABSENT : ~ In (key first) (map key xs) |- _ =>
      apply ABSENT; apply in_map_iff; exists second; split; [apply REFLECT; exact SAME|exact MEMBER] end.
  - apply IH; assumption.
Qed.

Lemma memory_nodup_flat_map {A B} (f : A -> list B) xs :
  NoDup xs -> (forall x, NoDup (f x)) ->
  (forall x y point, In point (f x) -> In point (f y) -> x = y) -> NoDup (flat_map f xs).
Proof.
  intros UNIQUE EACH DISJOINT; induction UNIQUE; cbn; [constructor|].
  apply NoDup_app; [apply EACH|exact IHUNIQUE|].
  intros point FIRST SECOND; apply in_flat_map in SECOND as [other [MEMBER SECOND]].
  assert (SAME : x = other) by (eapply DISJOINT; eassumption); subst other; contradiction.
Qed.
Lemma memory_nodup_zrange lower upper : NoDup (Zrange lower upper).
Proof.
  unfold Zrange; eapply memory_nodup_map_reflect with (key := fun n => n).
  - intros first second SAME; cbn in SAME; lia.
  - rewrite map_id; apply n_range_NoDup.
Qed.
Lemma memory_environment_suffix_distinct (first second : Z) (env prefix other : list Z) :
  prefix++first::env = other++second::env -> first = second.
Proof.
  intro SAME; apply (f_equal (@rev Z)) in SAME; rewrite !rev_app_distr in SAME; cbn in SAME.
  rewrite <- !app_assoc in SAME; apply app_inv_head in SAME; inversion SAME; reflexivity.
Qed.

Theorem indexed_memory_event_keys_unique :
  (forall st base env, NoDup (map memory_event_key (indexed_memory_loop_trace base st env))) /\
  (forall sts base env, NoDup (map memory_event_key (indexed_memory_list_trace base sts env))).
Proof.
  apply trace_stmt_list_ind.
  - intros lower upper body IH base env; cbn; rewrite memory_map_flat_map.
    apply memory_nodup_flat_map; [apply memory_nodup_zrange|intro index; apply IH|].
    intros first second key FIRST SECOND.
    apply in_map_iff in FIRST as [event [EVENT FIRST]].
    apply in_map_iff in SECOND as [other [OTHER SECOND]].
    assert (ENVIRONMENTS : event_environment (indexed_event_payload event) =
      event_environment (indexed_event_payload other)).
    { apply (f_equal snd) in EVENT,OTHER; cbn in EVENT,OTHER; congruence. }
    destruct (proj1 indexed_memory_environment_extension body base (first::env) event FIRST) as [prefix ENV].
    destruct (proj1 indexed_memory_environment_extension body base (second::env) other SECOND) as [suffix OTHER_ENV].
    rewrite ENV,OTHER_ENV in ENVIRONMENTS; eapply memory_environment_suffix_distinct; exact ENVIRONMENTS.
  - intros instruction arguments base env; cbn; constructor; [cbn; tauto|constructor].
  - intros sts IH; exact IH.
  - intros test body IH base env; cbn; destruct (L.eval_test env test); [apply IH|constructor].
  - intros base env; constructor.
  - intros st IH sts REST base env; cbn; rewrite map_app; apply NoDup_app; [apply IH|apply REST|].
    intros key HEAD TAIL; apply in_map_iff in HEAD as [event [EVENT HEAD]].
    apply in_map_iff in TAIL as [other [OTHER TAIL]].
    assert (SITE : indexed_event_site event = indexed_event_site other).
    { apply (f_equal fst) in EVENT,OTHER; cbn in EVENT,OTHER; congruence. }
    pose proof (proj1 indexed_memory_site_bounds_contracts st base env event HEAD) as HEAD_BOUND.
    pose proof (proj2 indexed_memory_site_bounds_contracts sts (base+memory_leaf_count st)%nat env other TAIL) as TAIL_BOUND.
    lia.
Qed.

Theorem memory_extracted_trace_points_unique st instructions env :
  NoDup (map (memory_extracted_event_point instructions) (indexed_memory_loop_trace O st env)).
Proof.
  eapply memory_nodup_map_reflect with (key := memory_event_key); [|apply indexed_memory_event_keys_unique].
  intros first second SAME.
  pose proof (f_equal PL.ip_nth SAME) as SITE.
  pose proof (f_equal PL.ip_index SAME) as ENV.
  change (indexed_event_site first = indexed_event_site second) in SITE.
  change (rev (event_environment (indexed_event_payload first)) =
    rev (event_environment (indexed_event_payload second))) in ENV.
  apply (f_equal (@rev Z)) in ENV; rewrite !rev_involutive in ENV.
  unfold memory_event_key; rewrite SITE,ENV; reflexivity.
Qed.
Print Assumptions indexed_memory_event_keys_unique.
Print Assumptions memory_extracted_trace_points_unique.
