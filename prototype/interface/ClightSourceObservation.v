From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightSameAddress ClightTempFrame ClightRegionProgress
  ClightTempFootprint ClightLoopSyntax ClightPrivateRegion ClightProjectedExecution CompCertMemoryEquivalence.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightPrivateScan.
Import ListNotations.
Set Implicit Arguments.

(** A receipt is derived from ordinary source execution. It contains no
    assumption about aliasing and does not insert a speculative load. *)
Definition observed_pointer_domain pointers (entry : clight_entry) :=
  forall identifier, In identifier pointers -> exists block offset,
    (entry_temps entry) ! identifier = Some (Vptr block offset) /\
    Mem.valid_pointer (entry_memory entry) block (Ptrofs.unsigned offset) = true.

Lemma observed_pointer_domain_frame pointers original current :
  entry_memory current = entry_memory original ->
  temp_agree pointers (entry_temps original) (entry_temps current) ->
  observed_pointer_domain pointers original -> observed_pointer_domain pointers current.
Proof.
  intros MEMORY FRAME OBSERVED identifier MEMBER.
  destruct (OBSERVED identifier MEMBER) as [block [offset [POINTER VALID]]].
  exists block,offset; rewrite MEMORY,(FRAME identifier MEMBER); auto.
Qed.

Fixpoint source_load_prefix (loads : list (ident * ident)) :=
  match loads with
  | [] => Sskip
  | (target,pointer)::rest => Ssequence (Sset target (signed_load pointer)) (source_load_prefix rest)
  end.
Definition source_load_targets (loads : list (ident * ident)) := map fst loads.
Definition source_load_pointers (loads : list (ident * ident)) := map snd loads.

Definition source_observations_check pointers loads :=
  forallb (fun identifier => existsb (Pos.eqb identifier) (source_load_pointers loads)) pointers &&
  forallb (fun identifier => negb (existsb (Pos.eqb identifier) (source_load_pointers loads)))
    (source_load_targets loads).
Lemma source_observations_check_sound pointers loads :
  source_observations_check pointers loads = true ->
  (forall identifier, In identifier pointers -> In identifier (source_load_pointers loads)) /\
  (forall identifier, In identifier (source_load_targets loads) -> ~ In identifier (source_load_pointers loads)).
Proof.
  unfold source_observations_check; rewrite andb_true_iff; intros [COVER FRESH]; split.
  - intros identifier MEMBER; apply forallb_forall with (x:=identifier) in COVER; [|exact MEMBER].
    apply existsb_exists in COVER as [other [IN SAME]]; apply Pos.eqb_eq in SAME; subst other; exact IN.
  - intros identifier MEMBER BAD; apply forallb_forall with (x:=identifier) in FRESH; [|exact MEMBER].
    apply negb_true_iff in FRESH; assert (FOUND : existsb (Pos.eqb identifier) (source_load_pointers loads) = true).
    { apply existsb_exists; exists identifier; split; [exact BAD|apply Pos.eqb_refl]. } congruence.
Qed.

Lemma source_load_prefix_supported loads : private_scan_statement (source_load_prefix loads).
Proof. induction loads as [|[target pointer] rest IH]; cbn; auto using scan_skip,scan_set,scan_sequence. Qed.
Lemma source_load_prefix_writes loads : writes_only (source_load_targets loads) (source_load_prefix loads).
Proof.
  induction loads as [|[target pointer] rest IH]; cbn [source_load_prefix source_load_targets map fst].
  - constructor.
  - constructor; [constructor; cbn; auto|].
    eapply writes_only_weaken; [intros identifier MEMBER; right; exact MEMBER|exact IH].
Qed.

(** Every completed prefix records the capability at its final state. Outputs
    must preserve pointer bindings; duplicate outputs and pointers are allowed. *)
Theorem source_load_prefix_observations loads fe ge locals temps memory trace after final outcome :
  (forall identifier, In identifier (source_load_targets loads) -> ~ In identifier (source_load_pointers loads)) ->
  exec_stmt fe ge locals temps memory (source_load_prefix loads) trace after final outcome ->
  trace = E0 /\ final = memory /\ outcome = Out_normal /\
  observed_pointer_domain (source_load_pointers loads) (Entry ge locals after final).
Proof.
  revert temps trace after final outcome; induction loads as [|[target pointer] rest IH];
    intros temps trace after final outcome FRESH RUN.
  - inversion RUN; subst; repeat split; intros identifier MEMBER; contradiction.
  - cbn [source_load_prefix] in RUN; inversion RUN; subst.
    2: match goal with SET : exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion SET; subst; contradiction end.
    match goal with SET : exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion SET; subst end.
    match goal with LOAD : eval_expr _ _ _ _ (signed_load _) _ |- _ =>
      apply signed_load_inv in LOAD as [block [offset [POINTER READ]]] end.
    assert (REST_FRESH : forall identifier, In identifier (source_load_targets rest) ->
      ~ In identifier (source_load_pointers rest)).
    { intros identifier MEMBER BAD; apply (FRESH identifier).
      - cbn [source_load_targets map fst]; right; exact MEMBER.
      - cbn [source_load_pointers map snd]; right; exact BAD. }
    match goal with TAIL : exec_stmt _ _ _ _ _ (source_load_prefix rest) _ _ _ _ |- _ =>
      pose proof TAIL as TAIL_RUN;
      destruct (IH _ _ _ _ _ REST_FRESH TAIL)
        as [TRACE [MEMORY [OUTCOME OBSERVED]]]; subst end.
    repeat split; try reflexivity.
    intros identifier MEMBER; cbn [source_load_pointers map snd] in MEMBER; destruct MEMBER as [SAME|MEMBER].
    + subst identifier; exists block,offset; split; [|eapply loaded_address_valid; exact READ].
      assert (NOT_TARGET : pointer <> target).
      { intro SAME; subst target; apply (FRESH pointer).
        - cbn [source_load_targets map fst]; left; reflexivity.
        - cbn [source_load_pointers map snd]; left; reflexivity. }
      assert (NOT_REST : ~ In pointer (source_load_targets rest)).
      { intro BAD; apply (FRESH pointer).
        - cbn [source_load_targets map fst]; right; exact BAD.
        - cbn [source_load_pointers map snd]; left; reflexivity. }
      erewrite writes_only_frame; [|exact TAIL_RUN|apply source_load_prefix_writes|].
      * rewrite PTree.gso by exact NOT_TARGET; exact POINTER.
      * exact NOT_REST.
    + apply OBSERVED; exact MEMBER.
Qed.

(** The language host localizes a domain at the point after a real source
    prefix. The domain producer sees both source executions; the prefix is
    retained exactly, and the body consumer supplies conditional preservation.
    This finite-region theorem does not cover an arbitrary divergent prefix. *)
Theorem source_prefix_region_contract live prefix source target writes (domain : clight_entry -> Prop) :
  private_scan_statement prefix ->
  writes_only writes (Ssequence prefix source) ->
  (forall temps p locals entry memory middle after final,
    exec_stmt (adapter_entry temps) (globalenv p) locals entry memory prefix E0 middle memory Out_normal ->
    exec_stmt (adapter_entry temps) (globalenv p) locals middle memory source E0 after final Out_normal ->
    domain (Entry (globalenv p) locals middle memory)) ->
  (forall temps p locals entry memory after final,
    statement_scope live source -> domain (Entry (globalenv p) locals entry memory) ->
    exec_stmt (adapter_entry temps) (globalenv p) locals entry memory source E0 after final Out_normal ->
    exists exit result,
      exec_stmt (adapter_entry temps) (globalenv p) locals entry memory target E0 exit result Out_normal /\
      temp_agree live after exit /\ memory_equivalent final result) ->
  PrivateRegion.projected_region_contract live (Ssequence prefix source) (Ssequence prefix target).
Proof.
  intros PREFIX WRITES DOMAIN BODY temps p locals entry current memory after final SCOPE AGREE SOURCE fn continuation.
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv p) locals entry memory
    (Ssequence prefix source) E0 after final Out_normal SOURCE live current writes WRITES SCOPE AGREE)
    as [middle [TRANSPORTED PUBLIC]].
  inversion TRANSPORTED; subst.
  2: contradiction.
  match goal with RUN : exec_stmt _ _ _ _ _ prefix _ _ _ _ |- _ =>
    destruct (@private_scan_completed_shape _ _ _ _ _ _ _ _ _ _ RUN PREFIX) as [TRACE [MEMORY _]];
    subst; rename RUN into PREFIX_RUN end.
  match goal with EMPTY : E0 ** ?tail = E0 |- _ => cbn in EMPTY; subst tail end.
  match goal with RUN : exec_stmt _ _ _ _ _ source _ _ _ _ |- _ => rename RUN into BODY_RUN end.
  assert (BODY_SCOPE : statement_scope live source).
  { intros identifier MEMBER; apply SCOPE; cbn [statement_temps]; apply in_or_app; right; exact MEMBER. }
  destruct (BODY _ _ _ _ _ _ _ BODY_SCOPE (DOMAIN _ _ _ _ _ _ _ _ PREFIX_RUN BODY_RUN) BODY_RUN)
    as [exit [result [TARGET [EXIT MEMORY]]]].
  assert (COMBINED : exec_stmt (adapter_entry temps) (globalenv p) locals current memory
    (Ssequence prefix target) E0 exit result Out_normal).
  { eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); eassumption. }
  destruct (exec_stmt_steps (adapter_entry temps) p _ _ _ _ _ _ _ _ COMBINED fn continuation) as [finish [STEPS FINISH]].
  inversion FINISH; subst finish; exists exit,result; split; [exact STEPS|split; [|exact MEMORY]].
  eapply temp_agree_trans; [exact PUBLIC|exact EXIT].
Qed.

Print Assumptions observed_pointer_domain_frame.
Print Assumptions source_observations_check_sound.
Print Assumptions source_load_prefix_observations.
Print Assumptions source_prefix_region_contract.
