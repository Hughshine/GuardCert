(** Source-licensed header checks for an actual sequence of full-word stores.
    Reads in later RHS expressions stay after earlier source stores. *)
From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightTempFrame ClightFiniteRegion ClightStraightLine.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite
  ClightReadonlyLoadedTreeSynthesis ClightConditionComposition ClightWordArithmeticTransport
  ClightWordCoordinateRename ClightDirectWordObservation ClightRenamedWordObservation
  ClightAffineJointObservation ClightObservedHeaderPrefix ClightStorePermissions ClightReadonlyCellSwap.
Import ListNotations.
Set Implicit Arguments.

Record word_store_site := WordStoreSite {
  wss_pointer : ident;
  wss_index : expr;
  wss_rhs : expr
}.
Definition word_store_site_code site :=
  direct_word_store (wss_pointer site) (wss_index site) (wss_rhs site).
Definition word_store_site_frame rename site current checked :=
  renamed_word_frame rename (wss_pointer site) (wss_index site) current checked.
Definition word_store_site_domain fe rename observers entry site :=
  renamed_word_point_domain fe rename (wss_pointer site) (wss_index site) (wss_rhs site) observers entry.
Definition word_store_site_preserved fe rename observers entry site :=
  renamed_word_point_preserved fe rename (wss_pointer site) (wss_index site) (wss_rhs site) observers entry.
Definition word_store_site_flag rename observers entry site :=
  renamed_word_point_flag rename (wss_pointer site) (wss_index site) observers entry.
Definition word_store_sequence_flag rename sites observers entry :=
  forallb (word_store_site_flag rename observers entry) sites.
Fixpoint word_store_sequence_tree rename sites observers := match sites with
| [] => Decision true
| site :: rest => decision_bind
    (renamed_word_observer_tree rename (wss_pointer site) (wss_index site) observers)
    (word_store_sequence_tree rename rest observers) (Decision false)
end.

Definition word_store_sequence_domain fe rename sites observers entry :=
  Forall (word_observer_receipt (entry_ge entry) (entry_env entry)
    (entry_temps entry) (entry_memory entry)) observers /\
  exists current memory after final,
    Forall (fun site => word_store_site_frame rename site current (entry_temps entry)) sites /\
    memory_accesses_back (entry_memory entry) memory /\
    tail_execution fe (entry_ge entry) (entry_env entry) (map word_store_site_code sites)
      current memory after final.
Definition word_store_sequence_preserved fe rename sites observers entry :=
  forall current memory after final,
    Forall (fun site => word_store_site_frame rename site current (entry_temps entry)) sites ->
    header_observations_match (map word_observer_snapshot observers) memory ->
    tail_execution fe (entry_ge entry) (entry_env entry) (map word_store_site_code sites)
      current memory after final ->
    header_observations_match (map word_observer_snapshot observers) final.

Lemma word_store_site_permissions fe ge locals site current memory after final :
  exec_stmt fe ge locals current memory (word_store_site_code site) E0 after final Out_normal ->
  after = current /\ memory_accesses_back memory final.
Proof.
  intro RUN; destruct (direct_word_store_receipt RUN) as [block [offset [value [ADDRESS [STORE [_ [SAME _]]]]]]].
  split; [exact SAME|].
  destruct (@storev_word_facts _ _ _ _ _ STORE) as [ACCESS RAW].
  eapply store_memory_accesses_back; exact RAW.
Qed.

Theorem word_store_sequence_permissions sites fe ge locals current memory after final :
  tail_execution fe ge locals (map word_store_site_code sites) current memory after final ->
  after = current /\ memory_accesses_back memory final.
Proof.
  revert current memory after final; induction sites as [|site rest IH]; intros current memory after final RUN;
    cbn [map] in RUN; inversion RUN; subst.
  - split; [reflexivity|apply memory_accesses_back_refl].
  - match goal with HEAD : exec_stmt _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct (word_store_site_permissions HEAD) as [SAME BACK]; subst end.
    match goal with TAIL : tail_execution _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ _ _ TAIL) as [SAME REST] end.
    split; [exact SAME|eapply memory_accesses_back_trans; eassumption].
Qed.

(** The receipt of every later store is obtained in its real intermediate
    memory. Only permission is transported backwards, never an RHS value. *)
Theorem word_store_sequence_point_domains sites fe rename observers entry current memory after final :
  Forall (word_observer_receipt (entry_ge entry) (entry_env entry)
    (entry_temps entry) (entry_memory entry)) observers ->
  Forall (fun site => word_store_site_frame rename site current (entry_temps entry)) sites ->
  memory_accesses_back (entry_memory entry) memory ->
  tail_execution fe (entry_ge entry) (entry_env entry) (map word_store_site_code sites)
    current memory after final ->
  Forall (word_store_site_domain fe rename observers entry) sites.
Proof.
  revert current memory after final; induction sites as [|site rest IH];
    intros current memory after final READS FRAMES BACK RUN; [constructor|].
  inversion FRAMES as [|head tail FRAME REST]; subst.
  cbn [map] in RUN; inversion RUN; subst; constructor.
  - split; [exact READS|].
    match goal with HEAD : exec_stmt _ _ _ _ _ _ _ ?next ?middle _ |- _ =>
      exists current, memory, next, middle;
      split; [exact FRAME|split; [exact BACK|exact HEAD]] end.
  - match goal with HEAD : exec_stmt _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct (word_store_site_permissions HEAD) as [SAME STEP]; subst end.
    eapply IH; [exact READS|exact REST|eapply memory_accesses_back_trans; eassumption|eassumption].
Qed.

Theorem word_store_sequence_domain_from_body fe rename sites observers entry body current memory after final :
  flatten_region body = map word_store_site_code sites ->
  Forall (word_observer_receipt (entry_ge entry) (entry_env entry)
    (entry_temps entry) (entry_memory entry)) observers ->
  Forall (fun site => word_store_site_frame rename site current (entry_temps entry)) sites ->
  memory_accesses_back (entry_memory entry) memory ->
  exec_stmt fe (entry_ge entry) (entry_env entry) current memory body E0 after final Out_normal ->
  word_store_sequence_domain fe rename sites observers entry.
Proof.
  intros BODY READS FRAMES BACK RUN; split; [exact READS|].
  exists current, memory, after, final; split; [exact FRAMES|split; [exact BACK|]].
  apply flatten_region_execution in RUN; rewrite BODY in RUN; exact RUN.
Qed.

Theorem word_store_sequence_tree_execution fe rename sites observers entry :
  Forall (fun site => word_arithmetic (wss_index site)) sites ->
  word_store_sequence_domain fe rename sites observers entry ->
  decision_run entry (word_store_sequence_tree rename sites observers)
    (word_store_sequence_flag rename sites observers entry).
Proof.
  intros WORDS [READS [current [memory [after [final [FRAMES [BACK SOURCE]]]]]]].
  pose proof (@word_store_sequence_point_domains sites fe rename observers entry
    current memory after final READS FRAMES BACK SOURCE) as DOMAINS.
  clear SOURCE FRAMES BACK; induction WORDS as [|site rest WORD WORDS IH];
    cbn [word_store_sequence_tree word_store_sequence_flag forallb]; [constructor|].
  inversion DOMAINS as [|head tail DOMAIN REST]; subst.
  pose proof (@renamed_word_point_execution fe rename (wss_pointer site) (wss_index site)
    (wss_rhs site) observers entry WORD DOMAIN) as HEAD.
  unfold word_store_site_flag; destruct (renamed_word_point_flag rename (wss_pointer site) (wss_index site) observers entry).
  - eapply decision_bind_run; [exact HEAD|apply IH; exact REST].
  - eapply decision_bind_run; [exact HEAD|constructor].
Qed.

Theorem word_store_sequence_sound fe rename sites observers entry :
  Forall (fun site => word_arithmetic (wss_index site)) sites ->
  word_store_sequence_domain fe rename sites observers entry ->
  word_store_sequence_flag rename sites observers entry = true ->
  word_store_sequence_preserved fe rename sites observers entry.
Proof.
  intros WORDS [READS [source_temps [source_memory [source_after [source_final [FRAMES [BACK SOURCE]]]]]]] ACCEPT.
  pose proof (@word_store_sequence_point_domains sites fe rename observers entry
    source_temps source_memory source_after source_final READS FRAMES BACK SOURCE) as DOMAINS.
  assert (PRESERVE : Forall (word_store_site_preserved fe rename observers entry) sites).
  { apply Forall_forall; intros site MEMBER.
    eapply renamed_word_point_sound.
    - rewrite Forall_forall in WORDS; apply WORDS; exact MEMBER.
    - rewrite Forall_forall in DOMAINS; apply DOMAINS; exact MEMBER.
    - unfold word_store_sequence_flag in ACCEPT; rewrite forallb_forall in ACCEPT; apply ACCEPT; exact MEMBER. }
  clear WORDS DOMAINS SOURCE ACCEPT FRAMES BACK; unfold word_store_sequence_preserved.
  induction PRESERVE as [|site rest HEAD PRESERVE IH]; intros current memory after final FRAMES READ RUN;
    cbn [map] in RUN; inversion RUN; subst; [exact READ|].
  inversion FRAMES as [|head tail FRAME REST]; subst.
  match goal with STEP : exec_stmt _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof (HEAD _ _ _ _ FRAME READ STEP) as NEXT;
    destruct (word_store_site_permissions STEP) as [SAME _]; subst end.
  eapply IH; eassumption.
Qed.

Definition word_store_sequence_condition fe O (observe : fragment_observation -> O -> Prop)
    rename sites observers (WORDS : Forall (fun site => word_arithmetic (wss_index site)) sites) :
  readonly_condition (readonly_clight_host fe observe)
    (word_store_sequence_domain fe rename sites observers)
    (word_store_sequence_preserved fe rename sites observers)
    (word_store_sequence_tree rename sites observers).
Proof.
  constructor.
  - intros entry DOMAIN; eapply readonly_decision_run_safe;
      exact (@word_store_sequence_tree_execution fe rename sites observers entry WORDS DOMAIN).
  - intros entry DOMAIN; exists (word_store_sequence_flag rename sites observers entry), entry;
      split; [exact (@word_store_sequence_tree_execution fe rename sites observers entry WORDS DOMAIN)|reflexivity].
  - intros entry answer checked DOMAIN [RUN SAME]; subst checked; split; [reflexivity|].
    intro ACCEPT; subst answer.
    pose proof (readonly_decision_determinate RUN (@word_store_sequence_tree_execution fe rename sites observers entry WORDS DOMAIN)) as FLAG.
    eapply word_store_sequence_sound; [exact WORDS|exact DOMAIN|symmetry; exact FLAG].
Defined.

Definition word_store_sequence_check_code rename sites observers flag :=
  tree_statement (word_store_sequence_tree rename sites observers)
    (Sset flag (Econst_int Int.one type_int32s)) (Sset flag (Econst_int Int.zero type_int32s)).
Theorem word_store_sequence_check_execution fe rename sites observers entry flag :
  Forall (fun site => word_arithmetic (wss_index site)) sites ->
  word_store_sequence_domain fe rename sites observers entry ->
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (word_store_sequence_check_code rename sites observers flag) E0
    (PTree.set flag (Vint (if word_store_sequence_flag rename sites observers entry then Int.one else Int.zero))
      (entry_temps entry)) (entry_memory entry) Out_normal.
Proof.
  intros WORDS DOMAIN; destruct entry as [ge locals temps memory].
  unfold word_store_sequence_check_code; eapply decision_fragment_run.
  - eapply word_store_sequence_tree_execution; [exact WORDS|exact DOMAIN].
  - cbn [entry_ge entry_env entry_temps entry_memory].
    destruct (word_store_sequence_flag rename sites observers (Entry ge locals temps memory)); constructor; constructor.
Qed.

Print Assumptions word_store_site_permissions.
Print Assumptions word_store_sequence_permissions.
Print Assumptions word_store_sequence_point_domains.
Print Assumptions word_store_sequence_domain_from_body.
Print Assumptions word_store_sequence_tree_execution.
Print Assumptions word_store_sequence_sound.
Print Assumptions word_store_sequence_condition.
Print Assumptions word_store_sequence_check_execution.
