From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightGlobalScope ClightRegionProgress ClightTempFrame
  ClightTempFootprint ClightProjectedExecution ClightLoopSyntax.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleSourceTreeData
  GuardMemoryDoubleSourceTreeDecode GuardMemoryDoubleSourceTreeState GuardMemoryDoubleSourceTreeSyntax GuardMemoryDoubleSourceTreeEffects
  GuardMemoryDoubleTreeCaptureData GuardMemoryDoubleTreeCaptureReceipt GuardMemoryDoubleTreeCaptureSource
  GuardMemoryLongControl GuardMemoryLongRangeCapture.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint double_tree_initialize_caches (headers : list ident) (cache : ident -> ident) : statement := match headers with
  | []=>Sskip | header::rest=>Ssequence (Sset (cache header) (Econst_int Int.zero memory_signed_int_type))
      (double_tree_initialize_caches rest cache) end.
Fixpoint double_tree_initialized_temps (headers : list ident) (cache : ident -> ident) (temps : temp_env) : temp_env := match headers with
  | []=>temps | header::rest=>double_tree_initialized_temps rest cache (PTree.set (cache header) (Vint Int.zero) temps) end.
Definition double_tree_capture_prepare tree cache flag lower upper :=
  Ssequence (double_tree_initialize_caches (double_source_tree_parameters tree) cache)
    (Ssequence (memory_capture_flag flag true) (double_tree_capture_code tree cache flag lower upper)).
Lemma double_tree_initialize_execution headers cache fe ge locals memory : forall temps,
  exec_stmt fe ge locals temps memory (double_tree_initialize_caches headers cache) E0
    (double_tree_initialized_temps headers cache temps) memory Out_normal.
Proof.
  induction headers; intro temps; cbn [double_tree_initialize_caches double_tree_initialized_temps]; [constructor|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [constructor; constructor|apply IHheaders].
Qed.
Lemma double_tree_initialize_writes headers cache :
  writes_only (map cache headers) (double_tree_initialize_caches headers cache).
Proof.
  induction headers; cbn [double_tree_initialize_caches map]; [constructor|apply writes_sequence].
  - apply writes_set; left; reflexivity.
  - eapply writes_only_weaken; [intros key MEMBER; right; exact MEMBER|exact IHheaders].
Qed.
Lemma double_tree_prepare_writes tree cache flag lower upper :
  writes_only (double_tree_capture_private tree cache flag) (double_tree_capture_prepare tree cache flag lower upper).
Proof.
  unfold double_tree_capture_prepare; apply writes_sequence.
  - eapply writes_only_weaken; [|apply double_tree_initialize_writes].
    intros key MEMBER; unfold double_tree_capture_private; right.
    apply in_map_iff in MEMBER as [header [SAME HEADER]]; subst key.
    apply in_map; apply double_source_tree_parameter_membership; exact HEADER.
  - apply writes_sequence; [unfold memory_capture_flag; apply writes_set; left; reflexivity|apply double_tree_capture_writes].
Qed.

(** A decoded original gets a concrete preparation fragment. Static decoding
    closes the raw observer exclusions; the site supplies scope, ranges and
    private-identifier freshness. Fallback replay also preserves public exits. *)
Theorem checked_double_tree_capture_prepare p source tree fe ge locals temps memory after final live cache flag lower upper :
  checked_double_source_tree p source=Some tree -> preserving_globals (globalenv p) ge ->
  double_source_tree_scope tree locals -> locals_avoid (double_source_tree_headers tree) locals ->
  (forall header, In header (double_source_tree_headers tree) ->
    Int.min_signed<=lower header<=Int.max_signed /\ Int.min_signed<=upper header<=Int.max_signed) ->
  (forall header, In header (double_source_tree_headers tree) -> flag<>cache header) ->
  (forall key, In key (statement_temps source++live) -> ~ In key (double_tree_capture_private tree cache flag)) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists prepared accepted prepared_after,
    exec_stmt fe ge locals temps memory (double_tree_capture_prepare tree cache flag lower upper) E0 prepared memory Out_normal /\
    double_tree_flag_value prepared flag accepted /\ temp_agree live temps prepared /\
    exec_stmt fe ge locals prepared memory source E0 prepared_after final Out_normal /\ temp_agree live after prepared_after.
Proof.
  intros DECODE GLOBAL SCOPE LOCAL LIMITS FRESH PRIVATE RUN.
  destruct (@checked_double_source_tree_sound p source tree DECODE) as [SOURCE [CHECK [WRITES LAYOUT]]].
  assert (EXCLUSIONS : double_source_tree_header_exclusions tree (double_source_tree_headers tree)).
  { intros instruction header POINT MEMBER; unfold double_tree_write_global.
    apply (@double_source_tree_header_writes_check_sound tree); [exact WRITES|exact POINT|].
    apply double_source_tree_parameter_membership; exact MEMBER. }
  set (initialized:=double_tree_initialized_temps (double_source_tree_parameters tree) cache temps).
  destruct (@double_tree_capture_source_execution p [] tree fe ge locals temps memory after final
    (PTree.set flag (Vint Int.one) initialized) cache flag lower upper CHECK GLOBAL SCOPE EXCLUSIONS LOCAL LIMITS FRESH
    (PTree.gss _ _ _) ltac:(rewrite <- SOURCE; exact RUN)) as [prepared [accepted [CAPTURE [FLAG FRAME]]]].
  assert (PREPARATION : exec_stmt fe ge locals temps memory (double_tree_capture_prepare tree cache flag lower upper)
    E0 prepared memory Out_normal).
  { unfold double_tree_capture_prepare; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
    - apply double_tree_initialize_execution.
    - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [apply memory_capture_flag_execution|exact CAPTURE]. }
  assert (AGREE : temp_agree (statement_temps source++live) temps prepared).
  { intros key MEMBER; eapply writes_only_frame; [exact PREPARATION|apply double_tree_prepare_writes|apply PRIVATE; exact MEMBER]. }
  destruct (@structured_execution_temp_transport fe ge locals temps memory source E0 after final Out_normal RUN
    (statement_temps source++live) prepared (double_source_tree_writes tree)
    ltac:(rewrite SOURCE; exact (@double_source_tree_writes_only p [] tree CHECK))
    ltac:(unfold statement_scope; intros key MEMBER; apply in_or_app; left; exact MEMBER) AGREE)
    as [prepared_after [REPLAY EXIT]].
  exists prepared,accepted,prepared_after; split; [exact PREPARATION|split; [exact FLAG|]].
  split; [eapply temp_agree_weaken; [intros key MEMBER; apply in_or_app; right; exact MEMBER|exact AGREE]|].
  split; [exact REPLAY|eapply temp_agree_weaken; [intros key MEMBER; apply in_or_app; right; exact MEMBER|exact EXIT]].
Qed.

Print Assumptions double_tree_initialize_execution.
Print Assumptions double_tree_initialize_writes.
Print Assumptions double_tree_prepare_writes.
Print Assumptions checked_double_tree_capture_prepare.
