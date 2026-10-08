(** Accepted joint scans derive the cached nested source and transport it to
    the actual scan exit. Cached execution never licenses its own scan. *)
From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightNoWrap
  ClightLoopSyntax ClightCountedLoop ClightCountedProtocol ClightFrontendLoopProtocol ClightProjectedExecution ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardInterface Require Import ClightLoadedOffsetHeader ClightNestedLoadedOffset ClightNestedExpressionCapture
  ClightNestedExpressionTransport ClightObservedHeaderPrefix ClightWordStoreSequence ClightWordStoreSequenceFactory
  ClightWordStoreNestedPrefix ClightWordStoreNestedScan.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma word_store_counted_writes allowed row cache body :
  In row allowed -> writes_only allowed body -> writes_only allowed(frontend_counted_loop row cache body).
Proof.
  intros ROW BODY; unfold frontend_counted_loop,counter_increment; apply writes_loop; apply writes_sequence.
  - apply writes_sequence; [constructor|apply writes_if; constructor].
  - exact BODY.
  - constructor.
  - constructor; exact ROW.
Qed.
Lemma word_store_nested_cached_writes row cache column child_cache body (checked:checked_word_store_body body) :
  writes_only [row;column] (nested_cached_source row cache column child_cache body).
Proof.
  unfold nested_cached_source,nested_cached_body; apply word_store_counted_writes; [left; reflexivity|].
  apply writes_sequence.
  - constructor; right; left; reflexivity.
  - apply word_store_counted_writes; [right; left; reflexivity|].
    eapply writes_only_weaken; [|exact(wsbody_writes checked)]; cbn; tauto.
Qed.

Section CACHED.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variables row cache pointer column child_cache child_pointer row_cursor row_limit column_cursor column_limit flag : ident.
Variables delta child_delta : int.
Variable body : statement.
Variable checked : checked_word_store_body body.
Variables stable live : list ident.
Variable rename : ident -> ident.
Hypotheses (POINTER_STABLE : In pointer stable) (CHILD_POINTER_STABLE : In child_pointer stable)
  (CACHE_STABLE : In cache stable) (CHILD_CACHE_STABLE : In child_cache stable)
  (ROW_PRIVATE : ~In row stable) (COLUMN_PRIVATE : ~In column stable) (ROW_COLUMN : row<>column)
  (STABLE_LIVE : incl stable live)
  (UNIQUE : NoDup [row_cursor;row_limit;column_cursor;column_limit;flag])
  (PRIVATE : forall id, In id [row_cursor;row_limit;column_cursor;column_limit;flag] -> ~In id live)
  (RENAME_ROW : rename row=row_cursor) (RENAME_COLUMN : rename column=column_cursor).
Hypothesis RENAME_STABLE : forall id, In id stable -> rename id=id.
Hypothesis SITE_POINTERS : forall site, In site(wsbody_sites checked) -> In(wss_pointer site) stable.
Hypothesis SITE_INDICES : forall site, In site(wsbody_sites checked) -> expression_scope(row::column::stable)(wss_index site).
Let sites := wsbody_sites checked.
Let ready := word_store_nested_ready pointer delta cache child_pointer child_delta child_cache.
Let result entry := word_store_nested_scan_result cache child_cache row_cursor column_cursor rename sites pointer child_pointer entry.
Let scan := word_store_nested_scan_code cache child_cache row_cursor row_limit column_cursor column_limit flag rename sites pointer child_pointer.
Let source := nested_loaded_offset_source row pointer delta column child_pointer child_delta body.
Let cached := nested_cached_source row cache column child_cache body.

Theorem word_store_nested_scan_from_source entry current source_after final :
  ready entry -> 0<=Int.signed(temp_word cache(entry_temps entry)) ->
  0<=Int.signed(temp_word child_cache(entry_temps entry)) -> (entry_temps entry)!row=Some(Vint Int.zero) ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry) source E0 source_after final Out_normal ->
  temp_agree live(entry_temps entry) current ->
  exists after,
    exec_stmt fe(entry_ge entry)(entry_env entry) current(entry_memory entry) scan E0 after(entry_memory entry) Out_normal /\
    temp_agree live current after /\ after!flag=Some(memory_boolean_word(result entry)) /\
    (result entry=true -> exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
      cached E0 source_after final Out_normal).
Proof.
  intros READY NONNEGATIVE CHILD_NONNEGATIVE ROW SOURCE FRAME.
  assert (PREFIX : word_store_nested_outer_prefix fe row cache pointer delta column child_cache child_pointer child_delta body stable 0 entry).
  { eapply word_store_nested_outer_initial; eassumption. }
  destruct (@word_store_nested_scan_execution fe row cache pointer column child_cache child_pointer
    row_cursor row_limit column_cursor column_limit flag delta child_delta body checked stable live rename
    POINTER_STABLE CHILD_POINTER_STABLE CACHE_STABLE CHILD_CACHE_STABLE ROW_PRIVATE COLUMN_PRIVATE ROW_COLUMN
    STABLE_LIVE UNIQUE PRIVATE RENAME_ROW RENAME_COLUMN RENAME_STABLE SITE_POINTERS SITE_INDICES entry current
    PREFIX CHILD_NONNEGATIVE FRAME) as [after [RUN [PUBLIC [FLAG ACCEPTED]]]].
  exists after; split; [exact RUN|split; [exact PUBLIC|split; [exact FLAG|]]].
  intro ACCEPT.
  assert (PRESERVE : forall i j current_temps memory exit last,
    0<=i<Int.signed(temp_word cache(entry_temps entry)) ->
    0<=j<Int.signed(temp_word child_cache(entry_temps entry)) ->
    current_temps!row=Some(Vint(Int.repr i)) -> current_temps!column=Some(Vint(Int.repr j)) ->
    temp_agree stable(entry_temps entry) current_temps ->
    header_observations_match(nested_loaded_offset_observations pointer child_pointer entry) memory ->
    exec_stmt fe(entry_ge entry)(entry_env entry) current_temps memory body E0 exit last Out_normal ->
    header_observations_match(nested_loaded_offset_observations pointer child_pointer entry) last).
  { intros i j current_temps memory exit last IR JR CURRENT_ROW CURRENT_COLUMN FRAME' OBSERVED BODY.
    destruct(ACCEPTED ACCEPT i j IR JR) as [INV CHECK].
    eapply word_store_nested_point_preserved with (checked:=checked) (rename:=rename)
      (row:=row) (cache:=cache) (column:=column) (child_cache:=child_cache)
      (pointer:=pointer) (child_pointer:=child_pointer) (delta:=delta) (child_delta:=child_delta)
      (stable:=stable) (row_cursor:=row_cursor) (column_cursor:=column_cursor)
      (entry:=entry) (i:=i) (j:=j); try eassumption; try exact(proj2 JR).
    - intro MEMBER; eapply PRIVATE with(id:=row_cursor); [cbn; tauto|apply STABLE_LIVE; exact MEMBER].
    - intro MEMBER; eapply PRIVATE with(id:=column_cursor); [cbn; tauto|apply STABLE_LIVE; exact MEMBER].
    - exact(proj1(proj2(word_store_nested_controls_pairwise UNIQUE))). }
  apply (proj1 (@nested_loaded_offset_initial_cached fe(entry_ge entry)(entry_env entry)(entry_temps entry)
    (entry_memory entry) row pointer delta column child_pointer child_delta cache child_cache body stable [] source_after final
    POINTER_STABLE CHILD_POINTER_STABLE CACHE_STABLE CHILD_CACHE_STABLE ROW_PRIVATE COLUMN_PRIVATE ROW_COLUMN
    (wsbody_normal checked)(wsbody_quiet checked)(wsbody_writes checked) ltac:(cbn; tauto) ltac:(cbn; tauto)
    ltac:(intros; cbn; tauto) (proj1 READY)(proj2 READY) NONNEGATIVE CHILD_NONNEGATIVE ROW
    PRESERVE SOURCE)).
Qed.

Theorem word_store_nested_scan_cached_exit entry current source_after final :
  statement_scope live cached ->
  ready entry -> 0<=Int.signed(temp_word cache(entry_temps entry)) ->
  0<=Int.signed(temp_word child_cache(entry_temps entry)) -> (entry_temps entry)!row=Some(Vint Int.zero) ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry) source E0 source_after final Out_normal ->
  temp_agree live(entry_temps entry) current ->
  exists after,
    exec_stmt fe(entry_ge entry)(entry_env entry) current(entry_memory entry) scan E0 after(entry_memory entry) Out_normal /\
    temp_agree live current after /\ after!flag=Some(memory_boolean_word(result entry)) /\
    (result entry=true -> exists cached_after,
      exec_stmt fe(entry_ge entry)(entry_env entry) after(entry_memory entry) cached E0 cached_after final Out_normal /\
      temp_agree live source_after cached_after).
Proof.
  intros SCOPE READY NONNEGATIVE CHILD_NONNEGATIVE ROW SOURCE FRAME.
  destruct (word_store_nested_scan_from_source READY NONNEGATIVE CHILD_NONNEGATIVE ROW SOURCE FRAME)
    as [after [RUN [PUBLIC [FLAG CACHED]]]].
  exists after; split; [exact RUN|split; [exact PUBLIC|split; [exact FLAG|]]].
  intro ACCEPT; eapply structured_execution_temp_transport;
    [exact(CACHED ACCEPT)|exact(word_store_nested_cached_writes row cache column child_cache checked)|exact SCOPE|].
  eapply temp_agree_trans; eassumption.
Qed.
End CACHED.

Print Assumptions word_store_counted_writes.
Print Assumptions word_store_nested_cached_writes.
Print Assumptions word_store_nested_scan_from_source.
Print Assumptions word_store_nested_scan_cached_exit.
