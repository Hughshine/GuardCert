From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightRedundantSet ClightTempFrame
  ClightTempFootprint ClightProjectedExecution ClightLoopSyntax ClightRegionProgress.
From GuardInterface Require Import ClightStrictLoopProgress ClightStrictIteration
  ClightLoadedBoundSyntax ClightAffineLoadedBoundTransport ClightLoadedSnapshotInsertion
  ClightCheckPlanFrame ClightAffineFirstBodyReceipt.
Import ListNotations.
Set Implicit Arguments.

(** This is a receipt from the actual loaded source, not from a loop already
    transported to a stable cached bound. The body may change the bound cell. *)
Theorem loaded_affine_first_body_receipt fe ge locals temps memory iterator pointer cache body after final
  block offset upper :
  normal_statement body=true -> quiet_statement body=true ->
  temps!pointer=Some(Vptr block offset) ->
  Mem.loadv Mint32 memory (Vptr block offset)=Some(Vint upper) ->
  temps!cache=Some(Vint upper) ->
  exec_stmt fe ge locals temps memory (loaded_bound_loop iterator pointer body)
    E0 after final Out_normal ->
  affine_first_body_receipt iterator cache body fe (Entry ge locals temps memory).
Proof.
  intros NORMAL QUIET POINTER READ CACHE SOURCE.
  destruct (loaded_bound_completed_header SOURCE) as [flag TEST].
  destruct (loaded_bound_test_facts TEST)
    as [row [word [other [other_offset [ROW [OTHER [LOAD FLAG]]]]]]].
  assert (ADDRESS : Vptr other other_offset=Vptr block offset) by congruence.
  injection ADDRESS as BLOCK OFFSET; subst other other_offset.
  assert (WORD : word=upper) by congruence; subst word.
  unfold affine_first_body_receipt; cbn [entry_temps register_domain].
  split; [exists row; exact ROW|split; [exists upper; exact CACHE|]].
  intro ACTIVE; unfold temp_word in ACTIVE; rewrite ROW,CACHE in ACTIVE.
  assert (TRUE : flag=true).
  { rewrite FLAG; unfold Int.lt; destruct (zlt (Int.signed row) (Int.signed upper));
      [reflexivity|contradiction]. }
  rewrite TRUE in TEST; unfold loaded_bound_loop in SOURCE.
  destruct (@strict_active_iteration fe ge locals iterator (loaded_bound_test iterator pointer) body
    temps memory after final NORMAL QUIET TEST SOURCE)
    as [body_after [body_final [next [next_memory [BODY REST]]]]].
  exists body_after,body_final; exact BODY.
Qed.

Lemma loaded_bound_pointer_in_scope iterator pointer body :
  In pointer (statement_temps (loaded_bound_loop iterator pointer body)).
Proof.
  unfold loaded_bound_loop,strict_frontend_loop.
  cbn [statement_temps expression_temps loaded_bound_test signed_load signed_pointer_temp].
  repeat rewrite in_app_iff; cbn; tauto.
Qed.

(** Ordered capture is justified by the real first header, including a
    zero-trip source. Freshness transports the original source into the
    prepared entry without assuming stability of any later memory read. *)
Theorem loaded_affine_capture_receipt fe ge locals temps memory iterator pointer body cache live after final :
  normal_statement body=true -> quiet_statement body=true ->
  check_plan_frameable (loaded_bound_loop iterator pointer body)=true ->
  ~In cache (statement_temps (loaded_bound_loop iterator pointer body)++live) ->
  exec_stmt fe ge locals temps memory (loaded_bound_loop iterator pointer body)
    E0 after final Out_normal ->
  exists upper prepared_after,
    exec_stmt fe ge locals temps memory (Sset cache (signed_load pointer))
      E0 (PTree.set cache (Vint upper) temps) memory Out_normal /\
    exec_stmt fe ge locals (PTree.set cache (Vint upper) temps) memory
      (loaded_bound_loop iterator pointer body) E0 prepared_after final Out_normal /\
    temp_agree (statement_temps (loaded_bound_loop iterator pointer body)++live) after prepared_after /\
    affine_first_body_receipt iterator cache body fe
      (Entry ge locals (PTree.set cache (Vint upper) temps) memory).
Proof.
  intros NORMAL QUIET FRAMEABLE PRIVATE SOURCE.
  destruct (loaded_header_snapshot_read SOURCE) as [upper EVAL].
  destruct (signed_load_inv EVAL) as [block [offset [POINTER READ]]].
  destruct (@structured_execution_temp_transport fe ge locals temps memory
    (loaded_bound_loop iterator pointer body) E0 after final Out_normal SOURCE
    (statement_temps (loaded_bound_loop iterator pointer body)++live)
    (PTree.set cache (Vint upper) temps)
    (statement_temps (loaded_bound_loop iterator pointer body))
    (@check_plan_frameable_writes _ FRAMEABLE)
    ltac:(unfold statement_scope; intros identifier MEMBER; apply in_or_app; left; exact MEMBER)
    (@temp_agree_set _ temps cache (Vint upper) PRIVATE)) as [prepared_after [PREPARED PUBLIC]].
  exists upper,prepared_after; split; [constructor; exact EVAL|split; [exact PREPARED|split; [exact PUBLIC|]]].
  eapply loaded_affine_first_body_receipt; [exact NORMAL|exact QUIET| |exact READ|apply PTree.gss|exact PREPARED].
  rewrite PTree.gso; [exact POINTER|].
  intro SAME; subst cache; apply PRIVATE,in_or_app; left; apply loaded_bound_pointer_in_scope.
Qed.

Print Assumptions loaded_affine_first_body_receipt.
Print Assumptions loaded_bound_pointer_in_scope.
Print Assumptions loaded_affine_capture_receipt.

Lemma loaded_bound_zero_trip_execution fe ge locals temps memory iterator pointer body :
  expression_test (loaded_bound_test iterator pointer) (Entry ge locals temps memory) false ->
  exec_stmt fe ge locals temps memory (loaded_bound_loop iterator pointer body)
    E0 temps memory Out_normal.
Proof.
  intros [value [EVAL BOOL]]; unfold loaded_bound_loop,strict_frontend_loop.
  eapply exec_Sloop_stop1 with (out':=Out_break).
  - eapply exec_Sseq_2; [|discriminate].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [constructor|].
    eapply exec_Sifthenelse with (b:=false); [exact EVAL|exact BOOL|constructor].
  - constructor.
Qed.
Print Assumptions loaded_bound_zero_trip_execution.
