From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightTempFrame ClightNoWrap
  ClightCountedLoop ClightLoopSyntax ClightRegionProgress CompCertMemoryActions
  ClightRectangularLoops ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineSourceExpressions
  GuardMemoryParametricSourceClight GuardMemoryMultiPointerSequence.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightWordReadSnapshots
  ClightAffineHeaderSnapshots ClightObservedHeaderPrefix ClightObservedBodyPrefix
  ClightAffineInnerPointerSourceGuard ClightAffinePreparedState ClightAffinePreparedRows
  ClightStrictLoopProgress ClightExpressionHeaderCapture.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** These are initial read receipts, not assumptions about future writes. *)
Definition cached_signed_read pointer cache entry := exists block offset word,
  (entry_temps entry)!pointer=Some(Vptr block offset) /\
  (entry_temps entry)!cache=Some(Vint word) /\
  Mem.loadv Mint32 (entry_memory entry)(Vptr block offset)=Some(Vint word).
Definition cached_signed_observations pointer cache entry : list(memory_location*val) :=
  match (entry_temps entry)!pointer,(entry_temps entry)!cache with
  | Some(Vptr block offset),Some(Vint word) =>
      [(MemoryLocation Mint32 block(Ptrofs.unsigned offset),Vint word)]
  | _,_ => [] end.

Lemma cached_signed_initial_observations pointer cache entry :
  cached_signed_read pointer cache entry ->
  header_observations_match(cached_signed_observations pointer cache entry)(entry_memory entry).
Proof.
  intros [block [offset [word [POINTER [CACHE READ]]]]].
  unfold cached_signed_observations; rewrite POINTER,CACHE.
  unfold header_observations_match; constructor; [|constructor].
  cbn [fst snd location_load]; cbn [Mem.loadv] in READ;
    destruct(zle _ _); [exact READ|discriminate].
Qed.

Theorem cached_signed_current_read pointer cache stable entry current memory :
  In pointer stable -> In cache stable -> cached_signed_read pointer cache entry ->
  temp_agree stable(entry_temps entry)current ->
  header_observations_match(cached_signed_observations pointer cache entry)memory ->
  exists word, current!cache=Some(Vint word) /\
    eval_expr(entry_ge entry)(entry_env entry)current memory(signed_load pointer)(Vint word).
Proof.
  intros POINTER_MEMBER CACHE_MEMBER [block [offset [word [POINTER [CACHE INITIAL]]]]] FRAME OBSERVED.
  unfold cached_signed_observations in OBSERVED; rewrite POINTER,CACHE in OBSERVED.
  unfold header_observations_match in OBSERVED; inversion OBSERVED; subst.
  assert(READ : Mem.loadv Mint32 memory(Vptr block offset)=Some(Vint word)).
  { cbn [Mem.loadv] in INITIAL |- *; destruct(zle _ _); [|discriminate].
    match goal with OBS:location_load _ _=Some _ |- _ => exact OBS end. }
  exists word; split; [rewrite FRAME by exact CACHE_MEMBER; exact CACHE|].
  apply eval_Elvalue with(loc:=block)(ofs:=offset)(bf:=Full).
  - apply eval_Ederef,eval_Etempvar; rewrite FRAME by exact POINTER_MEMBER; exact POINTER.
  - apply deref_loc_value with(chunk:=Mint32); [reflexivity|exact READ].
Qed.

Definition single_snapshot_binding (pointer cache identifier : ident) :=
  if Pos.eqb identifier pointer then Some cache else None.
Lemma single_snapshot_receipts code pointer cache stable entry current memory :
  In pointer stable -> In cache stable -> cached_signed_read pointer cache entry ->
  temp_agree stable(entry_temps entry)current ->
  header_observations_match(cached_signed_observations pointer cache entry)memory ->
  snapshot_word_receipts(single_snapshot_binding pointer cache)code
    (entry_ge entry)(entry_env entry)current memory.
Proof.
  intros POINTER CACHE READ FRAME OBSERVED identifier target MEMBER BIND.
  unfold single_snapshot_binding in BIND; destruct(Pos.eqb identifier pointer)eqn:SAME; [|discriminate].
  apply Pos.eqb_eq in SAME; subst identifier; injection BIND as TARGET; subst target.
  exact(@cached_signed_current_read pointer cache stable entry current memory POINTER CACHE READ FRAME OBSERVED).
Qed.

Definition affine_snapshot_body source(package:memory_affine_inner_pointer_package source) header :=
  affine_setup_child
    (affine_inner_pointer_column(affine_inner_pointer_shape package))
    (affine_inner_pointer_inner_bound(affine_inner_pointer_shape package)) header
    (affine_inner_pointer_body(affine_inner_pointer_shape package)).
Definition affine_snapshot_source source(package:memory_affine_inner_pointer_package source) root header :=
  strict_frontend_loop(affine_inner_pointer_row(affine_inner_pointer_shape package))
    (loaded_bound_test(affine_inner_pointer_row(affine_inner_pointer_shape package))root)
    (affine_snapshot_body package header).
Definition affine_snapshot_stable source(package:memory_affine_inner_pointer_package source) root child :=
  child::affine_prepared_stable package root.
Definition affine_snapshot_observations source(package:memory_affine_inner_pointer_package source) root child child_cache entry :=
  cached_signed_observations root(affine_inner_pointer_bound(affine_inner_pointer_shape package))entry ++
  cached_signed_observations child child_cache entry.
Definition affine_snapshot_ready source(package:memory_affine_inner_pointer_package source) root child child_cache entry :=
  affine_inner_pointer_ready package entry /\
  cached_signed_read root(affine_inner_pointer_bound(affine_inner_pointer_shape package))entry /\
  cached_signed_read child child_cache entry.
Definition affine_snapshot_package_prefix source(package:memory_affine_inner_pointer_package source)
  root child child_cache header fe :=
  @observed_body_prefix fe(affine_inner_pointer_row(affine_inner_pointer_shape package))
    (affine_inner_pointer_bound(affine_inner_pointer_shape package))
    (loaded_bound_test(affine_inner_pointer_row(affine_inner_pointer_shape package))root)
    (affine_snapshot_body package header)(affine_snapshot_stable package root child)
    (affine_snapshot_ready package root child child_cache)
    (affine_snapshot_observations package root child child_cache).

Section ROWS.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variables root child child_cache : ident.
Variable header : expr.
Let shape := affine_inner_pointer_shape package.
Let row := affine_inner_pointer_row shape.
Let column := affine_inner_pointer_column shape.
Let inner_bound := affine_inner_pointer_inner_bound shape.
Let cache := affine_inner_pointer_bound shape.
Let stable := affine_snapshot_stable package root child.
Let CERT := affine_inner_pointer_syntax package.
Hypothesis ROOT_FRESH : root<>row /\ root<>column /\ root<>inner_bound.
Hypothesis CHILD_FRESH : child<>row /\ child<>column /\ child<>inner_bound.
Hypothesis CACHE_MEMBER : In child_cache stable.
Hypothesis HEADER_WORD : snapshot_word_expression header.
(** Ordinary shape equality, to be produced by a checked source adapter. *)
Hypothesis CACHED_BODY : affine_inner_pointer_outer_body shape =
  affine_snapshot_body package(snapshot_word_replace(single_snapshot_binding child child_cache)header).

Lemma affine_snapshot_protected identifier : In identifier stable ->
  identifier<>row /\ identifier<>column /\ identifier<>inner_bound.
Proof.
  intros [<-|MEMBER]; [exact CHILD_FRESH|].
  exact(@affine_prepared_external_protected source package root ROOT_FRESH identifier MEMBER).
Qed.

Theorem affine_snapshot_actual_row_decode_exact fe entry i current memory after final :
  affine_snapshot_ready package root child child_cache entry ->
  0<=i<affine_prepared_count package entry -> current!row=Some(Vint(Int.repr i)) ->
  temp_agree stable(entry_temps entry)current ->
  header_observations_match(affine_snapshot_observations package root child child_cache entry)memory ->
  exec_stmt fe(entry_ge entry)(entry_env entry)current memory(affine_snapshot_body package header)
    E0 after final Out_normal ->
  counted_iterations(affine_prepared_point package entry i)(Z.to_nat(affine_prepared_upper package entry i))
    0 memory final /\ after=memory_parametric_settle column inner_bound(affine_prepared_upper package entry)i current.
Proof.
  intros [READY [ROOT CHILD]] RANGE ROW FRAME OBSERVED BODY.
  unfold affine_snapshot_observations,header_observations_match in OBSERVED;
    apply Forall_app in OBSERVED as [ROOT_OBS CHILD_OBS].
  assert(RECEIPTS : snapshot_word_receipts(single_snapshot_binding child child_cache)header
    (entry_ge entry)(entry_env entry)current memory).
  { exact(@single_snapshot_receipts header child child_cache stable entry current memory
      (or_introl eq_refl) CACHE_MEMBER CHILD FRAME CHILD_OBS). }
  assert(CACHED : exec_stmt fe(entry_ge entry)(entry_env entry)current memory
    (affine_inner_pointer_outer_body shape)E0 after final Out_normal).
  { rewrite CACHED_BODY; unfold affine_snapshot_body,affine_setup_child in BODY|-*.
    apply(proj1(@snapshot_word_setup_execution fe(entry_ge entry)(entry_env entry)current memory
      inner_bound header
      (Ssequence(ClightRectangularLoops.rectangle_reset column)
        (frontend_counted_loop column inner_bound(affine_inner_pointer_body shape)))
      (single_snapshot_binding child child_cache)E0 after final Out_normal HEADER_WORD RECEIPTS)); exact BODY. }
  eapply(@affine_prepared_actual_row_decode_exact source package root ROOT_FRESH fe entry i current memory after final);
    [exact READY|exact RANGE|exact ROW| |exact CACHED].
  eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER; right; exact MEMBER.
Qed.

Theorem affine_snapshot_actual_row_decode fe entry i current memory after final :
  affine_snapshot_ready package root child child_cache entry ->
  0<=i<affine_prepared_count package entry -> current!row=Some(Vint(Int.repr i)) ->
  temp_agree stable(entry_temps entry)current ->
  header_observations_match(affine_snapshot_observations package root child child_cache entry)memory ->
  exec_stmt fe(entry_ge entry)(entry_env entry)current memory(affine_snapshot_body package header)
    E0 after final Out_normal ->
  counted_iterations(affine_prepared_point package entry i)(Z.to_nat(affine_prepared_upper package entry i))
    0 memory final /\ after!row=current!row /\ temp_agree stable current after.
Proof.
  intros READY RANGE ROW FRAME OBSERVED BODY.
  destruct(affine_snapshot_actual_row_decode_exact READY RANGE ROW FRAME OBSERVED BODY)as [ITER EXIT].
  split; [exact ITER|rewrite EXIT; split].
  - pose proof(affine_inner_pointer_rc CERT)as RC; change(row<>column)in RC.
    pose proof(affine_inner_pointer_rk CERT)as RK; change(row<>inner_bound)in RK.
    unfold memory_parametric_settle; rewrite !PTree.gso by congruence; reflexivity.
  - unfold memory_parametric_settle; eapply temp_agree_trans; apply temp_agree_set.
    + intro MEMBER; exact(proj2(proj2(affine_snapshot_protected MEMBER))eq_refl).
    + intro MEMBER; exact(proj1(proj2(affine_snapshot_protected MEMBER))eq_refl).
Qed.
End ROWS.

Print Assumptions cached_signed_initial_observations.
Print Assumptions cached_signed_current_read.
Print Assumptions single_snapshot_receipts.
Print Assumptions affine_snapshot_actual_row_decode_exact.
Print Assumptions affine_snapshot_actual_row_decode.
