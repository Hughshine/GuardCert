From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame ClightRedundantSet
  ClightCountedLoop ClightLoopSyntax ClightRegionProgress CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryLoops.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage.
From GuardInterface Require Import ClightLoadedOffsetHeader ClightExpressionHeaderCapture
  ClightExpressionBodyPrefix ClightObservedHeaderPrefix ClightLoadedAffineNumericGuard
  ClightAffineFirstBodyReceipt ClightLoadedAffineBodyPrefix ClightLoadedAffineBodyDomain
  ClightLoadedAffineBodyStability ClightAffineBodyReceipt ClightAffineObservedWriteTest ClightStorePermissions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition offset_affine_body_ready parameters proposal pointer delta entry :=
  affine_loaded_body_ready parameters proposal entry /\
  loaded_offset_cached_header pointer delta(affine_proposed_bound proposal) entry.
Definition offset_affine_body_prefix fe parameters proposal pointer delta :=
  expression_body_prefix fe (affine_proposed_iterator proposal)(affine_proposed_bound proposal)
    (signed_load_offset pointer delta)(affine_proposed_body proposal)
    (affine_loaded_body_stable parameters proposal pointer)
    (offset_affine_body_ready parameters proposal pointer delta)(loaded_offset_observations pointer).
Definition offset_affine_body_preserved fe parameters proposal pointer :=
  expression_body_preserved fe (affine_proposed_iterator proposal)(affine_proposed_body proposal)
    (affine_loaded_body_stable parameters proposal pointer)(loaded_offset_observations pointer).

Lemma offset_affine_body_header parameters proposal pointer delta entry index current memory :
  offset_affine_body_ready parameters proposal pointer delta entry ->
  0<=index<=Int.signed(temp_word(affine_proposed_bound proposal)(entry_temps entry)) ->
  current!(affine_proposed_iterator proposal)=Some(Vint(Int.repr index)) ->
  temp_agree(affine_loaded_body_stable parameters proposal pointer)(entry_temps entry) current ->
  header_observations_match(loaded_offset_observations pointer entry) memory ->
  eval_expr(entry_ge entry)(entry_env entry) current memory(signed_load_offset pointer delta)
    (Vint(temp_word(affine_proposed_bound proposal)(entry_temps entry))).
Proof.
  intros [READY SNAPSHOT] RANGE ROW FRAME OBSERVED.
  pose proof SNAPSHOT as [block [offset [raw [POINTER [READ CACHE]]]]].
  eapply loaded_offset_bound_from_observations with(entry:=entry)
    (cache:=affine_proposed_bound proposal)(stable:=affine_loaded_body_stable parameters proposal pointer);
    [right; left; reflexivity|exact SNAPSHOT| |exact FRAME|exact OBSERVED].
  unfold temp_word; rewrite CACHE; reflexivity.
Qed.

Theorem offset_affine_body_ready_from_source source parameters live proposal pointer delta
  (package : affine_guard_package source parameters live proposal) fe ge locals temps memory after final :
  loaded_offset_cached_header pointer delta(affine_proposed_bound proposal)(Entry ge locals temps memory) ->
  affine_loaded_numeric_premise parameters proposal(Entry ge locals temps memory) ->
  temps!(affine_proposed_iterator proposal)=Some(Vint Int.zero) ->
  exec_stmt fe ge locals temps memory
    (loaded_offset_loop(affine_proposed_iterator proposal) pointer delta(affine_proposed_body proposal)) E0 after final Out_normal ->
  offset_affine_body_ready parameters proposal pointer delta(Entry ge locals temps memory).
Proof.
  intros SNAPSHOT NUMERIC ROW SOURCE; split; [|exact SNAPSHOT].
  split; [exact NUMERIC|split; [exact ROW|]].
  destruct SNAPSHOT as [block [offset [raw [POINTER [READ CACHE]]]]].
  destruct(affine_loaded_numeric_body_properties package) as [NORMAL QUIET].
  eapply affine_receipted_package_word_view; [exact package| |exact(proj1 NUMERIC)].
  eapply signed_expression_first_body_receipt with(upper:=Int.add raw delta)
    (bound:=signed_load_offset pointer delta);
    [reflexivity|exact NORMAL|exact QUIET| |exact CACHE|exact SOURCE].
  eapply signed_load_offset_eval; [exact POINTER|exact READ].
Qed.

Theorem offset_affine_body_initial_prefix source parameters live proposal pointer delta
  (package : affine_guard_package source parameters live proposal) fe ge locals temps memory after final :
  loaded_offset_cached_header pointer delta(affine_proposed_bound proposal)(Entry ge locals temps memory) ->
  affine_loaded_numeric_premise parameters proposal(Entry ge locals temps memory) ->
  temps!(affine_proposed_iterator proposal)=Some(Vint Int.zero) ->
  0<=Int.signed(temp_word(affine_proposed_bound proposal) temps) ->
  exec_stmt fe ge locals temps memory
    (loaded_offset_loop(affine_proposed_iterator proposal) pointer delta(affine_proposed_body proposal)) E0 after final Out_normal ->
  offset_affine_body_prefix fe parameters proposal pointer delta 0(Entry ge locals temps memory).
Proof.
  intros SNAPSHOT NUMERIC ROW NONNEGATIVE SOURCE.
  eapply expression_body_prefix_initial with(after:=after)(final:=final);
    [eapply offset_affine_body_ready_from_source; eassumption| |exact NONNEGATIVE|exact ROW| |exact SOURCE].
  - destruct SNAPSHOT as [block [offset [raw [POINTER [READ CACHE]]]]]; exists(Int.add raw delta); exact CACHE.
  - eapply loaded_offset_initial_observations; exact SNAPSHOT.
Qed.

Section BODY.
Variables source : statement.
Variables parameters live : list ident.
Variable proposal : affine_guard_proposal.
Variable package : affine_guard_package source parameters live proposal.
Variables pointer : ident.
Variable delta : int.
Hypothesis NAMES : affine_loaded_body_names_check proposal pointer=true.

Theorem offset_affine_prefix_body_receipt fe entry index :
  offset_affine_body_prefix fe parameters proposal pointer delta index entry ->
  index<Int.signed(temp_word(affine_proposed_bound proposal)(entry_temps entry)) ->
  affine_body_receipt fe parameters proposal pointer index entry.
Proof.
  intros PREFIX ACTIVE; destruct(affine_loaded_numeric_body_properties package) as [NORMAL QUIET].
  eapply affine_expression_prefix_body_receipt with(bound:=signed_load_offset pointer delta)
    (ready:=offset_affine_body_ready parameters proposal pointer delta)
    (observations:=loaded_offset_observations pointer);
    [reflexivity|exact NORMAL|exact QUIET| |apply offset_affine_body_header|exact PREFIX|exact ACTIVE].
  intros origin READY; exact(proj1 READY).
Qed.

Lemma offset_affine_prefix_observed_read fe entry index :
  offset_affine_body_prefix fe parameters proposal pointer delta index entry ->
  forall block offset, (entry_temps entry)!pointer=Some(Vptr block offset) ->
    exists value, Mem.loadv Mint32(entry_memory entry)(Vptr block offset)=Some value.
Proof.
  intros [[READY [actual [base [raw [POINTER [READ CACHE]]]]]] REST] block offset ADDRESS.
  assert(SAME:Vptr actual base=Vptr block offset) by congruence; injection SAME as BLOCK OFFSET; subst actual base.
  exists(Vint raw); exact READ.
Qed.

Theorem offset_affine_body_check_preserved fe entry index code block offset :
  offset_affine_body_prefix fe parameters proposal pointer delta index entry ->
  index<Int.signed(temp_word(affine_proposed_bound proposal)(entry_temps entry)) ->
  affine_loaded_body_model parameters proposal=Some code -> (entry_temps entry)!pointer=Some(Vptr block offset) ->
  ClightLoadedAffineWriteTest.affine_loaded_body_check_result proposal index entry
    (MemoryLocation Mint32 block(Ptrofs.unsigned offset))=true ->
  offset_affine_body_preserved fe parameters proposal pointer index entry.
Proof.
  intros PREFIX ACTIVE LOWER POINTER CHECK.
  pose proof PREFIX as [[READY SNAPSHOT] [CACHE [RANGE REST]]].
  pose proof (@offset_affine_prefix_body_receipt fe entry index PREFIX ACTIVE) as RECEIPT.
  pose proof (@offset_affine_prefix_observed_read fe entry index PREFIX) as READABLE.
  pose proof (@affine_received_body_check_writes_apart source parameters live proposal package pointer NAMES
    fe entry index code RECEIPT READABLE LOWER block offset POINTER CHECK) as APART.
  intros current memory after final ROW FRAME OBSERVED BODY.
  pose proof (@affine_loaded_ready_body_observation source parameters live proposal package pointer NAMES
    fe entry index code current memory after final (MemoryLocation Mint32 block(Ptrofs.unsigned offset))
    READY ltac:(lia) ROW FRAME LOWER APART BODY) as KEEP.
  destruct SNAPSHOT as [other [base [raw [ADDRESS [READ WORD]]]]].
  assert(SAME:Vptr other base=Vptr block offset) by congruence; injection SAME as BLOCK OFFSET; subst other base.
  unfold loaded_offset_observations in OBSERVED |- *; rewrite POINTER,READ in OBSERVED |- *.
  inversion OBSERVED as [|first rest VALUE REST']; subst.
  constructor; [|constructor]; change(location_load(MemoryLocation Mint32 block(Ptrofs.unsigned offset)) final=Some(Vint raw)).
  rewrite KEEP; exact VALUE.
Qed.
End BODY.

Print Assumptions offset_affine_body_header.
Print Assumptions offset_affine_body_ready_from_source.
Print Assumptions offset_affine_body_initial_prefix.
Print Assumptions offset_affine_prefix_body_receipt.
Print Assumptions offset_affine_prefix_observed_read.
Print Assumptions offset_affine_body_check_preserved.
