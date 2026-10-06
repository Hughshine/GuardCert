From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightRedundantSet ClightNoWrap ClightFrontendLoopProtocol.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestSourceShape AffineNestSourceDecode
  AffineNestLeafModel AffineNestGuardPackage AffineNestGuardParameterCheck.
From GuardInterface Require Import ClightLoadedAffineNumericGuard ClightLoadedBodyPrefix ClightLoadedBodyTransport
  ClightStructuredStorePermissions ClightStorePermissions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_loaded_body_stable parameters proposal pointer :=
  affine_proposed_bound proposal::pointer::(parameters++affine_proposed_pointers proposal).

(** The loaded pointer and body pointer registers must survive the source's
    nested counters. This is a checked syntax obligation, not a future-value
    stability premise. *)
Definition affine_loaded_body_names_check proposal pointer :=
  forallb (fun identifier=>negb(existsb(Pos.eqb identifier)
    (affine_nest_mutated(affine_proposal_nest proposal)))) (pointer::affine_proposed_pointers proposal).

Lemma affine_loaded_body_names_sound proposal pointer :
  affine_loaded_body_names_check proposal pointer=true ->
  forall identifier, In identifier(pointer::affine_proposed_pointers proposal) ->
    ~In identifier(affine_nest_mutated(affine_proposal_nest proposal)).
Proof.
  intros CHECK identifier MEMBER; apply forallb_forall with(x:=identifier) in CHECK; [|exact MEMBER].
  apply negb_true_iff in CHECK; intro BAD.
  assert (FOUND : existsb(Pos.eqb identifier)(affine_nest_mutated(affine_proposal_nest proposal))=true).
  { apply existsb_exists; exists identifier; split; [exact BAD|apply Pos.eqb_refl]. }
  congruence.
Qed.

Section PACKAGE.
Variables source : statement.
Variables parameters live : list ident.
Variable proposal : affine_guard_proposal.
Variable package : affine_guard_package source parameters live proposal.
Variable pointer : ident.
Hypothesis NAMES : affine_loaded_body_names_check proposal pointer=true.

Lemma affine_loaded_body_writes :
  writes_only (affine_nest_controls(affine_proposed_child proposal)) (affine_proposed_body proposal).
Proof.
  pose proof (described_affine_shapes(affine_package_description package)) as SHAPES.
  rewrite (affine_package_nest package) in SHAPES.
  eapply affine_nest_body_writes; [exact SHAPES|exact(affine_leaf_writes(affine_package_leaf package))].
Qed.

Lemma affine_loaded_body_controls :
  ~In (affine_proposed_iterator proposal) (affine_nest_controls(affine_proposed_child proposal)) /\
  (forall identifier, In identifier(affine_loaded_body_stable parameters proposal pointer) ->
    ~In identifier(affine_nest_mutated(affine_proposal_nest proposal))).
Proof.
  pose proof (@affine_nest_fresh_controls _ (described_affine_fresh(affine_package_description package))) as FRESH.
  rewrite (affine_package_nest package) in FRESH; cbn [affine_proposal_nest affine_nest_controls] in FRESH.
  apply NoDup_cons_iff in FRESH as [ROOT REST]; apply NoDup_cons_iff in REST as [BOUND REST].
  split; [intro BAD; apply ROOT; right; exact BAD|].
  intros identifier MEMBER BAD; cbn [affine_loaded_body_stable] in MEMBER.
  destruct MEMBER as [CACHE|[POINTER|PARAMETER]].
  - subst identifier; cbn [affine_nest_mutated affine_proposal_nest] in BAD.
    destruct BAD as [SAME|BAD]; [apply ROOT; left; symmetry; exact SAME|exact(BOUND BAD)].
  - subst identifier; exact (@affine_loaded_body_names_sound proposal pointer NAMES pointer (or_introl eq_refl) BAD).
  - apply in_app_or in PARAMETER as [PARAMETER|BODY_POINTER].
    + exact (proj2 (@check_affine_guard_parameters_sound _ _ _ _ _ (affine_package_used package) identifier PARAMETER) BAD).
    + exact (@affine_loaded_body_names_sound proposal pointer NAMES identifier (or_intror BODY_POINTER) BAD).
Qed.

Theorem affine_loaded_body_memory_back fe ge locals temps memory trace after final outcome :
  exec_stmt fe ge locals temps memory (affine_proposed_body proposal) trace after final outcome ->
  memory_accesses_back memory final.
Proof. intro SOURCE; eapply structured_memory_accesses_back; [exact SOURCE|apply affine_loaded_body_writes]. Qed.

Theorem affine_loaded_body_initial_prefix fe ge locals temps memory after final :
  affine_loaded_numeric_snapshot pointer proposal (Entry ge locals temps memory) ->
  affine_loaded_numeric_premise parameters proposal (Entry ge locals temps memory) ->
  temps!(affine_proposed_iterator proposal)=Some(Vint Int.zero) ->
  0<=Int.signed(temp_word (affine_proposed_bound proposal) temps) ->
  exec_stmt fe ge locals temps memory (affine_loaded_numeric_source pointer proposal) E0 after final Out_normal ->
  loaded_body_prefix fe (affine_proposed_iterator proposal) (affine_proposed_bound proposal) pointer
    (affine_proposed_body proposal) (affine_loaded_body_stable parameters proposal pointer)
    (affine_loaded_numeric_premise parameters proposal) 0 (Entry ge locals temps memory).
Proof.
  intros [block [offset [upper [POINTER [READ CACHE]]]]] NUMERIC ROW NONNEGATIVE SOURCE.
  cbn [entry_temps entry_memory] in POINTER,READ,CACHE.
  eapply loaded_body_prefix_initial with(block:=block)(offset:=offset)(after:=after)(final:=final);
    try eassumption; [exists upper; exact CACHE|].
  cbn [entry_temps]; unfold temp_word; rewrite CACHE; exact READ.
Qed.

(** The remaining domain obligation is stated on actual completed bodies.
    Once the new recursive scan proves it, the cached source needed by the
    existing candidate/dependence checker is derived here. *)
Theorem affine_loaded_body_cached_source fe ge locals temps memory after final :
  affine_loaded_numeric_snapshot pointer proposal (Entry ge locals temps memory) ->
  temps!(affine_proposed_iterator proposal)=Some(Vint Int.zero) ->
  0<=Int.signed(temp_word (affine_proposed_bound proposal) temps) ->
  (forall i, 0<=i<Int.signed(temp_word (affine_proposed_bound proposal) temps) ->
    loaded_body_preserved fe (affine_proposed_iterator proposal) (affine_proposed_bound proposal) pointer
      (affine_proposed_body proposal) (affine_loaded_body_stable parameters proposal pointer) i
      (Entry ge locals temps memory)) ->
  exec_stmt fe ge locals temps memory (affine_loaded_numeric_source pointer proposal) E0 after final Out_normal ->
  exec_stmt fe ge locals temps memory (affine_nest_source(affine_proposal_nest proposal)) E0 after final Out_normal.
Proof.
  intros [block [offset [upper [POINTER [READ CACHE]]]]] ROW NONNEGATIVE PRESERVE SOURCE.
  cbn [entry_temps entry_memory] in POINTER,READ,CACHE.
  destruct (affine_loaded_numeric_body_properties package) as [NORMAL QUIET].
  destruct affine_loaded_body_controls as [ROOT PROTECTED].
  assert (STABLE : forall identifier, In identifier(affine_loaded_body_stable parameters proposal pointer) ->
    ~In identifier(affine_nest_controls(affine_proposed_child proposal))).
  { intros identifier MEMBER BAD; apply(PROTECTED identifier MEMBER).
    cbn [affine_nest_mutated affine_proposal_nest]; right; exact BAD. }
  assert (ROOT_FRESH : ~In (affine_proposed_iterator proposal)(affine_loaded_body_stable parameters proposal pointer)).
  { intro MEMBER; apply(PROTECTED _ MEMBER); cbn [affine_nest_mutated affine_proposal_nest]; left; reflexivity. }
  change (exec_stmt fe ge locals temps memory
    (frontend_counted_loop (affine_proposed_iterator proposal)(affine_proposed_bound proposal)(affine_proposed_body proposal))
    E0 after final Out_normal).
  assert (CACHE_MEMBER : In (affine_proposed_bound proposal)(affine_loaded_body_stable parameters proposal pointer)).
  { left; reflexivity. }
  assert (POINTER_MEMBER : In pointer(affine_loaded_body_stable parameters proposal pointer)).
  { right; left; reflexivity. }
  assert (NN : 0<=Int.signed upper) by (unfold temp_word in NONNEGATIVE; rewrite CACHE in NONNEGATIVE; exact NONNEGATIVE).
  assert (PRESERVE' : forall i, 0<=i<Int.signed upper ->
    loaded_body_preserved fe (affine_proposed_iterator proposal)(affine_proposed_bound proposal) pointer
      (affine_proposed_body proposal)(affine_loaded_body_stable parameters proposal pointer) i (Entry ge locals temps memory)).
  { intros i RANGE; apply PRESERVE; unfold temp_word; rewrite CACHE; exact RANGE. }
  exact (@loaded_body_initial_cached fe ge locals (affine_proposed_iterator proposal)(affine_proposed_bound proposal)
    pointer (affine_proposed_body proposal)(affine_loaded_body_stable parameters proposal pointer)
    (affine_nest_controls(affine_proposed_child proposal)) temps memory block offset upper CACHE POINTER
    CACHE_MEMBER POINTER_MEMBER ROOT_FRESH NORMAL QUIET affine_loaded_body_writes ROOT STABLE NN PRESERVE'
    after final ROW READ SOURCE).
Qed.
End PACKAGE.

Print Assumptions affine_loaded_body_names_sound.
Print Assumptions affine_loaded_body_writes.
Print Assumptions affine_loaded_body_controls.
Print Assumptions affine_loaded_body_memory_back.
Print Assumptions affine_loaded_body_initial_prefix.
Print Assumptions affine_loaded_body_cached_source.
