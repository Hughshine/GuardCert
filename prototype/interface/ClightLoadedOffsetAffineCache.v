From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap ClightFrontendLoopProtocol.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestSourceDecode AffineNestGuardPackage.
From GuardInterface Require Import ClightLoadedOffsetHeader ClightLoadedOffsetAffineBody
  ClightLoadedAffineNumericGuard ClightLoadedAffineBodyPrefix.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Accepted preservation of actual header observations derives execution of
    the cached mathematical source. Cached execution is not a scan input. *)
Theorem offset_affine_body_cached_source source parameters live proposal
  (package : affine_guard_package source parameters live proposal) pointer delta fe ge locals temps memory after final :
  affine_loaded_body_names_check proposal pointer=true ->
  loaded_offset_cached_header pointer delta(affine_proposed_bound proposal)(Entry ge locals temps memory) ->
  temps!(affine_proposed_iterator proposal)=Some(Vint Int.zero) ->
  0<=Int.signed(temp_word(affine_proposed_bound proposal) temps) ->
  (forall i, 0<=i<Int.signed(temp_word(affine_proposed_bound proposal) temps) ->
    offset_affine_body_preserved fe parameters proposal pointer i(Entry ge locals temps memory)) ->
  exec_stmt fe ge locals temps memory(loaded_offset_loop(affine_proposed_iterator proposal) pointer delta
    (affine_proposed_body proposal)) E0 after final Out_normal ->
  exec_stmt fe ge locals temps memory(affine_nest_source(affine_proposal_nest proposal)) E0 after final Out_normal.
Proof.
  intros NAMES SNAPSHOT ROW NONNEGATIVE PRESERVE SOURCE.
  destruct(affine_loaded_numeric_body_properties package) as [NORMAL QUIET].
  destruct(@affine_loaded_body_controls source parameters live proposal package pointer NAMES) as [ROOT PROTECTED].
  assert(STABLE:forall identifier, In identifier(affine_loaded_body_stable parameters proposal pointer) ->
    ~In identifier(affine_nest_controls(affine_proposed_child proposal))).
  { intros identifier MEMBER BAD; apply(PROTECTED identifier MEMBER).
    cbn [affine_nest_mutated affine_proposal_nest]; right; exact BAD. }
  assert(ROOT_FRESH:~In(affine_proposed_iterator proposal)(affine_loaded_body_stable parameters proposal pointer)).
  { intro MEMBER; apply(PROTECTED _ MEMBER); cbn [affine_nest_mutated affine_proposal_nest]; left; reflexivity. }
  change(exec_stmt fe ge locals temps memory
    (frontend_counted_loop(affine_proposed_iterator proposal)(affine_proposed_bound proposal)(affine_proposed_body proposal))
    E0 after final Out_normal).
  eapply loaded_offset_body_initial_cached with(stable:=affine_loaded_body_stable parameters proposal pointer)
    (written:=affine_nest_controls(affine_proposed_child proposal));
    [right; left; reflexivity|left; reflexivity|exact ROOT_FRESH|exact NORMAL|exact QUIET|
     exact(affine_loaded_body_writes package)|exact ROOT|exact STABLE|exact SNAPSHOT|exact NONNEGATIVE|exact ROW| |exact SOURCE].
  intros i current before exit last RANGE CURRENT FRAME OBSERVED RUN.
  exact(@PRESERVE i RANGE current before exit last CURRENT FRAME OBSERVED RUN).
Qed.

Print Assumptions offset_affine_body_cached_source.
