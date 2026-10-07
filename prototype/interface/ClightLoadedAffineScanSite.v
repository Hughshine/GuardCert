From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap ClightRedundantSet ClightCountedLoop.
From GuardMemory Require Import GuardMemoryBooleanScan GuardMemoryWindowParameterGuard
  GuardMemoryIntervalBox GuardMemoryIntervalGuard.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage
  AffineNestPackageGuard AffineNestStaticPackage AffineNestScanNamespace.
From GuardInterface Require Import ClightSharedGuard ClightMaterializedCheck ClightCheckPlanFrame
  ClightAffineNestMaterialized ClightAffineFirstBodyReceipt ClightLoadedAffineFirstPath
  ClightLoadedAffineNumericGuard ClightLoadedAffineNumericSite ClightLoadedAffineBodyDomain
  ClightLoadedAffineBodyPrefix ClightLoadedAffineRootScan.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition loaded_affine_scan_ports parameters proposal live :=
  affine_single_materialized_ports parameters proposal(affine_proposed_bound proposal::live).
Definition loaded_affine_scan_gate proposal :=
  window_parameters_tree [(0,1);(0,2147483648)]
    [affine_proposed_iterator proposal;affine_proposed_bound proposal](Decision true).
Definition loaded_affine_scan_gate_flag proposal entry :=
  window_parameters_accept [(0,1);(0,2147483648)]
    [affine_proposed_iterator proposal;affine_proposed_bound proposal] entry.
Definition loaded_affine_scan_tail proposal pointer :=
  Sifthenelse(shared_guard_choice(affine_proposed_result proposal))
    (tree_statement(loaded_affine_scan_gate proposal)
      (affine_loaded_root_scan_statement proposal pointer(affine_proposal_rename proposal)(affine_proposed_result proposal))
      (Sset(affine_proposed_result proposal)(Econst_int Int.zero type_int32s))) Sskip.
Definition loaded_affine_scan_body source parameters live proposal pointer
  (numeric : loaded_affine_numeric_site source parameters live proposal pointer) :=
  Ssequence(loaded_numeric_check_code numeric)(loaded_affine_scan_tail proposal pointer).

(* A proposal is still syntax and interval data. This constructor checks all
   additional names, the recursive model, and the concrete dispatch body. *)
Record loaded_affine_scan_site source parameters live proposal pointer := {
  loaded_scan_numeric : loaded_affine_numeric_site source parameters live proposal pointer;
  loaded_scan_pointer_ports : incl(pointer::affine_proposed_pointers proposal) live;
  loaded_scan_body_names : affine_loaded_body_names_check proposal pointer=true;
  loaded_scan_child_code : GuardMemoryLoops.L.stmt;
  loaded_scan_child_lower : affine_loaded_body_model parameters proposal=Some loaded_scan_child_code;
  loaded_scan_namespace : affine_scan_namespace(affine_proposal_nest proposal) parameters
    (loaded_affine_scan_ports parameters proposal live)(affine_proposal_rename proposal)(affine_proposed_result proposal);
  loaded_scan_test : materialized_check;
  loaded_scan_describe : describe_materialized_check(loaded_affine_scan_body loaded_scan_numeric)
    (shared_guard_choice(affine_proposed_result proposal))=Some loaded_scan_test
}.
Definition check_loaded_affine_scan_site source parameters live proposal pointer :
  option(loaded_affine_scan_site source parameters live proposal pointer).
Proof.
  destruct(check_loaded_affine_numeric_site source parameters live proposal pointer) as [numeric|]; [|exact None].
  destruct(affine_names_allocated_check(pointer::affine_proposed_pointers proposal) live) eqn:POINTERS; [|exact None].
  destruct(affine_loaded_body_names_check proposal pointer) eqn:NAMES; [|exact None].
  destruct(affine_loaded_body_model parameters proposal) as [child|] eqn:LOWER; [|exact None].
  destruct(check_affine_scan_namespace(affine_proposal_nest proposal) parameters
    (loaded_affine_scan_ports parameters proposal live)(affine_proposal_rename proposal)(affine_proposed_result proposal))
    as [namespace|]; [|exact None].
  destruct(describe_materialized_check(loaded_affine_scan_body numeric)(shared_guard_choice(affine_proposed_result proposal)))
    as [test|] eqn:DESCRIBE; [|exact None].
  exact(Some {| loaded_scan_numeric:=numeric; loaded_scan_pointer_ports:=@affine_names_allocated_check_sound _ _ POINTERS;
    loaded_scan_body_names:=NAMES; loaded_scan_child_code:=child; loaded_scan_child_lower:=LOWER;
    loaded_scan_namespace:=namespace; loaded_scan_test:=test; loaded_scan_describe:=DESCRIBE |}).
Defined.

Lemma loaded_affine_scan_gate_sound proposal entry :
  register_domain(affine_proposed_iterator proposal) entry ->
  loaded_affine_scan_gate_flag proposal entry=true ->
  (entry_temps entry)!(affine_proposed_iterator proposal)=Some(Vint Int.zero) /\
  0<=Int.signed(temp_word(affine_proposed_bound proposal)(entry_temps entry)).
Proof.
  intros [word WORD] CHECK.
  assert(RANGES:interval_ranges [(0,1);(0,2147483648)]
    (map (fun identifier=>Int.signed(temp_word identifier(entry_temps entry)))
      [affine_proposed_iterator proposal;affine_proposed_bound proposal])).
  { apply(@window_parameters_accept_sound [(0,1);(0,2147483648)]
      [affine_proposed_iterator proposal;affine_proposed_bound proposal] entry); [|exact CHECK].
    assert(ZERO:signed_range 0).
    { unfold signed_range; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia. }
    assert(MAX:signed_range 2147483647).
    { unfold signed_range; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia. }
    constructor; [split; exact ZERO|constructor; [split; [exact ZERO|exact MAX]|constructor]]. }
  inversion RANGES as [|first value rest values ROOT CACHE]; subst.
  inversion CACHE as [|first value rest values COUNT EMPTY]; subst.
  cbn [fst snd] in ROOT,COUNT; split; [|lia].
  unfold temp_word in ROOT; rewrite WORD in ROOT.
  assert(ZERO:Int.signed word=0) by lia.
  rewrite <-Int.repr_signed with(i:=word),ZERO in WORD; exact WORD.
Qed.

Print Assumptions check_loaded_affine_scan_site.
Print Assumptions loaded_affine_scan_gate_sound.
