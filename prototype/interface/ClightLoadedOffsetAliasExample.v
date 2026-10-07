From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightNoWrap ClightCountedLoop
  CompCertMemoryActions ClightRegionProgress.
From GuardMemory Require Import GuardMemoryPointerCompute GuardMemoryPointerAccess.
From GuardInterface Require Import ClightLoadedOffsetHeader ClightExpressionHeaderCapture
  ClightSignedExpressionProgress ClightStrictLoopProgress ClightDualLoadedUnitSyntax ClightObservedHeaderPrefix
  ClightLoadedBodyPrefixExamples ClightLoadedAffineScanExamples ClightCheckPlanFrame.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** *limit is initially 2, so the captured upper is 3. Each source body
    stores 1 through an alias of limit. The actual repeated-plus-one header
    therefore stops at row 2. Capturing its first value alone is insufficient. *)
Definition loa_source := loaded_offset_loop 1%positive 11%positive Int.one lns_body.
Definition loa_second_state : {final | Mem.store Mint32 lbp_one_memory 1%positive 0(Vint Int.one)=Some final}.
Proof.
  apply Mem.valid_access_store.
  eapply Mem.store_valid_access_1; [exact(proj2_sig lbp_one_memory_state)|].
  eapply Mem.store_valid_access_3; exact(proj2_sig lbp_one_memory_state).
Defined.
Definition loa_final := proj1_sig loa_second_state.
Definition loa_exit := PTree.set 1%positive (Vint(Int.repr 2)) (PTree.set 1%positive (Vint Int.one) lns_alias_temps).

Lemma loa_after_first_read : Mem.loadv Mint32 lbp_one_memory(Vptr 1%positive Ptrofs.zero)=Some(Vint Int.one).
Proof.
  change (Mem.load Mint32 lbp_one_memory 1%positive 0=Some(Vint Int.one)).
  exact (@Mem.load_store_same Mint32 lbp_two_memory 1%positive 0(Vint Int.one)
    lbp_one_memory(proj2_sig lbp_one_memory_state)).
Qed.
Lemma loa_final_read : Mem.loadv Mint32 loa_final(Vptr 1%positive Ptrofs.zero)=Some(Vint Int.one).
Proof.
  change (Mem.load Mint32 loa_final 1%positive 0=Some(Vint Int.one)).
  exact (@Mem.load_store_same Mint32 lbp_one_memory 1%positive 0(Vint Int.one) loa_final(proj2_sig loa_second_state)).
Qed.

Lemma loa_second_body fe ge locals :
  exec_stmt fe ge locals (PTree.set 1%positive(Vint Int.one) lns_alias_temps) lbp_one_memory lns_body
    E0 (PTree.set 1%positive(Vint Int.one) lns_alias_temps) loa_final Out_normal.
Proof.
  unfold lns_body,memory_pointer_compute_statement.
  eapply exec_Sassign with(loc:=1%positive)(ofs:=Ptrofs.zero)(bf:=Full)(v2:=Vint Int.one)(v:=Vint Int.one).
  - change (eval_lvalue ge locals (PTree.set 1%positive(Vint Int.one) lns_alias_temps) lbp_one_memory
      (memory_pointer_lvalue 3%positive(Econst_int Int.zero type_int32s))
      1%positive(Ptrofs.add Ptrofs.zero(Ptrofs.repr(4*0))) Full).
    apply memory_pointer_lvalue_evaluation; [reflexivity|reflexivity|constructor|].
    unfold signed_range; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia.
  - constructor.
  - reflexivity.
  - apply assign_loc_value with(chunk:=Mint32); [reflexivity|exact(proj2_sig loa_second_state)].
Qed.

Theorem offset_alias_original_stops_after_two fe ge locals :
  exec_stmt fe ge locals lns_alias_temps lbp_two_memory loa_source E0 loa_exit loa_final Out_normal.
Proof.
  unfold loa_source,loaded_offset_loop,loa_exit.
  eapply strict_iteration_encode with(body_temps:=lns_alias_temps)(body_memory:=lbp_one_memory).
  - change true with(Int.lt Int.zero(Int.add(Int.repr 2) Int.one)).
    eapply signed_expression_test_eval; [reflexivity|reflexivity|].
    eapply signed_load_offset_eval; [reflexivity|exact lbp_concrete_read].
  - exists Int.zero; split; [reflexivity|change(0<2147483647); lia].
  - apply self_alias_source_body.
  - change (exec_stmt fe ge locals (PTree.set 1%positive(Vint Int.one) lns_alias_temps) lbp_one_memory
      (loaded_offset_loop 1%positive 11%positive Int.one lns_body) E0
      (PTree.set 1%positive(Vint(Int.repr 2))(PTree.set 1%positive(Vint Int.one) lns_alias_temps)) loa_final Out_normal).
    unfold loaded_offset_loop; eapply strict_iteration_encode with
      (body_temps:=PTree.set 1%positive(Vint Int.one) lns_alias_temps)(body_memory:=loa_final).
    + change true with(Int.lt Int.one(Int.add Int.one Int.one)).
      eapply signed_expression_test_eval; [reflexivity|apply PTree.gss|].
      eapply signed_load_offset_eval; [reflexivity|exact loa_after_first_read].
    + exists Int.one; split; [apply PTree.gss|change(1<2147483647); lia].
    + apply loa_second_body.
    + apply signed_expression_zero_trip_execution.
      change false with(Int.lt(Int.repr 2)(Int.add Int.one Int.one)).
      eapply signed_expression_test_eval; [reflexivity|apply PTree.gss|].
      eapply signed_load_offset_eval; [reflexivity|exact loa_final_read].
Qed.

Theorem offset_alias_initial_raw_and_cached_words_differ ge locals :
  loaded_offset_cached_header 11%positive Int.one 2%positive
    (Entry ge locals (PTree.set 2%positive(Vint(Int.repr 3)) lns_alias_temps) lbp_two_memory) /\
  Mem.loadv Mint32 lbp_two_memory(Vptr 1%positive Ptrofs.zero)=Some(Vint(Int.repr 2)).
Proof.
  split; [exists 1%positive,Ptrofs.zero,(Int.repr 2); split; [reflexivity|split; [exact lbp_concrete_read|reflexivity]]|
    exact lbp_concrete_read].
Qed.

Theorem offset_alias_header_observation_changes ge locals :
  ~header_observations_match (loaded_offset_observations 11%positive(Entry ge locals lns_alias_temps lbp_two_memory)) lbp_one_memory.
Proof.
  unfold loaded_offset_observations; cbn [entry_temps entry_memory].
  change (lns_alias_temps!11%positive) with(Some(Vptr 1%positive Ptrofs.zero)).
  cbn -[Mem.loadv].
  rewrite lbp_concrete_read; intro OBSERVED; inversion OBSERVED as [|first rest READ REST]; subst.
  change (Mem.load Mint32 lbp_one_memory 1%positive 0=Some(Vint(Int.repr 2))) in READ.
  pose proof loa_after_first_read as VALUE.
  change (Mem.load Mint32 lbp_one_memory 1%positive 0=Some(Vint Int.one)) in VALUE.
  rewrite VALUE in READ; vm_compute in READ; discriminate.
Qed.

Print Assumptions loa_after_first_read.
Print Assumptions loa_final_read.
Print Assumptions loa_second_body.
Print Assumptions offset_alias_original_stops_after_two.
Print Assumptions offset_alias_initial_raw_and_cached_words_differ.
Print Assumptions offset_alias_header_observation_changes.
