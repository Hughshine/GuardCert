From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryNaryAffineAccess GuardMemoryNaryCompute
  GuardMemoryAffineSourceExpressions GuardMemoryPointerCompute GuardMemoryPointerAccess GuardMemoryPointerNaryAccess.
From GuardAffineNest Require Import AffineNestSyntax AffineNestGuardPackage AffineNestPackageExamples.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightStrictLoopProgress ClightStableLoopCondition
  ClightLoadedAffineNumericExamples ClightLoadedAffineBodyPrefix ClightLoadedBodyPrefixExamples
  ClightLoadedAffineScanSite ClightLoadedAffineScanExecution ClightLoadedAffineScanCertificate ClightDualLoadedUnitSyntax.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Example recursive_loaded_scan_selected :
  lnf_present(check_loaded_affine_scan_site lnf_source affine_memory_example_parameters lnf_live lnf_proposal 11%positive)=true.
Proof. vm_compute; reflexivity. Qed.
Definition lns_site : loaded_affine_scan_site lnf_source affine_memory_example_parameters lnf_live lnf_proposal 11%positive.
Proof.
  destruct(check_loaded_affine_scan_site lnf_source affine_memory_example_parameters lnf_live lnf_proposal 11%positive)
    as [site|] eqn:CHECK; [exact site|].
  pose proof recursive_loaded_scan_selected as PRESENT; rewrite CHECK in PRESENT; discriminate.
Defined.
Example recursive_missing_pointer_port_refused :
  lnf_present(check_loaded_affine_scan_site lnf_source affine_memory_example_parameters
    [1%positive;2%positive;3%positive;5%positive;6%positive;7%positive;8%positive;9%positive;11%positive]
    lnf_proposal 11%positive)=false.
Proof. vm_compute; reflexivity. Qed.

Theorem concrete_empty_complete_scan_executes fe ge locals : exists after,
  exec_stmt fe ge locals(lnf_empty_temps 1%positive Ptrofs.zero) lnf_zero_memory
    (loaded_affine_scan_body(loaded_scan_numeric lns_site)) E0 after lnf_zero_memory Out_normal /\
  temp_agree lnf_live(lnf_empty_temps 1%positive Ptrofs.zero) after /\
  after!107%positive=Some(Vint Int.zero).
Proof.
  destruct(@loaded_affine_scan_site_execution _ _ _ _ _ lns_site fe ge locals
    (lnf_empty_temps 1%positive Ptrofs.zero) lnf_zero_memory _ _
    (@empty_loaded_source_completes fe ge locals lnf_zero_memory 1%positive Ptrofs.zero concrete_zero_bound_read))
    as [after [RUN [FRAME [FLAG ACCEPT]]]].
  exists after; split; [exact RUN|split; [exact FRAME|]].
  unfold loaded_affine_scan_flag in FLAG; cbn [entry_temps entry_memory] in FLAG.
  change ((lnf_empty_temps 1%positive Ptrofs.zero)!11%positive) with (Some(Vptr 1%positive Ptrofs.zero)) in FLAG.
  cbn -[Mem.loadv] in FLAG.
  rewrite concrete_zero_bound_read in FLAG.
  change (after!107%positive=Some(Vint Int.zero)) in FLAG; exact FLAG.
Qed.

(* A one-word write illustrates the hazard: the original bound can change
   after just one iteration although the captured count says two. *)
Definition lns_access := MemoryNaryAccess 3%positive(RectangleShape 1 1 1 0)
  (MemorySourceConstant 0)([0;0],0).
Definition lns_operation := MemoryNaryCompute lns_access [] (ConstantValue 1)(Econst_int Int.one type_int32s).
Definition lns_body := memory_pointer_compute_statement lns_operation.
Definition lns_proposal := AffineGuardProposal 1%positive 2%positive lns_body(AffineSourceLeaf lns_body)
  [(0,2);(1,3)] 0 1 [3%positive] [lns_operation] [(1,3)] 0 2 [] [101%positive;102%positive] 103%positive.
Definition lns_live := [1%positive;3%positive;11%positive].
Definition lns_source := loaded_bound_loop 1%positive 11%positive lns_body.
Example self_alias_scan_site_selected :
  lnf_present(check_loaded_affine_scan_site lns_source [2%positive] lns_live lns_proposal 11%positive)=true.
Proof. vm_compute; reflexivity. Qed.
Definition lns_alias_site : loaded_affine_scan_site lns_source [2%positive] lns_live lns_proposal 11%positive.
Proof.
  destruct(check_loaded_affine_scan_site lns_source [2%positive] lns_live lns_proposal 11%positive) as [site|] eqn:CHECK;
    [exact site|].
  pose proof self_alias_scan_site_selected as PRESENT; rewrite CHECK in PRESENT; discriminate.
Defined.
Definition lns_alias_temps := PTree.set 1%positive(Vint Int.zero)
  (PTree.set 3%positive(Vptr 1%positive Ptrofs.zero)(PTree.set 11%positive(Vptr 1%positive Ptrofs.zero)(PTree.empty val))).

Lemma self_alias_source_body fe ge locals :
  exec_stmt fe ge locals lns_alias_temps lbp_two_memory lns_body E0 lns_alias_temps lbp_one_memory Out_normal.
Proof.
  unfold lns_body,memory_pointer_compute_statement.
  eapply exec_Sassign with(loc:=1%positive)(ofs:=Ptrofs.zero)(bf:=Full)(v2:=Vint Int.one)(v:=Vint Int.one).
  - change(eval_lvalue ge locals lns_alias_temps lbp_two_memory
      (memory_pointer_lvalue 3%positive(Econst_int Int.zero type_int32s))
      1%positive(Ptrofs.add Ptrofs.zero(Ptrofs.repr(4*0))) Full).
    apply memory_pointer_lvalue_evaluation; [reflexivity|reflexivity|constructor|].
    unfold signed_range; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia.
  - constructor.
  - reflexivity.
  - apply assign_loc_value with(chunk:=Mint32); [reflexivity|exact lbp_concrete_store].
Qed.

Lemma self_alias_original_stops_after_one fe ge locals :
  exec_stmt fe ge locals lns_alias_temps lbp_two_memory lns_source E0
    (PTree.set 1%positive(Vint Int.one) lns_alias_temps) lbp_one_memory Out_normal.
Proof.
  unfold lns_source,loaded_bound_loop.
  eapply strict_iteration_encode with(body_temps:=lns_alias_temps)(body_memory:=lbp_one_memory).
  - change true with(Int.lt Int.zero(Int.repr 2)); eapply loaded_bound_test_eval; [reflexivity|reflexivity|exact lbp_concrete_read].
  - exists Int.zero; split; [reflexivity|change(0<2147483647); lia].
  - apply self_alias_source_body.
  - apply strict_zero_trip_encode.
    change false with(Int.lt Int.one Int.one); eapply loaded_bound_test_eval; [apply PTree.gss|reflexivity|].
    change(Mem.load Mint32 lbp_one_memory 1%positive 0=Some(Vint Int.one)).
    exact(@Mem.load_store_same Mint32 lbp_two_memory 1%positive 0(Vint Int.one) lbp_one_memory(proj2_sig lbp_one_memory_state)).
Qed.

Example self_alias_complete_flag_refuses ge locals :
  loaded_affine_scan_flag [2%positive] lns_proposal 11%positive(Entry ge locals lns_alias_temps lbp_two_memory)=false.
Proof.
  unfold loaded_affine_scan_flag; cbn [entry_temps entry_memory].
  change(lns_alias_temps!11%positive) with(Some(Vptr 1%positive Ptrofs.zero)).
  cbn -[Mem.loadv].
  rewrite lbp_concrete_read; vm_compute; reflexivity.
Qed.

Theorem self_alias_complete_guard_executes fe ge locals : exists after,
  exec_stmt fe ge locals lns_alias_temps lbp_two_memory(loaded_affine_scan_body(loaded_scan_numeric lns_alias_site))
    E0 after lbp_two_memory Out_normal /\
  temp_agree lns_live lns_alias_temps after /\ after!103%positive=Some(Vint Int.zero).
Proof.
  destruct(@loaded_affine_scan_site_execution _ _ _ _ _ lns_alias_site fe ge locals lns_alias_temps lbp_two_memory _ _
    (@self_alias_original_stops_after_one fe ge locals)) as [after [RUN [FRAME [FLAG ACCEPT]]]].
  exists after; split; [exact RUN|split; [exact FRAME|]].
  rewrite self_alias_complete_flag_refuses in FLAG; exact FLAG.
Qed.

Print Assumptions recursive_loaded_scan_selected.
Print Assumptions recursive_missing_pointer_port_refused.
Print Assumptions concrete_empty_complete_scan_executes.
Print Assumptions self_alias_scan_site_selected.
Print Assumptions self_alias_source_body.
Print Assumptions self_alias_original_stops_after_one.
Print Assumptions self_alias_complete_flag_refuses.
Print Assumptions self_alias_complete_guard_executes.
