From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryPointerAccess GuardMemoryPointerCompute.
From GuardAffineNest Require Import AffineNestSyntax AffineNestGuardPackage.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightStrictLoopProgress ClightDualLoadedUnitSyntax
  ClightLoadedAffineScanSite ClightLoadedAffineScanExecution ClightLoadedAffineScanCertificate ClightLoadedAffineScanExamples.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition lns_eight_bytes := fst(Mem.alloc Mem.empty 0 8).
Lemma lns_allocated_word offset : 0<=offset -> offset+4<=8 -> (4|offset) ->
  Mem.valid_access lns_eight_bytes Mint32 1%positive offset Writable.
Proof.
  intros LOW HIGH ALIGN; eapply Mem.valid_access_implies with(p1:=Freeable); [|constructor].
  eapply Mem.valid_access_alloc_same with(m1:=Mem.empty)(lo:=0)(hi:=8);
    [reflexivity|exact LOW|exact HIGH|exact ALIGN].
Qed.
Definition lns_initial_state : {memory | Mem.store Mint32 lns_eight_bytes 1%positive 0(Vint(Int.repr 2))=Some memory}.
Proof. apply Mem.valid_access_store,lns_allocated_word; [lia|lia|exists 0; reflexivity]. Defined.
Definition lns_initial := proj1_sig lns_initial_state.
Definition lns_first_state : {memory | Mem.store Mint32 lns_initial 1%positive 4(Vint Int.one)=Some memory}.
Proof.
  apply Mem.valid_access_store; eapply Mem.store_valid_access_1; [exact(proj2_sig lns_initial_state)|].
  apply lns_allocated_word; [lia|lia|exists 1; reflexivity].
Defined.
Definition lns_first := proj1_sig lns_first_state.
Definition lns_last_state : {memory | Mem.store Mint32 lns_first 1%positive 4(Vint Int.one)=Some memory}.
Proof.
  apply Mem.valid_access_store; eapply Mem.store_valid_access_1; [exact(proj2_sig lns_first_state)|].
  eapply Mem.store_valid_access_3; exact(proj2_sig lns_first_state).
Defined.
Definition lns_last := proj1_sig lns_last_state.
Definition lns_separate_temps := PTree.set 1%positive(Vint Int.zero)
  (PTree.set 3%positive(Vptr 1%positive(Ptrofs.repr 4))
    (PTree.set 11%positive(Vptr 1%positive Ptrofs.zero)(PTree.empty val))).

Lemma same_block_bound_reads :
  Mem.loadv Mint32 lns_initial(Vptr 1%positive Ptrofs.zero)=Some(Vint(Int.repr 2)) /\
  Mem.loadv Mint32 lns_first(Vptr 1%positive Ptrofs.zero)=Some(Vint(Int.repr 2)) /\
  Mem.loadv Mint32 lns_last(Vptr 1%positive Ptrofs.zero)=Some(Vint(Int.repr 2)).
Proof.
  change(Mem.load Mint32 lns_initial 1%positive 0=Some(Vint(Int.repr 2)) /\
    Mem.load Mint32 lns_first 1%positive 0=Some(Vint(Int.repr 2)) /\
    Mem.load Mint32 lns_last 1%positive 0=Some(Vint(Int.repr 2))).
  rewrite(@Mem.load_store_other Mint32 lns_first 1%positive 4(Vint Int.one) lns_last(proj2_sig lns_last_state)
    Mint32 1%positive 0 ltac:(right; left; change(0+4<=4); lia)),
    (@Mem.load_store_other Mint32 lns_initial 1%positive 4(Vint Int.one) lns_first(proj2_sig lns_first_state)
    Mint32 1%positive 0 ltac:(right; left; change(0+4<=4); lia)),
    (@Mem.load_store_same Mint32 lns_eight_bytes 1%positive 0(Vint(Int.repr 2)) lns_initial(proj2_sig lns_initial_state)).
  repeat split; reflexivity.
Qed.

Lemma same_block_constant_body fe ge locals temps memory final :
  temps!3%positive=Some(Vptr 1%positive(Ptrofs.repr 4)) ->
  Mem.store Mint32 memory 1%positive 4(Vint Int.one)=Some final ->
  exec_stmt fe ge locals temps memory lns_body E0 temps final Out_normal.
Proof.
  intros POINTER STORE; unfold lns_body,memory_pointer_compute_statement.
  eapply exec_Sassign with(loc:=1%positive)(ofs:=Ptrofs.repr 4)(bf:=Full)(v2:=Vint Int.one)(v:=Vint Int.one).
  - change(eval_lvalue ge locals temps memory(memory_pointer_lvalue 3%positive(Econst_int Int.zero type_int32s))
      1%positive(Ptrofs.add(Ptrofs.repr 4)(Ptrofs.repr(4*0))) Full).
    apply memory_pointer_lvalue_evaluation; [exact POINTER|reflexivity|constructor|].
    unfold signed_range; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia.
  - constructor.
  - reflexivity.
  - apply assign_loc_value with(chunk:=Mint32); [reflexivity|change(Mem.store Mint32 memory 1%positive 4(Vint Int.one)=Some final); exact STORE].
Qed.

Lemma same_block_original_completes fe ge locals :
  exec_stmt fe ge locals lns_separate_temps lns_initial lns_source E0
    (PTree.set 1%positive(Vint(Int.repr 2))(PTree.set 1%positive(Vint Int.one) lns_separate_temps)) lns_last Out_normal.
Proof.
  destruct same_block_bound_reads as [READ [FIRST_READ LAST_READ]].
  unfold lns_source,loaded_bound_loop.
  eapply strict_iteration_encode with(body_temps:=lns_separate_temps)(body_memory:=lns_first).
  - change true with(Int.lt Int.zero(Int.repr 2)); eapply loaded_bound_test_eval; [reflexivity|reflexivity|exact READ].
  - exists Int.zero; split; [reflexivity|change(0<2147483647); lia].
  - apply same_block_constant_body; [reflexivity|exact(proj2_sig lns_first_state)].
  - change(exec_stmt fe ge locals(PTree.set 1%positive(Vint Int.one) lns_separate_temps) lns_first
      (strict_frontend_loop 1%positive(loaded_bound_test 1%positive 11%positive) lns_body) E0
      (PTree.set 1%positive(Vint(Int.repr 2))(PTree.set 1%positive(Vint Int.one) lns_separate_temps)) lns_last Out_normal).
    eapply strict_iteration_encode with(body_temps:=PTree.set 1%positive(Vint Int.one) lns_separate_temps)(body_memory:=lns_last).
    + change true with(Int.lt Int.one(Int.repr 2)); eapply loaded_bound_test_eval; [apply PTree.gss|reflexivity|exact FIRST_READ].
    + exists Int.one; split; [apply PTree.gss|change(1<2147483647); lia].
    + apply same_block_constant_body; [reflexivity|exact(proj2_sig lns_last_state)].
    + apply strict_zero_trip_encode; change false with(Int.lt(Int.repr 2)(Int.repr 2)).
      eapply loaded_bound_test_eval; [apply PTree.gss|reflexivity|exact LAST_READ].
Qed.

Example same_block_nonoverlap_flag_accepts ge locals :
  loaded_affine_scan_flag [2%positive] lns_proposal 11%positive(Entry ge locals lns_separate_temps lns_initial)=true.
Proof.
  unfold loaded_affine_scan_flag; cbn [entry_temps entry_memory].
  change(lns_separate_temps!11%positive) with(Some(Vptr 1%positive Ptrofs.zero)); cbn -[Mem.loadv].
  rewrite(proj1 same_block_bound_reads); vm_compute; reflexivity.
Qed.

Theorem same_block_complete_guard_accepts fe ge locals : exists after,
  exec_stmt fe ge locals lns_separate_temps lns_initial(loaded_affine_scan_body(loaded_scan_numeric lns_alias_site))
    E0 after lns_initial Out_normal /\
  temp_agree lns_live lns_separate_temps after /\ after!103%positive=Some(Vint Int.one) /\
  loaded_affine_scan_presumption fe [2%positive] lns_proposal 11%positive(Entry ge locals lns_separate_temps lns_initial).
Proof.
  destruct(@loaded_affine_scan_site_execution _ _ _ _ _ lns_alias_site fe ge locals lns_separate_temps lns_initial _ _
    (@same_block_original_completes fe ge locals)) as [after [RUN [FRAME [FLAG ACCEPT]]]].
  exists after; split; [exact RUN|split; [exact FRAME|split]].
  - rewrite same_block_nonoverlap_flag_accepts in FLAG; exact FLAG.
  - apply ACCEPT; apply same_block_nonoverlap_flag_accepts.
Qed.

Theorem same_block_cached_source_is_derived fe ge locals : exists upper cached_after,
  exec_stmt fe ge locals(PTree.set 2%positive(Vint upper) lns_separate_temps) lns_initial
    (affine_nest_source(affine_proposal_nest lns_proposal)) E0 cached_after lns_last Out_normal /\
  temp_agree lns_live
    (PTree.set 1%positive(Vint(Int.repr 2))(PTree.set 1%positive(Vint Int.one) lns_separate_temps)) cached_after.
Proof.
  destruct(@same_block_complete_guard_accepts fe ge locals) as [after [RUN [FRAME [FLAG PREMISE]]]].
  exact(@loaded_affine_scan_presumption_cached_source _ _ _ _ _ lns_alias_site fe ge locals lns_separate_temps lns_initial
    _ _ PREMISE(@same_block_original_completes fe ge locals)).
Qed.

Print Assumptions same_block_bound_reads.
Print Assumptions same_block_original_completes.
Print Assumptions same_block_nonoverlap_flag_accepts.
Print Assumptions same_block_complete_guard_accepts.
Print Assumptions same_block_cached_source_is_derived.
