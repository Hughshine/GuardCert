From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightNoWrap ClightRedundantSet
  ClightSameAddress ClightTempFrame ClightCountedLoop ClightCountedProtocol ClightDecisionRule ClightLoopSyntax ClightRegionProgress
  CompCertMemoryActions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestGuardPackage AffineNestPackageExamples.
From GuardInterface Require Import GuardedRewrite ReadonlyPrefixScan ClightReadonlyRewrite
  ClightConditionComposition ClightReadonlyBranching ClightLoadedBoundSyntax ClightLoadedBodyPrefix
  ClightLoadedBodyTransport ClightLoadedAffineBodyPrefix ClightLoadedAffineNumericExamples ClightLoadedAffineNumericSite
  ClightReadonlyCellSwap ClightWordAddressSeparation ClightIndexedAliasGuard ClightStrictIteration ClightStrictLoopProgress
  ClightDualLoadedUnitSyntax.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Example deep_loaded_body_names_accepted : affine_loaded_body_names_check lnf_proposal 11%positive=true.
Proof. vm_compute; reflexivity. Qed.
Example mutated_loaded_pointer_refused : affine_loaded_body_names_check lnf_proposal 2%positive=false.
Proof. vm_compute; reflexivity. Qed.
Example root_counter_as_pointer_refused : affine_loaded_body_names_check lnf_proposal 1%positive=false.
Proof. vm_compute; reflexivity. Qed.

(** A real source overwrites its own observed bound. With a cached value 2,
    the original executes one iteration and stops at row 1. No non-alias or
    future observation-stability premise is supplied to the guard. *)
Definition lbp_body := loaded_bound_body 3%positive 1%positive.
Definition lbp_stable := [2%positive;3%positive].
Definition lbp_temps block offset := PTree.set 1%positive (Vint Int.zero)
  (PTree.set 2%positive (Vint(Int.repr 2)) (PTree.set 3%positive (Vptr block offset) (PTree.empty val))).
Definition lbp_probe := word_address_separation (signed_pointer_temp 3%positive) 3%positive.
Definition lbp_prefix fe := loaded_body_prefix fe 1%positive 2%positive 3%positive lbp_body lbp_stable (fun _=>True).

Lemma lbp_probe_domain fe i entry : lbp_prefix fe i entry ->
  i<Int.signed(temp_word 2%positive (entry_temps entry)) ->
  word_address_domain (signed_pointer_temp 3%positive) 3%positive entry.
Proof.
  intros INV ACTIVE.
  destruct (@loaded_body_prefix_receipt fe 1%positive 2%positive 3%positive lbp_body lbp_stable (fun _=>True)
    ltac:(cbn; auto) eq_refl eq_refl i entry INV ACTIVE)
    as [block [offset [current [memory [after [final [POINTER [ROW [FRAME [READ [BACK BODY]]]]]]]]]]].
  destruct (loaded_bound_body_store BODY) as [other [base [value [OUT STORE]]]].
  cbn [entry_temps] in OUT.
  rewrite FRAME in OUT by (cbn; auto).
  assert (SAME : Vptr other base=Vptr block offset) by congruence; inversion SAME; subst.
  destruct (@storev_word_facts _ _ _ _ _ STORE) as [[ACCESS BOUND] RAW].
  destruct INV as [_ [_ [_ [initial_block [initial_offset [old [old_memory [last [finish
    [INITIAL_POINTER [INITIAL_READ REST]]]]]]]]]]].
  assert (ADDRESS : Vptr initial_block initial_offset=Vptr block offset) by congruence; inversion ADDRESS; subst.
  exists block,offset,block,offset,(Vint(temp_word 2%positive (entry_temps entry))).
  split; [constructor; exact POINTER|split; [exact POINTER|split; [apply BACK; exact ACCESS|exact INITIAL_READ]]].
Qed.

Lemma lbp_self_separation_impossible entry :
  word_address_separated (signed_pointer_temp 3%positive) 3%positive entry -> False.
Proof.
  intros [block [offset [other [base [EVAL [POINTER APART]]]]]].
  apply scalar_temp_inv in EVAL.
  assert (SAME : Vptr block offset=Vptr other base) by congruence; inversion SAME; subst.
  unfold location_disjoint in APART; cbn in APART; intuition lia.
Qed.

Definition lbp_body_condition fe O (observe : fragment_observation -> O -> Prop) i :
  readonly_condition (readonly_clight_host fe observe)
    (fun entry=>lbp_prefix fe i entry /\ i<Int.signed(temp_word 2%positive (entry_temps entry)))
    (loaded_body_preserved fe 1%positive 2%positive 3%positive lbp_body lbp_stable i) lbp_probe.
Proof.
  eapply readonly_condition_entails.
  - eapply readonly_condition_restrict; [apply word_address_separation_condition; reflexivity|].
    intros entry [INV ACTIVE]; eapply lbp_probe_domain; eassumption.
  - intros entry DOMAIN SEPARATED; exfalso; apply (lbp_self_separation_impossible SEPARATED).
Defined.

Definition lbp_spec fe O (observe : fragment_observation -> O -> Prop) :=
  @loaded_body_prefix_spec fe 1%positive 2%positive 3%positive lbp_body lbp_stable (fun _=>True)
    ltac:(cbn; auto) eq_refl eq_refl [] ltac:(constructor) ltac:(cbn; tauto)
    ltac:(intros identifier MEMBER; cbn; tauto) ltac:(vm_compute; intuition discriminate)
    O observe (fun _=>lbp_probe) (lbp_body_condition fe observe).
Definition lbp_scan fe O (observe : fragment_observation -> O -> Prop) :=
  synthesize_prefix_scan (clight_readonly_check_algebra fe observe)
    (clight_readonly_branch_algebra fe observe) (lbp_spec fe observe) 2 0.

Lemma lbp_probe_refuses fe i entry : lbp_prefix fe i entry ->
  i<Int.signed(temp_word 2%positive (entry_temps entry)) -> decision_run entry lbp_probe false.
Proof.
  intros INV ACTIVE.
  destruct (@lbp_probe_domain fe i entry INV ACTIVE) as [block [offset [other [base [loaded [EVAL [POINTER [ACCESS READ]]]]]]]].
  apply scalar_temp_inv in EVAL.
  assert (SAME : Vptr block offset=Vptr other base) by congruence; inversion SAME; subst.
  assert (EQUALITY : expression_test (word_address_equal (signed_pointer_temp 3%positive) 3%positive) entry true).
  { replace true with (address_flag other base other base) by
      (unfold address_flag; rewrite Pos.eqb_refl,Ptrofs.eq_true; reflexivity).
    eapply word_address_equality_test; [reflexivity|constructor; exact POINTER|exact POINTER|exact ACCESS|exact READ]. }
  unfold lbp_probe,word_address_separation; eapply run_test with(b:=true); [exact EQUALITY|constructor].
Qed.

Section ACTUAL_SOURCE.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variables memory final : mem.
Variable block : block.
Variable offset : ptrofs.
Hypothesis READ : Mem.loadv Mint32 memory (Vptr block offset)=Some(Vint(Int.repr 2)).
Hypothesis STORE : Mem.storev Mint32 memory (Vptr block offset) (Vint Int.one)=Some final.

Lemma lbp_actual_body : exec_stmt fe ge locals (lbp_temps block offset) memory lbp_body
  E0 (lbp_temps block offset) final Out_normal.
Proof.
  unfold lbp_body,loaded_bound_body; eapply exec_Sassign with(loc:=block)(ofs:=offset)(bf:=Full)
    (v2:=Vint Int.one)(v:=Vint Int.one).
  - apply eval_Ederef,eval_Etempvar; reflexivity.
  - eapply eval_Ebinop with(v1:=Vint Int.zero)(v2:=Vint Int.one); [constructor; reflexivity|constructor|reflexivity].
  - reflexivity.
  - apply assign_loc_value with(chunk:=Mint32); [reflexivity|exact STORE].
Qed.

Lemma lbp_actual_source : exec_stmt fe ge locals (lbp_temps block offset) memory
  (loaded_bound_loop 1%positive 3%positive lbp_body) E0
  (PTree.set 1%positive (Vint Int.one) (lbp_temps block offset)) final Out_normal.
Proof.
  assert (FINAL_READ : Mem.loadv Mint32 final (Vptr block offset)=Some(Vint Int.one)).
  { destruct (@storev_word_facts _ _ _ _ _ STORE) as [[ACCESS BOUND] RAW].
    cbn [Mem.loadv]; rewrite zle_true by exact BOUND.
    exact (@Mem.load_store_same Mint32 memory block (Ptrofs.unsigned offset) (Vint Int.one) final RAW). }
  unfold loaded_bound_loop; eapply strict_iteration_encode with(body_temps:=lbp_temps block offset)(body_memory:=final).
  - change true with (Int.lt Int.zero (Int.repr 2)); eapply loaded_bound_test_eval; [reflexivity|reflexivity|exact READ].
  - exists Int.zero; split; [reflexivity|change (0<2147483647)%Z; lia].
  - exact lbp_actual_body.
  - change (exec_stmt fe ge locals (PTree.set 1%positive (Vint Int.one) (lbp_temps block offset)) final
      (strict_frontend_loop 1%positive (loaded_bound_test 1%positive 3%positive) lbp_body) E0
      (PTree.set 1%positive (Vint Int.one) (lbp_temps block offset)) final Out_normal).
    apply strict_zero_trip_encode.
    change false with (Int.lt Int.one Int.one); eapply loaded_bound_test_eval; [apply PTree.gss|reflexivity|exact FINAL_READ].
Qed.

Lemma lbp_initial_receipt : lbp_prefix fe 0 (Entry ge locals (lbp_temps block offset) memory).
Proof.
  eapply loaded_body_prefix_initial with(block:=block)(offset:=offset)
    (after:=PTree.set 1%positive (Vint Int.one) (lbp_temps block offset))(final:=final).
  - exact I.
  - exists (Int.repr 2); reflexivity.
  - change (0<=2)%Z; lia.
  - reflexivity.
  - reflexivity.
  - exact READ.
  - exact lbp_actual_source.
Qed.

Theorem lbp_actual_scan_refuses O (observe : fragment_observation -> O -> Prop) :
  decision_run (Entry ge locals (lbp_temps block offset) memory) (lbp_scan fe observe) false.
Proof.
  unfold lbp_scan; cbn [synthesize_prefix_scan lbp_spec loaded_body_prefix_spec prefix_active_probe
    prefix_point_probe prefix_next loaded_body_active_probe clight_readonly_check_algebra clight_readonly_branch_algebra].
  eapply run_test with(b:=true).
  - pose proof (@indexed_active_test 2%positive 0 (Entry ge locals (lbp_temps block offset) memory)
      ltac:(change (-2147483648<=0<=2147483647)%Z; lia) ltac:(exists(Int.repr 2); reflexivity)) as ACTIVE.
    exact ACTIVE.
  - eapply decision_bind_run with(b:=false); [eapply lbp_probe_refuses; [exact lbp_initial_receipt|change (0<2)%Z; lia]|constructor].
Qed.

(** Actual lowering of the refusing guard leaves public state and memory
    unchanged; both leaves are skip, so no source store is executed here. *)
Theorem lbp_actual_check_executes O (observe : fragment_observation -> O -> Prop) :
  exec_stmt fe ge locals (lbp_temps block offset) memory
    (tree_statement (lbp_scan fe observe) Sskip Sskip) E0 (lbp_temps block offset) memory Out_normal.
Proof.
  change (clight_fragment_run fe (tree_statement (lbp_scan fe observe) Sskip Sskip)
    (Entry ge locals (lbp_temps block offset) memory) (FragmentObservation E0 (lbp_temps block offset) memory Out_normal)).
  apply readonly_tree_execution_exact; exists false; split; [apply lbp_actual_scan_refuses|constructor].
Qed.

Theorem lbp_observation_not_preserved :
  ~loaded_body_preserved fe 1%positive 2%positive 3%positive lbp_body lbp_stable 0
    (Entry ge locals (lbp_temps block offset) memory).
Proof.
  intro PRESERVE.
  pose proof (@PRESERVE block offset (lbp_temps block offset) memory (lbp_temps block offset) final
    eq_refl eq_refl (temp_agree_refl _ _) READ lbp_actual_body) as SAME.
  destruct (@storev_word_facts _ _ _ _ _ STORE) as [[ACCESS BOUND] RAW].
  assert (FINAL_READ : Mem.loadv Mint32 final (Vptr block offset)=Some(Vint Int.one)).
  { cbn [Mem.loadv]; rewrite zle_true by exact BOUND.
    exact (@Mem.load_store_same Mint32 memory block (Ptrofs.unsigned offset) (Vint Int.one) final RAW). }
  rewrite READ,FINAL_READ in SAME; vm_compute in SAME; discriminate.
Qed.
End ACTUAL_SOURCE.

(** Concrete CompCert allocation witnesses both the source execution and the
    source-derived check domain in the alias/refusal example. *)
Definition lbp_two_memory_state :
  {memory | Mem.store Mint32 lnf_allocated 1%positive 0 (Vint(Int.repr 2))=Some memory}.
Proof.
  apply Mem.valid_access_store; eapply Mem.valid_access_implies with(p1:=Freeable); [|constructor].
  eapply Mem.valid_access_alloc_same with(m1:=Mem.empty)(lo:=0)(hi:=4);
    [reflexivity|lia|change (0+4<=4)%Z; lia|change (4|0)%Z; exists 0%Z; reflexivity].
Defined.
Definition lbp_two_memory := proj1_sig lbp_two_memory_state.
Definition lbp_one_memory_state :
  {final | Mem.store Mint32 lbp_two_memory 1%positive 0 (Vint Int.one)=Some final}.
Proof.
  apply Mem.valid_access_store.
  eapply Mem.store_valid_access_1; [exact(proj2_sig lbp_two_memory_state)|].
  eapply Mem.store_valid_access_3; exact(proj2_sig lbp_two_memory_state).
Defined.
Definition lbp_one_memory := proj1_sig lbp_one_memory_state.
Lemma lbp_concrete_read : Mem.loadv Mint32 lbp_two_memory (Vptr 1%positive Ptrofs.zero)=Some(Vint(Int.repr 2)).
Proof.
  change (Mem.load Mint32 lbp_two_memory 1%positive 0=Some(Vint(Int.repr 2))).
  exact (@Mem.load_store_same Mint32 lnf_allocated 1%positive 0 (Vint(Int.repr 2))
    lbp_two_memory (proj2_sig lbp_two_memory_state)).
Qed.
Lemma lbp_concrete_store : Mem.storev Mint32 lbp_two_memory (Vptr 1%positive Ptrofs.zero) (Vint Int.one)=Some lbp_one_memory.
Proof.
  change (Mem.store Mint32 lbp_two_memory 1%positive 0 (Vint Int.one)=Some lbp_one_memory).
  exact(proj2_sig lbp_one_memory_state).
Qed.

Theorem lbp_concrete_source_and_check fe ge locals O (observe : fragment_observation -> O -> Prop) :
  exec_stmt fe ge locals (lbp_temps 1%positive Ptrofs.zero) lbp_two_memory
    (loaded_bound_loop 1%positive 3%positive lbp_body) E0
    (PTree.set 1%positive (Vint Int.one)(lbp_temps 1%positive Ptrofs.zero)) lbp_one_memory Out_normal /\
  decision_run (Entry ge locals (lbp_temps 1%positive Ptrofs.zero) lbp_two_memory) (lbp_scan fe observe) false /\
  exec_stmt fe ge locals (lbp_temps 1%positive Ptrofs.zero) lbp_two_memory
    (tree_statement (lbp_scan fe observe) Sskip Sskip) E0 (lbp_temps 1%positive Ptrofs.zero) lbp_two_memory Out_normal.
Proof.
  split; [exact(@lbp_actual_source fe ge locals _ _ _ _ lbp_concrete_read lbp_concrete_store)|split].
  - exact(@lbp_actual_scan_refuses fe ge locals _ _ _ _ lbp_concrete_read lbp_concrete_store O observe).
  - exact(@lbp_actual_check_executes fe ge locals _ _ _ _ lbp_concrete_read lbp_concrete_store O observe).
Qed.

Theorem deep_empty_cached_source_derived fe ge locals :
  exec_stmt fe ge locals (lnf_ready_empty 1%positive Ptrofs.zero) lnf_zero_memory
    (affine_nest_source(affine_proposal_nest lnf_proposal)) E0
    (lnf_ready_empty 1%positive Ptrofs.zero) lnf_zero_memory Out_normal.
Proof.
  eapply affine_loaded_body_cached_source with(package:=loaded_numeric_package lnf_site)(pointer:=11%positive).
  - exact deep_loaded_body_names_accepted.
  - exists 1%positive,Ptrofs.zero,Int.zero; split; [reflexivity|split; [exact concrete_zero_bound_read|reflexivity]].
  - reflexivity.
  - change (0<=0)%Z; lia.
  - intros i RANGE; change (0<=i<0)%Z in RANGE; lia.
  - exact (@empty_prepared_loaded_source_completes fe ge locals lnf_zero_memory
      1%positive Ptrofs.zero concrete_zero_bound_read).
Qed.

Print Assumptions deep_loaded_body_names_accepted.
Print Assumptions mutated_loaded_pointer_refused.
Print Assumptions root_counter_as_pointer_refused.
Print Assumptions lbp_probe_domain.
Print Assumptions lbp_body_condition.
Print Assumptions lbp_probe_refuses.
Print Assumptions lbp_actual_body.
Print Assumptions lbp_actual_source.
Print Assumptions lbp_initial_receipt.
Print Assumptions lbp_actual_scan_refuses.
Print Assumptions lbp_actual_check_executes.
Print Assumptions lbp_observation_not_preserved.
Print Assumptions lbp_concrete_read.
Print Assumptions lbp_concrete_store.
Print Assumptions lbp_concrete_source_and_check.
Print Assumptions deep_empty_cached_source_derived.
