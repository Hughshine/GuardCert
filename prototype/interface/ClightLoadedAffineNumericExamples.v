From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame.
From GuardAffineNest Require Import AffineNestGuardPackage AffineNestPackageGuard AffineNestPackageExamples AffineNestDomainGuard.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightLoadedAffineFirstPath
  ClightLoadedAffineNumericGuard ClightLoadedAffineNumericSite ClightMaterializedCheck ClightAffineNestMaterialized.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition lnf_proposal := affine_memory_example_proposal
  [101%positive;104%positive;102%positive;105%positive;103%positive;106%positive] 107%positive.
Definition lnf_live := [1%positive;2%positive;3%positive;5%positive;6%positive;7%positive;
  8%positive;9%positive;10%positive;11%positive].
Definition lnf_source := affine_loaded_numeric_source 11%positive lnf_proposal.
Definition lnf_present {A : Type} (value : option A) := match value with Some _=>true|None=>false end.
Definition lnf_describe source live :=
  check_loaded_affine_numeric_site source affine_memory_example_parameters live lnf_proposal 11%positive.

Example three_level_loaded_numeric_site_selected : lnf_present (lnf_describe lnf_source lnf_live)=true.
Proof. vm_compute; reflexivity. Qed.
Example private_cache_cannot_be_public : lnf_present (lnf_describe lnf_source (4%positive::lnf_live))=false.
Proof. vm_compute; reflexivity. Qed.
Example cached_ast_cannot_replace_loaded_source_key :
  lnf_present (lnf_describe affine_memory_example_source lnf_live)=false.
Proof. vm_compute; reflexivity. Qed.
Example wrong_body_refused :
  lnf_present (lnf_describe (loaded_bound_loop 1%positive 11%positive Sskip) lnf_live)=false.
Proof. vm_compute; reflexivity. Qed.

Definition lnf_site : loaded_affine_numeric_site lnf_source affine_memory_example_parameters lnf_live lnf_proposal 11%positive.
Proof.
  destruct (lnf_describe lnf_source lnf_live) as [site|] eqn:SELECT; [exact site|].
  pose proof three_level_loaded_numeric_site_selected as PRESENT; rewrite SELECT in PRESENT; discriminate.
Defined.

Definition lnf_empty_temps block offset :=
  PTree.set 11%positive (Vptr block offset) (PTree.set 1%positive (Vint Int.zero) (PTree.empty val)).
Definition lnf_ready_empty block offset := PTree.set 4%positive (Vint Int.zero) (lnf_empty_temps block offset).
Definition lnf_active_temps := PTree.set 1%positive (Vint Int.zero)
  (PTree.set 4%positive (Vint (Int.repr 2)) (PTree.set 7%positive (Vint Int.one)
    (PTree.set 8%positive (Vint Int.one) (PTree.set 9%positive (Vint Int.zero) (PTree.empty val))))).

(** This only tests the numeric condition. It does not assert stable memory,
    candidate correctness, or availability of future body accesses. *)
Example nonempty_numeric_flag_accepts ge locals memory :
  affine_package_guard_flag affine_memory_example_parameters lnf_proposal
    (Entry ge locals lnf_active_temps memory)=true.
Proof. vm_compute; reflexivity. Qed.
Example empty_numeric_flag_refuses ge locals memory block offset :
  affine_package_guard_flag affine_memory_example_parameters lnf_proposal
    (Entry ge locals (lnf_ready_empty block offset) memory)=false.
Proof. vm_compute; reflexivity. Qed.

Section EMPTY_EXECUTION.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable memory : mem.
Variable block : block.
Variable offset : ptrofs.
Hypothesis READ : Mem.loadv Mint32 memory (Vptr block offset)=Some(Vint Int.zero).

Lemma empty_loaded_source_completes :
  exec_stmt fe ge locals (lnf_empty_temps block offset) memory lnf_source
    E0 (lnf_empty_temps block offset) memory Out_normal.
Proof.
  apply loaded_bound_zero_trip_execution.
  change (expression_test (loaded_bound_test 1%positive 11%positive)
    (Entry ge locals (lnf_empty_temps block offset) memory) (Int.lt Int.zero Int.zero)).
  eapply loaded_bound_test_eval; [reflexivity|reflexivity|exact READ].
Qed.

Lemma empty_prepared_loaded_source_completes :
  exec_stmt fe ge locals (lnf_ready_empty block offset) memory lnf_source
    E0 (lnf_ready_empty block offset) memory Out_normal.
Proof.
  apply loaded_bound_zero_trip_execution.
  change (expression_test (loaded_bound_test 1%positive 11%positive)
    (Entry ge locals (lnf_ready_empty block offset) memory) (Int.lt Int.zero Int.zero)).
  eapply loaded_bound_test_eval; [reflexivity|reflexivity|exact READ].
Qed.

(** The real Clight check completes with missing child-bound parameters,
    missing scalar data and no body pointer. Only the real source header is
    read. Memory and public temps are preserved; the guard refuses. *)
Theorem empty_loaded_capture_and_check_execute : exists checked,
  exec_stmt fe ge locals (lnf_empty_temps block offset) memory (loaded_numeric_check_code lnf_site)
    E0 checked memory Out_normal /\
  temp_agree lnf_live (lnf_empty_temps block offset) checked /\
  checked!4%positive=Some(Vint Int.zero) /\ checked!107%positive=Some(Vint Int.zero) /\
  checked!7%positive=None /\ checked!8%positive=None /\ checked!9%positive=None /\ checked!10%positive=None.
Proof.
  destruct (affine_loaded_numeric_body_properties (loaded_numeric_package lnf_site)) as [NORMAL QUIET].
  pose proof (@loaded_affine_first_body_receipt fe ge locals (lnf_ready_empty block offset) memory
    1%positive 11%positive 4%positive (affine_proposed_body lnf_proposal)
    (lnf_ready_empty block offset) memory block offset Int.zero NORMAL QUIET
    eq_refl READ eq_refl empty_prepared_loaded_source_completes) as RECEIPT.
  destruct (@affine_receipted_package_guard_execution _ _ _ _ (loaded_numeric_package lnf_site)
    fe ge locals (lnf_ready_empty block offset) memory RECEIPT) as [checked [GUARD [FRAME [RESULT MATH]]]].
  destruct (@describe_materialized_check_exact _ _ _ (loaded_numeric_describe lnf_site)) as [BODY COND].
  rewrite empty_numeric_flag_refuses in RESULT.
  assert (PUBLIC : temp_agree lnf_live (lnf_ready_empty block offset) checked).
  { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER;
      unfold affine_single_materialized_ports; apply in_or_app; right; apply in_or_app; right; cbn; auto. }
  exists checked; split.
  - unfold loaded_numeric_check_code; rewrite BODY.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [|exact GUARD].
    constructor; apply eval_Elvalue with (loc:=block) (ofs:=offset) (bf:=Full).
    + apply eval_Ederef,eval_Etempvar; reflexivity.
    + apply deref_loc_value with (chunk:=Mint32); [reflexivity|exact READ].
  - split.
    + eapply temp_agree_trans with (le1:=lnf_ready_empty block offset);
        [apply temp_agree_set; vm_compute; intuition discriminate|exact PUBLIC].
    + split.
      * rewrite FRAME; [reflexivity|unfold affine_single_materialized_ports;
          apply in_or_app; right; apply in_or_app; left; cbn; auto].
      * split; [exact RESULT|].
        rewrite (PUBLIC 7%positive ltac:(vm_compute; intuition congruence)),
          (PUBLIC 8%positive ltac:(vm_compute; intuition congruence)),
          (PUBLIC 9%positive ltac:(vm_compute; intuition congruence)),
          (PUBLIC 10%positive ltac:(vm_compute; intuition congruence)); repeat split; reflexivity.
Qed.
End EMPTY_EXECUTION.

(** A concrete one-word allocation witnesses the execution domain; the
    preceding zero-trip theorem is not relying on an unrealizable read. *)
Definition lnf_allocated := fst (Mem.alloc Mem.empty 0 4).
Definition lnf_zero_memory_state :
  {memory | Mem.store Mint32 lnf_allocated 1%positive 0 (Vint Int.zero)=Some memory}.
Proof.
  apply Mem.valid_access_store; eapply Mem.valid_access_implies with (p1:=Freeable); [|constructor].
  eapply Mem.valid_access_alloc_same with (m1:=Mem.empty) (lo:=0) (hi:=4);
    [reflexivity|lia|change (0+4<=4)%Z; lia|change (4|0)%Z; exists 0%Z; reflexivity].
Defined.
Definition lnf_zero_memory := proj1_sig lnf_zero_memory_state.
Lemma concrete_zero_bound_read :
  Mem.loadv Mint32 lnf_zero_memory (Vptr 1%positive Ptrofs.zero)=Some(Vint Int.zero).
Proof.
  change (Mem.load Mint32 lnf_zero_memory 1%positive 0=Some(Vint Int.zero)).
  exact (@Mem.load_store_same Mint32 lnf_allocated 1%positive 0 (Vint Int.zero)
    lnf_zero_memory (proj2_sig lnf_zero_memory_state)).
Qed.

Theorem concrete_empty_loaded_check_executes fe ge locals : exists checked,
  exec_stmt fe ge locals (lnf_empty_temps 1%positive Ptrofs.zero) lnf_zero_memory
    (loaded_numeric_check_code lnf_site) E0 checked lnf_zero_memory Out_normal /\
  temp_agree lnf_live (lnf_empty_temps 1%positive Ptrofs.zero) checked /\
  checked!4%positive=Some(Vint Int.zero) /\ checked!107%positive=Some(Vint Int.zero) /\
  checked!7%positive=None /\ checked!8%positive=None /\ checked!9%positive=None /\ checked!10%positive=None.
Proof. exact (@empty_loaded_capture_and_check_execute fe ge locals lnf_zero_memory
  1%positive Ptrofs.zero concrete_zero_bound_read). Qed.

Print Assumptions three_level_loaded_numeric_site_selected.
Print Assumptions private_cache_cannot_be_public.
Print Assumptions cached_ast_cannot_replace_loaded_source_key.
Print Assumptions wrong_body_refused.
Print Assumptions nonempty_numeric_flag_accepts.
Print Assumptions empty_numeric_flag_refuses.
Print Assumptions empty_loaded_source_completes.
Print Assumptions empty_prepared_loaded_source_completes.
Print Assumptions empty_loaded_capture_and_check_execute.
Print Assumptions concrete_zero_bound_read.
Print Assumptions concrete_empty_loaded_check_executes.
