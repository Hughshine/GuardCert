From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame.
From GuardInterface Require Import ClightCheckPlan ClightCheckPlanFrame ClightAffineLoadedCheckPlan
  ClightAffineDynamicLoadedExamples ClightAffinePointerGuardExamples ClightAffineInnerPointerCandidates.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint check_plan_ifs plan : Z :=
  match plan with
  | PlanDecision _ => 0
  | PlanTest _ yes no => 1+check_plan_ifs yes+check_plan_ifs no
  | PlanAnd first second => 1+check_plan_ifs first+check_plan_ifs second
  end.
Fixpoint check_code_ifs code : Z :=
  match code with
  | Sifthenelse _ yes no => 1+check_code_ifs yes+check_code_ifs no
  | Ssequence first second | Sloop first second => check_code_ifs first+check_code_ifs second
  | Slabel _ body => check_code_ifs body
  | _ => 0
  end.
Theorem check_plan_code_ifs plan result : check_code_ifs (check_plan_code plan result) = check_plan_ifs plan.
Proof. induction plan; cbn [check_code_ifs check_plan_code check_plan_ifs]; lia. Qed.

Definition cp_small_plan fuel := match describe_affine_inner_pointer_at ap_source dl_small_profile with
  | Some package => affine_loaded_stability_plan package dl_bound_pointer fuel 0
  | None => PlanDecision false end.
Example compact_guard_one_row_ifs : check_code_ifs (check_plan_code (cp_small_plan 1%nat) 100%positive) = 11.
Proof. vm_compute; reflexivity. Qed.
Example compact_guard_two_row_ifs : check_code_ifs (check_plan_code (cp_small_plan 2%nat) 100%positive) = 22.
Proof. vm_compute; reflexivity. Qed.
Example compact_guard_three_row_ifs : check_code_ifs (check_plan_code (cp_small_plan 3%nat) 100%positive) = 33.
Proof. vm_compute; reflexivity. Qed.
Example compact_guard_sixty_four_row_syntax_ifs : check_code_ifs (check_plan_code (cp_small_plan 64%nat) 100%positive) = 704.
Proof. vm_compute; reflexivity. Qed.

(** The initial result is absent; a refused first plan skips a tail that reads
    another absent temporary. This is actual Clight execution, with arbitrary
    CompCert memory. No source/candidate runtime is involved in this fixture. *)
Definition cp_refused_plan := PlanAnd (PlanDecision false)
  (PlanTest (Etempvar 200%positive type_int32s) (PlanDecision true) (PlanDecision false)).
Example refused_plan_skips_undefined_tail fe ge locals memory :
  exec_stmt fe ge locals (PTree.empty val) memory (check_plan_code cp_refused_plan 100%positive)
    E0 (PTree.set 100%positive (Vint Int.zero) (PTree.empty val)) memory Out_normal.
Proof.
  eapply (@check_plan_code_execution fe (Entry ge locals (PTree.empty val) memory) cp_refused_plan false).
  - apply plan_run_and_false; constructor.
  - intros [BAD|[]]; discriminate.
  - apply temp_agree_refl.
Qed.
Example private_result_used_by_later_test_refuses :
  check_plan_resources (PlanTest (Etempvar 100%positive type_int32s) (PlanDecision true) (PlanDecision false))
    100%positive [] Sskip Sskip = false.
Proof. vm_compute; reflexivity. Qed.
Example public_result_name_refuses : check_plan_resources (PlanDecision true) 100%positive [100%positive] Sskip Sskip = false.
Proof. vm_compute; reflexivity. Qed.
Example result_used_by_source_refuses : check_plan_resources (PlanDecision true) 100%positive []
  Sskip (Sset 101%positive (Etempvar 100%positive type_int32s)) = false.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions check_plan_code_ifs.
Print Assumptions compact_guard_one_row_ifs.
Print Assumptions compact_guard_two_row_ifs.
Print Assumptions compact_guard_three_row_ifs.
Print Assumptions compact_guard_sixty_four_row_syntax_ifs.
Print Assumptions refused_plan_skips_undefined_tail.
Print Assumptions private_result_used_by_later_test_refuses.
Print Assumptions public_result_name_refuses.
Print Assumptions result_used_by_source_refuses.
