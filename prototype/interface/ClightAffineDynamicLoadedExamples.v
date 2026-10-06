From Stdlib Require Import List ZArith.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightPureExpr.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightSourceObservation
  ClightAffinePointerGuardExamples ClightAffineInnerPointerCandidateExamples ClightAffineInnerPointerCandidates
  ClightAffineLoadedSourceSyntax ClightAffineDynamicLoadedSyntax ClightAffineLoadedStability.
Import ListNotations.
Local Open Scope Z_scope.

(** Concrete normalized syntax fixtures. They exercise the actual selectors;
    they do not constitute C frontend, extraction, or native execution tests. *)
Definition dl_bound_pointer := 20%positive.
Definition dl_loads := (ap_n,dl_bound_pointer)::ap_loads.
Definition dl_loop := loaded_bound_loop ap_i dl_bound_pointer ap_outer.
Definition dl_source := Ssequence (source_load_prefix dl_loads) dl_loop.

Example independent_bound_source_selected :
  ap_selected (describe_affine_dynamic_loaded_source (fun _ => Some ap_profile) dl_source) = true.
Proof. vm_compute; reflexivity. Qed.
Example old_static_selector_refuses_independent_bound :
  ap_selected (describe_affine_loaded_source (fun _ => Some ap_profile) dl_source) = false.
Proof. vm_compute; reflexivity. Qed.
Example missing_bound_receipt_refuses :
  ap_selected (describe_affine_dynamic_loaded_source (fun _ => Some ap_profile)
    (Ssequence (source_load_prefix ap_loads) dl_loop)) = false.
Proof. vm_compute; reflexivity. Qed.
Example overwritten_bound_pointer_refuses :
  ap_selected (describe_affine_dynamic_loaded_source (fun _ => Some ap_profile)
    (Ssequence (source_load_prefix ((ap_n,dl_bound_pointer)::(dl_bound_pointer,ap_p)::ap_loads)) dl_loop)) = false.
Proof. vm_compute; reflexivity. Qed.
Example bound_pointer_equal_to_iterator_refuses :
  ap_selected (match describe_affine_inner_pointer_at ap_source ap_profile with
    | Some package => check_affine_dynamic_loaded_body (loaded_bound_loop ap_i ap_i ap_outer) package ap_i
    | None => None end) = false.
Proof. vm_compute; reflexivity. Qed.

(** Structural counts of the actual guard syntax, not runtime cost. The
    nested bind duplicates later scans at each accepting inner-scan exit. *)
Fixpoint dl_tests tree : Z :=
  match tree with Decision _ => 0 | Test _ yes no => 1+dl_tests yes+dl_tests no end.
Fixpoint dl_accepting_exits tree : Z :=
  match tree with Decision answer => if answer then 1 else 0
    | Test _ yes no => dl_accepting_exits yes+dl_accepting_exits no end.
Definition dl_small_profile := AffineInnerPointerSourceProfile 2 3 [] [] [] [ap_p;ap_q] 8192.
Definition dl_small_guard fuel := match describe_affine_inner_pointer_at ap_source dl_small_profile with
  | Some package => affine_loaded_stability_tree package dl_bound_pointer fuel 0
  | None => Decision false end.
Example nested_guard_one_row_has_seven_tests : dl_tests (dl_small_guard 1%nat) = 7.
Proof. vm_compute; reflexivity. Qed.
Example nested_guard_two_rows_has_thirty_five_tests : dl_tests (dl_small_guard 2%nat) = 35.
Proof. vm_compute; reflexivity. Qed.
Example nested_guard_two_rows_has_twenty_one_accepting_exits : dl_accepting_exits (dl_small_guard 2%nat) = 21.
Proof. vm_compute; reflexivity. Qed.
Example nested_guard_three_row_syntax_has_one_hundred_forty_seven_tests : dl_tests (dl_small_guard 3%nat) = 147.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions independent_bound_source_selected.
Print Assumptions old_static_selector_refuses_independent_bound.
Print Assumptions missing_bound_receipt_refuses.
Print Assumptions overwritten_bound_pointer_refuses.
Print Assumptions bound_pointer_equal_to_iterator_refuses.
Print Assumptions nested_guard_one_row_has_seven_tests.
Print Assumptions nested_guard_two_rows_has_thirty_five_tests.
Print Assumptions nested_guard_two_rows_has_twenty_one_accepting_exits.
Print Assumptions nested_guard_three_row_syntax_has_one_hundred_forty_seven_tests.
