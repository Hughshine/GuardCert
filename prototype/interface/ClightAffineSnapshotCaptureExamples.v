From Stdlib Require Import List.
From GuardInterface Require Import ClightAffineSnapshotSyntaxExamples ClightAffineSnapshotCaptureCandidate.
Import ListNotations.

Definition snapshot_example_capture live :=
  match snapshot_example_describe snapshot_example_source with
  | Some site=>ap_selected(check_affine_snapshot_capture site live)
  | None=>false end.

Example private_two_cache_capture_selected : snapshot_example_capture[]=true.
Proof. vm_compute; reflexivity. Qed.
Example ordinary_public_scope_capture_selected : snapshot_example_capture
  [ap_i;ap_j;ap_k;ap_p;ap_q;ap_a;snapshot_example_N;snapshot_example_M]=true.
Proof. vm_compute; reflexivity. Qed.
Example public_root_cache_refused : snapshot_example_capture[ap_n]=false.
Proof. vm_compute; reflexivity. Qed.
Example public_child_cache_refused : snapshot_example_capture[snapshot_example_cache]=false.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions private_two_cache_capture_selected.
Print Assumptions ordinary_public_scope_capture_selected.
Print Assumptions public_root_cache_refused.
Print Assumptions public_child_cache_refused.
