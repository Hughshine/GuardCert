From Stdlib Require Import List Bool ZArith Lia.
From Guard Require Import ClightRectangularStore ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryCommonLayout GuardMemoryRegistryBackend GuardMemoryLayoutOperations.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition memory_layout_range base shape :=
  rectangle_outer_limit base <= rectangle_outer_limit shape /\ rectangle_stride base <= rectangle_stride shape.
Definition memory_layout_range_check base shape :=
  Z.leb (rectangle_outer_limit base) (rectangle_outer_limit shape) && Z.leb (rectangle_stride base) (rectangle_stride shape).
Lemma memory_layout_range_check_sound base shape :
  memory_layout_range_check base shape = true -> memory_layout_range base shape.
Proof. unfold memory_layout_range_check,memory_layout_range; rewrite andb_true_iff; intros [N M]; apply Z.leb_le in N,M; tauto. Qed.
Definition memory_layout_requests_check base requests :=
  forallb (fun descriptor => rectangle_layout_check (memory_descriptor_shape descriptor) &&
    memory_layout_range_check base (memory_descriptor_shape descriptor)) requests.
Lemma memory_layout_requests_check_sound base requests :
  memory_layout_requests_check base requests = true ->
  Forall (fun descriptor => rectangle_layout_valid (memory_descriptor_shape descriptor) /\
    memory_layout_range base (memory_descriptor_shape descriptor)) requests.
Proof.
  intro CHECK; apply Forall_forall; intros descriptor MEMBER.
  unfold memory_layout_requests_check in CHECK; apply forallb_forall with (x := descriptor) in CHECK; [|exact MEMBER].
  apply andb_true_iff in CHECK as [VALID RANGE]; split.
  - apply rectangle_layout_check_sound; exact VALID.
  - apply memory_layout_range_check_sound; exact RANGE.
Qed.
Lemma memory_layout_request_indices base requests i j :
  rectangle_layout_valid base ->
  Forall (fun descriptor => rectangle_layout_valid (memory_descriptor_shape descriptor) /\
    memory_layout_range base (memory_descriptor_shape descriptor)) requests ->
  0 <= i < rectangle_outer_limit base -> 0 <= j < rectangle_stride base ->
  memory_layout_indices requests i j.
Proof.
  intros VALID REQUESTS I J descriptor MEMBER.
  apply Forall_forall with (x := descriptor) in REQUESTS; [|exact MEMBER].
  destruct REQUESTS as [LAYOUT [N M]].
  pose proof (rectangle_limits VALID) as [_ [_ [POSITIVE LIMIT]]].
  split; [exact LAYOUT|]; split.
  - apply rectangle_point_bound with (N := rectangle_outer_limit base) (M := rectangle_stride base); auto; lia.
  - replace (i*rectangle_stride (memory_descriptor_shape descriptor)) with
      (i*rectangle_stride (memory_descriptor_shape descriptor)+0) by ring.
    apply rectangle_point_bound with (N := rectangle_outer_limit base) (M := rectangle_stride base); auto; lia.
Qed.
Definition propose_memory_layout_common requests :=
  match requests with
  | [] => None
  | first::rest => Some (fold_left (fun base descriptor => memory_common_layout base (memory_descriptor_shape descriptor)) rest (memory_descriptor_shape first))
  end.
Print Assumptions memory_layout_request_indices.
