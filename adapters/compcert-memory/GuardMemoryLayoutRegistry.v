From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightRectangularStore.
From GuardMemory Require Import GuardMemoryMultipleArrays GuardMemoryRegistryBackend
  GuardMemoryCopyLayoutRegistry.
Import ListNotations.
Set Implicit Arguments.

(** A descriptor identifies an object; strides belong to the access functions.
    Repeated requests for an object can use different strides but must agree on
    its C array type and extent. *)
Definition memory_descriptor_for array shape descriptor :=
  memory_descriptor_id descriptor = array /\ memory_descriptor_variable descriptor = array /\
    rectangle_extent (memory_descriptor_shape descriptor) = rectangle_extent shape.
Definition memory_descriptors_cover descriptors requests :=
  Forall (fun request => exists descriptor, In descriptor descriptors /\
    memory_descriptor_for (memory_descriptor_id request) (memory_descriptor_shape request) descriptor) requests.
Fixpoint memory_unique_descriptors requests :=
  match requests with
  | [] => []
  | first::rest => first::filter (fun descriptor => negb (Pos.eqb (memory_descriptor_id descriptor) (memory_descriptor_id first)))
      (memory_unique_descriptors rest)
  end.
Lemma memory_descriptor_filter_ids array descriptors :
  map memory_descriptor_id (filter (fun descriptor => negb (Pos.eqb (memory_descriptor_id descriptor) array)) descriptors) =
  filter (fun identifier => negb (Pos.eqb identifier array)) (map memory_descriptor_id descriptors).
Proof.
  induction descriptors as [|descriptor rest IH]; [reflexivity|].
  cbn; destruct (negb (Pos.eqb (memory_descriptor_id descriptor) array)); cbn; rewrite IH; reflexivity.
Qed.
Lemma memory_unique_descriptor_ids requests :
  NoDup (map memory_descriptor_id (memory_unique_descriptors requests)).
Proof.
  induction requests as [|first rest IH]; cbn; [constructor|].
  constructor.
  - rewrite memory_descriptor_filter_ids; intro MEMBER; apply filter_In in MEMBER as [_ DIFFERENT].
    rewrite Pos.eqb_refl in DIFFERENT; discriminate.
  - rewrite memory_descriptor_filter_ids; apply NoDup_filter; exact IH.
Qed.
Lemma memory_unique_descriptors_member requests descriptor :
  In descriptor (memory_unique_descriptors requests) -> In descriptor requests.
Proof.
  induction requests as [|first rest IH]; cbn; [tauto|].
  intros [SAME|MEMBER]; [left; exact SAME|right; apply IH; apply filter_In in MEMBER; tauto].
Qed.

Lemma memory_descriptor_registry_variable descriptors entries ge locals array shape :
  Forall2 (memory_descriptor_binding ge locals) descriptors entries ->
  (exists descriptor, In descriptor descriptors /\ memory_descriptor_for array shape descriptor) ->
  exists entry, In entry entries /\ memory_array_id entry = array /\
    memory_array_extent entry = rectangle_extent shape /\
    rect_array_binding shape ge locals array (memory_array_block entry).
Proof.
  intros RELATED [descriptor [MEMBER [ID [VARIABLE EXTENT]]]].
  revert descriptor MEMBER ID VARIABLE EXTENT.
  induction RELATED as [|head entry rest entries BINDING RELATED IH]; intros descriptor MEMBER ID VARIABLE EXTENT; [contradiction|].
  cbn in MEMBER; destruct MEMBER as [SAME|MEMBER].
  - subst descriptor; destruct BINDING as [ENTRY_ID [ENTRY_EXTENT [VALID ARRAY]]].
    rewrite VARIABLE in ARRAY.
    apply (proj1 (@memory_rect_binding_equal_extent (memory_descriptor_shape head) shape ge locals array (memory_array_block entry) EXTENT)) in ARRAY.
    exists entry; split; [cbn; auto|]; split; [rewrite ENTRY_ID; exact ID|]; split; [rewrite ENTRY_EXTENT; exact EXTENT|exact ARRAY].
  - destruct (IH descriptor MEMBER ID VARIABLE EXTENT) as [other [IN [OTHER_ID [OTHER_EXTENT ARRAY]]]].
    exists other; split; [cbn; auto|]; repeat split; assumption.
Qed.
Lemma memory_registry_requested_array descriptors requests entries ge locals array shape :
  Forall2 (memory_descriptor_binding ge locals) descriptors entries ->
  memory_descriptors_cover descriptors requests ->
  In (MemoryArrayDescriptor array array shape) requests ->
  exists entry, In entry entries /\ memory_array_id entry = array /\
    memory_array_extent entry = rectangle_extent shape /\
    rect_array_binding shape ge locals array (memory_array_block entry).
Proof.
  intros RELATED COVER MEMBER; eapply memory_descriptor_registry_variable; [exact RELATED|].
  apply Forall_forall with (x := MemoryArrayDescriptor array array shape) in COVER; [|exact MEMBER].
  exact COVER.
Qed.

Definition memory_descriptor_for_check array shape descriptor :=
  Pos.eqb (memory_descriptor_id descriptor) array && Pos.eqb (memory_descriptor_variable descriptor) array &&
    Z.eqb (rectangle_extent (memory_descriptor_shape descriptor)) (rectangle_extent shape).
Lemma memory_descriptor_for_check_sound array shape descriptor :
  memory_descriptor_for_check array shape descriptor = true -> memory_descriptor_for array shape descriptor.
Proof.
  unfold memory_descriptor_for_check,memory_descriptor_for; repeat rewrite andb_true_iff.
  intros [[ID VARIABLE] EXTENT]; apply Pos.eqb_eq in ID,VARIABLE; apply Z.eqb_eq in EXTENT; tauto.
Qed.
Definition memory_descriptors_cover_check descriptors requests :=
  forallb (fun request => existsb (memory_descriptor_for_check (memory_descriptor_id request) (memory_descriptor_shape request)) descriptors) requests.
Lemma memory_descriptors_cover_check_sound descriptors requests :
  memory_descriptors_cover_check descriptors requests = true -> memory_descriptors_cover descriptors requests.
Proof.
  intro CHECK; unfold memory_descriptors_cover; apply Forall_forall; intros request MEMBER.
  unfold memory_descriptors_cover_check in CHECK; apply forallb_forall with (x := request) in CHECK; [|exact MEMBER].
  apply existsb_exists in CHECK as [descriptor [IN COVER]].
  exists descriptor; split; [exact IN|apply memory_descriptor_for_check_sound; exact COVER].
Qed.

Theorem memory_descriptor_entries_exist descriptors ge locals memory :
  Forall (fun descriptor => rectangle_layout_valid (memory_descriptor_shape descriptor)) descriptors ->
  NoDup (map memory_descriptor_id descriptors) ->
  (forall descriptor, In descriptor descriptors -> exists block,
    rect_array_binding (memory_descriptor_shape descriptor) ge locals (memory_descriptor_variable descriptor) block /\
    Mem.valid_pointer memory block 0 = true) ->
  exists entries, Forall2 (memory_descriptor_binding ge locals) descriptors entries /\
    NoDup (map memory_array_id entries) /\
    Forall (fun entry => Mem.valid_pointer memory (memory_array_block entry) 0 = true) entries.
Proof.
  intros VALID UNIQUE BINDINGS.
  assert (BUILD : exists entries, Forall2 (memory_descriptor_binding ge locals) descriptors entries /\
    map memory_array_id entries = map memory_descriptor_id descriptors /\
    Forall (fun entry => Mem.valid_pointer memory (memory_array_block entry) 0 = true) entries).
  { clear UNIQUE; induction VALID as [|descriptor descriptors VALID REST IH].
    - exists []; split; [constructor|split; [reflexivity|constructor]].
    - destruct (BINDINGS descriptor ltac:(cbn; auto)) as [block [ARRAY POINTER]].
      destruct (IH ltac:(intros d MEMBER; apply BINDINGS; cbn; auto)) as [entries [RELATED [IDS POINTERS]]].
      exists (MemoryArrayEntry (memory_descriptor_id descriptor) block (rectangle_extent (memory_descriptor_shape descriptor))::entries).
      split; [constructor; [unfold memory_descriptor_binding; cbn; split; [reflexivity|]; split; [reflexivity|]; split; assumption|exact RELATED]|].
      split; [cbn; rewrite IDS; reflexivity|constructor; assumption]. }
  destruct BUILD as [entries [RELATED [IDS POINTERS]]].
  exists entries; split; [exact RELATED|split; [rewrite IDS; exact UNIQUE|exact POINTERS]].
Qed.
Print Assumptions memory_descriptor_entries_exist.
