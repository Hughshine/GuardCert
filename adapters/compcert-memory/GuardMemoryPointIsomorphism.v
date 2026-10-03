From Stdlib Require Import List ZArith Lia Sorting.Sorted Sorting.Permutation.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryPolyhedral GuardMemoryPolyhedralRectangles
  GuardMemorySequencePolyhedral GuardMemorySequenceOrder.
Import ListNotations.
Set Implicit Arguments.

(** Point correspondence is a representation obligation. It does not assert
    that an instruction permutation preserves memory dependences. *)
Record memory_point_isomorphism parameters source target := MemoryPointIsomorphism {
  point_forward : PL.InstrPoint -> PL.InstrPoint;
  point_backward : PL.InstrPoint -> PL.InstrPoint;
  point_forward_valid : forall point, memory_sequence_valid_point parameters source point ->
    memory_sequence_valid_point parameters target (point_forward point);
  point_backward_valid : forall point, memory_sequence_valid_point parameters target point ->
    memory_sequence_valid_point parameters source (point_backward point);
  point_forward_inverse : forall point, memory_sequence_valid_point parameters source point ->
    point_backward (point_forward point) = point;
  point_backward_inverse : forall point, memory_sequence_valid_point parameters target point ->
    point_forward (point_backward point) = point;
  point_forward_time : forall point, memory_sequence_valid_point parameters source point ->
    PL.ILSema.ip_time_stamp (point_forward point) = PL.ILSema.ip_time_stamp point;
  point_backward_time : forall point, memory_sequence_valid_point parameters target point ->
    PL.ILSema.ip_time_stamp (point_backward point) = PL.ILSema.ip_time_stamp point;
  point_forward_execution : forall point initial final,
    memory_sequence_valid_point parameters source point ->
    PL.instr_point_sema point initial final -> PL.instr_point_sema (point_forward point) initial final;
  point_backward_execution : forall point initial final,
    memory_sequence_valid_point parameters target point ->
    PL.instr_point_sema point initial final -> PL.instr_point_sema (point_backward point) initial final
}.

Lemma memory_valid_map_nodup {A B} (valid : A -> Prop) (f : A -> B) (g : B -> A) points :
  (forall point, valid point -> g (f point) = point) ->
  (forall point, In point points -> valid point) ->
  NoDup points -> NoDup (map f points).
Proof.
  intros INVERSE VALID UNIQUE; induction UNIQUE; cbn; constructor.
  - intro MEMBER; apply in_map_iff in MEMBER as [other [SAME MEMBER]].
    apply H; assert (EQ : other = x).
    { rewrite <- (INVERSE other (VALID other (or_intror MEMBER))),
        <- (INVERSE x (VALID x (or_introl eq_refl))); congruence. }
    subst other; exact MEMBER.
  - apply IHUNIQUE; intros point MEMBER; apply VALID; right; exact MEMBER.
Qed.
Lemma memory_sorted_timestamp_map f points :
  (forall point, In point points -> PL.ILSema.ip_time_stamp (f point) = PL.ILSema.ip_time_stamp point) ->
  Sorted PL.instr_point_sched_le points -> Sorted PL.instr_point_sched_le (map f points).
Proof.
  intros TIMES ORDER; induction ORDER; cbn; constructor.
  - apply IHORDER; intros point MEMBER; apply TIMES; right; exact MEMBER.
  - inversion H; subst; constructor.
    unfold PL.instr_point_sched_le,PL.ILSema.instr_point_sched_lt,PL.ILSema.instr_point_sched_eq,
      PL.ILSema.instr_point_sched_ltb,PL.ILSema.instr_point_sched_eqb in *.
    rewrite (TIMES a (or_introl eq_refl)),(TIMES b (or_intror (or_introl eq_refl))); assumption.
Qed.
Lemma memory_point_execution_map f points initial final :
  (forall point before after, In point points ->
    PL.instr_point_sema point before after -> PL.instr_point_sema (f point) before after) ->
  PL.instr_point_list_semantics points initial final ->
  PL.instr_point_list_semantics (map f points) initial final.
Proof.
  intros MAP RUN; induction RUN; cbn.
  - constructor; assumption.
  - econstructor.
    + apply MAP; [left; reflexivity|exact H].
    + apply IHRUN; intros point before after MEMBER; apply MAP; right; exact MEMBER.
Qed.

Theorem memory_point_isomorphism_forward parameters source target context vars initial final
  (iso : memory_point_isomorphism parameters source target) :
  PL.poly_instance_list_semantics parameters (source,context,vars) initial final ->
  PL.poly_instance_list_semantics parameters (target,context,vars) initial final.
Proof.
  intro RUN; inversion RUN as [params program instructions ctxt variables before after flattened ordered
    PROGRAM FLAT PERM SORTED EXEC]; subst.
  injection PROGRAM as INSTRUCTIONS CONTEXT VARIABLES; subst instructions ctxt variables.
  assert (MEMBERS : forall point, In point ordered <-> memory_sequence_valid_point parameters source point).
  { intro point; unfold memory_sequence_valid_point.
    destruct FLAT as [_ [COVER [_ _]]]; rewrite <- COVER.
    split; eapply Permutation_in; [apply Permutation_sym; exact PERM|exact PERM]. }
  assert (UNIQUE : NoDup ordered).
  { eapply Permutation_NoDup; [exact PERM|exact (proj1 (proj2 (proj2 FLAT)))]. }
  set (mapped := map (point_forward iso) ordered).
  assert (COVER : forall point, In point mapped <-> memory_sequence_valid_point parameters target point).
  { intro point; unfold mapped; split.
    - intro MEMBER; apply in_map_iff in MEMBER as [old [<- MEMBER]].
      apply point_forward_valid; apply MEMBERS; exact MEMBER.
    - intro VALID; apply in_map_iff; exists (point_backward iso point); split.
      + apply point_backward_inverse; exact VALID.
      + apply MEMBERS; apply point_backward_valid; exact VALID. }
  assert (NODUP : NoDup mapped).
  { unfold mapped; eapply memory_valid_map_nodup with (g := point_backward iso).
    - exact (point_forward_inverse iso).
    - intros point MEMBER; apply MEMBERS; exact MEMBER.
    - exact UNIQUE. }
  destruct (@memory_sequence_ordered_flatten parameters target mapped COVER NODUP)
    as [canonical [TARGET_FLAT TARGET_PERM]].
  eapply PL.PolyPointListSema with (ipl := canonical) (sorted_ipl := mapped).
  - reflexivity.
  - exact TARGET_FLAT.
  - exact TARGET_PERM.
  - unfold mapped; apply memory_sorted_timestamp_map; [|exact SORTED].
    intros point MEMBER; apply point_forward_time; apply MEMBERS; exact MEMBER.
  - unfold mapped; apply memory_point_execution_map; [|exact EXEC].
    intros point before after MEMBER; apply point_forward_execution; apply MEMBERS; exact MEMBER.
Qed.
Definition memory_point_isomorphism_reverse parameters source target
  (iso : memory_point_isomorphism parameters source target) :
  memory_point_isomorphism parameters target source :=
  {| point_forward := point_backward iso; point_backward := point_forward iso;
     point_forward_valid := point_backward_valid iso; point_backward_valid := point_forward_valid iso;
     point_forward_inverse := point_backward_inverse iso; point_backward_inverse := point_forward_inverse iso;
     point_forward_time := point_backward_time iso; point_backward_time := point_forward_time iso;
     point_forward_execution := point_backward_execution iso; point_backward_execution := point_forward_execution iso |}.
Theorem memory_point_isomorphism_execution parameters source target context vars initial final
  (iso : memory_point_isomorphism parameters source target) :
  PL.poly_instance_list_semantics parameters (source,context,vars) initial final <->
  PL.poly_instance_list_semantics parameters (target,context,vars) initial final.
Proof.
  split; intro RUN; eapply memory_point_isomorphism_forward; [exact iso|exact RUN| |exact RUN].
  exact (memory_point_isomorphism_reverse iso).
Qed.
Print Assumptions memory_point_isomorphism_execution.
