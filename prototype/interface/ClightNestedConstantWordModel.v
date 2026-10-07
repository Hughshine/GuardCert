From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap ClightTempFootprint
  ClightCountedLoop ClightRectangularLoops ClightRegionProgress CompCertMemoryActions ClightPureExpr
  ClightRectangularGuard.
From GuardAffineNest Require Import AffineNestGuardPackage AffineNestLeafModel.
From GuardInterface Require Import CompCertWordObservation ClightWordObservationControl
  ClightNestedConstantSite ClightNestedConstantSiteFacts ClightNestedConstantSitePrepare
  ClightNestedConstantNumericGuard ClightNestedConstantNumericInputs ClightNestedConstantSiteNumeric
  ClightNestedConstantHeaders ClightNestedConstantScanStatic ClightNestedConstantModel
  ClightConstantBoundModel ClightNestedExpressionCapture ClightNestedExpressionTransport
  ClightStrictLoopProgress ClightLoadedBoundSyntax ClightLoadedOffsetHeader ClightSignedIndexedOffsetHeader
  ClightNestedIndexedObservers ClightAffineJointObservation ClightObservedHeaderPrefix.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The captures contain computed bounds, not raw header words. Compare
    against the computed image of the BODY word; modular addition is injective. *)
Definition ncs_same_word_flag shape word entry :=
  Int.eq (temp_word (ncs_root_cache shape) (entry_temps entry)) (Int.add word (ncs_delta shape)) &&
  Int.eq (temp_word (ncs_child_cache shape) (entry_temps entry)) (Int.add word (ncs_child_delta shape)).

Lemma word_add_right_cancel first second delta :
  Int.add first delta = Int.add second delta -> first = second.
Proof.
  intro SAME; apply (f_equal (fun value => Int.add value (Int.neg delta))) in SAME.
  rewrite !Int.add_assoc, Int.add_neg_zero, !Int.add_zero in SAME; exact SAME.
Qed.

Theorem ncs_same_word_flag_raw shape word entry block offset raw child_raw
  (headers : ncs_observation_receipt shape entry (ncs_observers shape block offset raw child_raw)) :
  ncs_same_word_flag shape word entry = true -> raw = word /\ child_raw = word.
Proof.
  intro ACCEPT; unfold ncs_same_word_flag in ACCEPT; apply andb_true_iff in ACCEPT as [ROOT CHILD].
  apply Int.same_if_eq in ROOT; apply Int.same_if_eq in CHILD.
  pose proof (ncs_receipt_reads headers) as READS.
  pose proof (ncs_receipt_ready headers) as [ROOT_READY CHILD_READY].
  destruct ROOT_READY as [b [o [r [POINTER [LOAD CACHE]]]]].
  destruct CHILD_READY as [b' [o' [r' [POINTER' [LOAD' CACHE']]]]].
  cbn [entry_temps] in CACHE, CACHE'; unfold temp_word in ROOT, CHILD; rewrite CACHE in ROOT; rewrite CACHE' in CHILD.
  cbn [ncs_observers nested_indexed_word_observers] in READS.
  pose proof (Forall_inv READS) as FIRST.
  pose proof (Forall_inv (Forall_inv_tail READS)) as SECOND.
  destruct FIRST as [_ [ADDRESS FIRST]]; destruct SECOND as [_ [ADDRESS' SECOND]].
  cbn [word_observer_address signed_pointer_temp] in ADDRESS; apply scalar_temp_inv in ADDRESS.
  cbn [word_observer_block word_observer_offset] in ADDRESS.
  assert (ROOT_ADDRESS : Vptr b o = Vptr block offset) by congruence.
  assert (CHILD_ADDRESS : Vptr b' o' = Vptr block offset) by congruence.
  inversion ROOT_ADDRESS; subst b o; inversion CHILD_ADDRESS; subst b' o'.
  cbn [word_observer_block word_observer_offset word_observer_value] in FIRST, SECOND.
  assert (RAW : raw = r) by congruence.
  assert (CHILD_RAW : child_raw = r') by congruence.
  subst raw child_raw; split; eapply word_add_right_cancel; eassumption.
Qed.

Theorem ncs_constant_body_word_control shape word :
  check_constant_word_statement word (ncs_leaf shape) = true ->
  check_constant_word_control word
    (constant_body_source (ncs_iterator shape) (Int.repr (ncs_upper shape)) (ncs_leaf shape)) = true.
Proof.
  intro CHECK; unfold constant_body_source, strict_frontend_loop, rectangle_reset, counter_increment.
  cbn [check_constant_word_control check_constant_word_statement].
  apply check_constant_word_statement_control in CHECK; rewrite CHECK; reflexivity.
Qed.

Theorem ncs_word_body_preserves_headers shape word block offset
  fe ge locals before memory trace after final outcome :
  check_constant_word_statement word (ncs_leaf shape) = true ->
  header_observations_match (map word_observer_snapshot (ncs_observers shape block offset word word)) memory ->
  exec_stmt fe ge locals before memory
    (constant_body_source (ncs_iterator shape) (Int.repr (ncs_upper shape)) (ncs_leaf shape))
    trace after final outcome ->
  header_observations_match (map word_observer_snapshot (ncs_observers shape block offset word word)) final.
Proof.
  intros CHECK OBSERVED RUN.
  assert (STORES : constant_word_stores word memory final).
  { eapply checked_constant_word_control_execution; [exact RUN|].
    apply ncs_constant_body_word_control; exact CHECK. }
  unfold header_observations_match in *.
  cbn [ncs_observers nested_indexed_word_observers map word_observer_snapshot] in *.
  inversion OBSERVED as [|a l FIRST REST]; subst.
  inversion REST as [|a' l' SECOND LAST]; subst.
  apply Forall_cons.
  - cbn [word_observer_snapshot word_observer_location word_observer_block word_observer_offset
      word_observer_value location_load fst snd] in FIRST |- *.
    eapply constant_word_stores_preserve_observation; eassumption.
  - apply Forall_cons.
    + cbn [word_observer_snapshot word_observer_location word_observer_block word_observer_offset
        word_observer_value location_load fst snd] in SECOND |- *.
      eapply constant_word_stores_preserve_observation; eassumption.
    + apply Forall_nil.
Qed.

Section MODEL.
Variables source : statement.
Variables parameters live : list ident.
Variable proposal : affine_guard_proposal.
Variable shape : nested_constant_shape.
Variable site : nested_constant_site source parameters live proposal shape.
Variable word : int.
Hypothesis BODY : check_constant_word_statement word (ncs_leaf shape) = true.

(** A sufficient entry condition replaces address separation with preservation
    of the observed values. All execution/frame evidence is produced by the
    existing checked site and original-source capture/preparation receipts. *)
Theorem ncs_same_word_accepted_model fe ge locals checked memory checked_source_after final
  (receipt : ncs_prepared_receipt source parameters live proposal shape fe ge locals checked memory checked_source_after final) :
  ncs_same_word_flag shape word (Entry ge locals (ncs_prepared_temps shape checked) memory) = true ->
  exists after,
    exec_stmt fe ge locals (ncs_prepared_temps shape checked) memory (ncs_model shape)
      E0 after final Out_normal /\
    temp_agree (ncs_scope source live) checked_source_after after.
Proof.
  intro ACCEPT.
  set (entry := Entry ge locals (ncs_prepared_temps shape checked) memory).
  destruct (ncs_prepare_observers receipt) as [block [offset [raw [child_raw HEADERS]]]].
  change (ncs_observation_receipt shape entry (ncs_observers shape block offset raw child_raw)) in HEADERS.
  destruct (@ncs_same_word_flag_raw shape word entry block offset raw child_raw HEADERS ACCEPT)
    as [RAW CHILD_RAW]; subst raw child_raw.
  pose proof (ncs_receipt_ready HEADERS) as [ROOT_READY CHILD_READY].
  destruct ROOT_READY as [b [o [r [P [READ ROOT_CACHE]]]]].
  destruct CHILD_READY as [b' [o' [r' [P' [READ' CHILD_CACHE]]]]].
  assert (ROOT_WORD : (entry_temps entry)!(ncs_root_cache shape) =
    Some (Vint (temp_word (ncs_root_cache shape) (entry_temps entry)))).
  { unfold temp_word; rewrite ROOT_CACHE; reflexivity. }
  assert (CHILD_WORD : (entry_temps entry)!(ncs_child_cache shape) =
    Some (Vint (temp_word (ncs_child_cache shape) (entry_temps entry)))).
  { unfold temp_word; rewrite CHILD_CACHE; reflexivity. }
  assert (POSITIVE : 0 < Int.signed (temp_word (ncs_root_cache shape) (entry_temps entry)) /\
    0 < Int.signed (temp_word (ncs_child_cache shape) (entry_temps entry))).
  { pose proof (ncs_prepare_accept receipt) as NUMERIC.
    change (ncs_numeric_flag parameters proposal shape entry = true) in NUMERIC.
    unfold ncs_numeric_flag, nested_constant_numeric_flag in NUMERIC.
    destruct (register_positive (ncs_root_cache shape) entry) eqn:ROOT; [|discriminate].
    destruct (register_positive (ncs_child_cache shape) entry) eqn:CHILD; [|discriminate].
    split; eapply register_positive_sound; eassumption. }
  destruct (ncs_prepare_source receipt) as [after [SOURCE [PUBLIC [CHILD COMPONENT]]]].
  pose proof SOURCE as ORIGINAL; rewrite (ncs_exact site) in ORIGINAL.
  assert (CACHED : exec_stmt fe ge locals (entry_temps entry) memory
    (nested_cached_source (ncs_row shape) (ncs_root_cache shape) (ncs_column shape) (ncs_child_cache shape)
      (constant_body_source (ncs_iterator shape) (Int.repr (ncs_upper shape)) (ncs_leaf shape)))
    E0 after final Out_normal).
  { edestruct nested_expression_initial_cached with
      (fe:=fe) (ge:=ge) (locals:=locals)
      (row:=ncs_row shape) (column:=ncs_column shape)
      (cache:=ncs_root_cache shape) (child_cache:=ncs_child_cache shape)
      (body:=constant_body_source (ncs_iterator shape) (Int.repr (ncs_upper shape)) (ncs_leaf shape))
      (stable:=ncs_stable source parameters live shape) (written:=[ncs_iterator shape])
      (upper:=temp_word (ncs_root_cache shape) (entry_temps entry))
      (child_upper:=temp_word (ncs_child_cache shape) (entry_temps entry))
      (observations:=map word_observer_snapshot (ncs_observers shape block offset word word))
      (base:=entry_temps entry) (memory:=memory) (after:=after) (final:=final)
      (bound:=signed_load_offset (ncs_pointer shape) (ncs_delta shape))
      (child_bound:=signed_indexed_offset (ncs_pointer shape) (ncs_index shape) (ncs_child_delta shape))
      as [CACHED OBSERVED].
    all: try reflexivity.
    all: try exact ROOT_WORD.
    all: try exact CHILD_WORD.
    all: try solve [apply (ncs_site_caches_stable site); unfold ncs_caches; cbn; tauto].
    all: try solve [apply (@ncs_scan_coordinate_not_stable source parameters live shape); unfold ncs_coordinates; cbn; tauto].
    all: try solve [pose proof (ncs_scan_coordinate_unique site) as UNIQUE;
      unfold ncs_coordinates in UNIQUE;
      repeat match goal with H : NoDup (_::_) |- _ => apply NoDup_cons_iff in H as [? H] end;
      cbn [List.In] in *; intuition congruence].
    all: try exact (proj1 (ncs_scan_source_effects site)).
    all: try exact (proj1 (proj2 (ncs_scan_source_effects site))).
    all: try exact (proj2 (proj2 (ncs_scan_source_effects site))).
    all: try solve [cbn; intuition congruence].
    all: try solve [intros identifier MEMBER BAD; cbn in BAD; destruct BAD as [SAME|[]]; subst identifier;
      apply (@ncs_scan_coordinate_not_stable source parameters live shape (ncs_iterator shape)) in MEMBER;
      [exact MEMBER|unfold ncs_coordinates; cbn; tauto]].
    all: try solve [lia].
    all: try solve [intros i current mem RANGE ROW FRAME OBSERVED;
      exact (@ncs_root_header_from_receipt shape entry _ HEADERS
        (ncs_stable source parameters live shape) current mem
        (ncs_site_pointer_stable site ltac:(left; reflexivity)) FRAME OBSERVED)].
    all: try solve [intros i j current mem RANGE CHILD_RANGE ROW COLUMN FRAME OBSERVED;
      exact (@ncs_child_header_from_receipt shape entry _ HEADERS
        (ncs_stable source parameters live shape) current mem
        (ncs_site_pointer_stable site ltac:(left; reflexivity)) FRAME OBSERVED)].
    all: try solve [intros i j current mem exit last RANGE CHILD_RANGE ROW COLUMN FRAME OBSERVED RUN;
      eapply ncs_word_body_preserves_headers; eassumption].
    all: try exact (ncs_prepare_row receipt).
    all: try exact (ncs_receipt_initial HEADERS).
    all: try exact ORIGINAL.
    all: try exact CACHED. }
  exists after; split; [|exact PUBLIC].
  unfold ncs_model; eapply nested_constant_closed_preinitialized_model.
  - exact (ncs_scan_model_unique site).
  - exact (affine_leaf_quiet (ncs_scan_leaf site)).
  - exact (affine_leaf_writes (ncs_scan_leaf site)).
  - exact CHILD_WORD.
  - exact (ncs_prepare_child receipt).
  - exact (ncs_prepare_component receipt).
  - exact CACHED.
Qed.
End MODEL.

Print Assumptions word_add_right_cancel.
Print Assumptions ncs_same_word_flag_raw.
Print Assumptions ncs_constant_body_word_control.
Print Assumptions ncs_word_body_preserves_headers.
Print Assumptions ncs_same_word_accepted_model.
