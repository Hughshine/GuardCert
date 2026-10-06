From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Clight.
From Guard Require Import ClightCondition ClightCountedLoop ClightPureExpr ClightRectangularStore CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryNaryCompute GuardMemoryNaryAffineAccess
  GuardMemoryNaryAffineExpressions GuardMemoryAffineSourceExpressions GuardMemoryBufferOffsets
  GuardMemoryObservationStability GuardMemoryWriteReceipts GuardMemoryAffineAddressSpecialization
  GuardMemoryMultiPointerCompute GuardMemoryMultiPointerAccess GuardMemoryNaryAccessCheck
  GuardMemoryNaryRanges GuardMemoryScalarAccess.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyConditionComposition
  ClightReadonlyRewrite ClightConditionComposition ClightWordAddressSeparation ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_write_address row column i j operation :=
  memory_affine_address_at row column i j
    (memory_nary_access_array (memory_nary_compute_write operation))
    (memory_nary_access_expression (memory_nary_compute_write operation)).

(** A reached source row supplies the receipt. The source descriptor/checker
    supplies arithmetic correspondence, ranges and parameter word bindings.
    None of these fields assumes that the observed bound is stable. *)
Definition memory_affine_write_ready row column i j valuation values entry operation :=
  memory_write_receipt (entry_temps entry) values (entry_memory entry) operation /\
  memory_source_affine_math (memory_affine_at_value row column i j valuation)
    (memory_nary_access_expression (memory_nary_compute_write operation)) =
    memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) values /\
  signed_range (memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) values) /\
  (forall identifier, In identifier
    (memory_source_affine_reads (memory_nary_access_expression (memory_nary_compute_write operation))) ->
    identifier <> row -> identifier <> column ->
    (entry_temps entry) ! identifier = Some (Vint (Int.repr (valuation identifier)))).

Definition memory_affine_write_domain row column i j valuation values parameter operations entry :=
  Forall (memory_affine_write_ready row column i j valuation values entry) operations /\
  exists block offset loaded, (entry_temps entry) ! parameter = Some (Vptr block offset) /\
    Mem.loadv Mint32 (entry_memory entry) (Vptr block offset) = Some loaded.

Definition memory_affine_writes_separated values parameter operations entry :=
  forall block offset, (entry_temps entry) ! parameter = Some (Vptr block offset) ->
    memory_pointer_writes_apart_observation (entry_temps entry) values operations
      (MemoryLocation Mint32 block (Ptrofs.unsigned offset)).

(** Reuse the existing checked access encoding and box-range theorem. The
    added probe does not require a second independent affine encoder. *)
Theorem memory_affine_checked_write_ready limits layout scalars extent
  row column i j valuation values entry operation :
  memory_multi_pointer_compute_valid limits layout scalars extent operation ->
  memory_nary_ranges limits (map (memory_affine_at_value row column i j valuation) layout) ->
  map (memory_affine_at_value row column i j valuation) (layout++scalars) = values ->
  (forall identifier, In identifier layout -> identifier <> row -> identifier <> column ->
    (entry_temps entry) ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  memory_write_receipt (entry_temps entry) values (entry_memory entry) operation ->
  memory_affine_write_ready row column i j valuation values entry operation.
Proof.
  intros [[[SHAPE [ENCODE BOUNDS]] EXTENT] REST] RANGE VALUES WORDS RECEIPT.
  assert (INDEX : memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) values =
    memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation))
      (map (memory_affine_at_value row column i j valuation) layout)).
  { rewrite <- VALUES,map_app,memory_scalar_index_value; [reflexivity|].
    rewrite (@memory_encode_nary_index_length layout _ _ ENCODE),length_map; reflexivity. }
  split; [exact RECEIPT|split; [|split]].
  - rewrite INDEX; apply memory_encode_nary_index_value; exact ENCODE.
  - rewrite INDEX; eapply rect_index_signed; [exact SHAPE|apply BOUNDS; exact RANGE].
  - intros identifier READ ROW COLUMN; apply WORDS; [|exact ROW|exact COLUMN].
    eapply memory_encode_nary_index_reads; eassumption.
Qed.

Fixpoint memory_affine_writes_probe row column i j parameter operations :=
  match operations with
  | [] => Decision true
  | operation::rest => decision_bind
      (word_address_separation (memory_affine_write_address row column i j operation) parameter)
      (memory_affine_writes_probe row column i j parameter rest) (Decision false)
  end.

Lemma memory_affine_write_address_eval row column i j valuation values entry operation block base :
  memory_affine_write_ready row column i j valuation values entry operation ->
  (entry_temps entry) ! (memory_nary_access_array (memory_nary_compute_write operation)) = Some (Vptr block base) ->
  eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (memory_affine_write_address row column i j operation)
    (Vptr block (Ptrofs.add base (Ptrofs.repr
      (4*memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) values)))).
Proof.
  intros [RECEIPT [MATH [RANGE WORDS]]] POINTER; rewrite <- MATH in RANGE |- *.
  apply memory_affine_address_at_evaluation; assumption.
Qed.

Definition memory_affine_single_write_condition fe O (observe : fragment_observation -> O -> Prop)
  row column i j valuation values parameter operation :
  readonly_condition (readonly_clight_host fe observe)
    (memory_affine_write_domain row column i j valuation values parameter [operation])
    (memory_affine_writes_separated values parameter [operation])
    (word_address_separation (memory_affine_write_address row column i j operation) parameter).
Proof.
  eapply readonly_condition_entails.
  - eapply readonly_condition_restrict; [apply word_address_separation_condition; reflexivity|].
    intros entry [READY [block [offset [loaded [POINTER READ]]]]].
    inversion READY as [|item rest PREP REST]; subst.
    destruct PREP as [[other [base [OUT ACCESS]]] [MATH [RANGE WORDS]]].
    exists other,(Ptrofs.add base (Ptrofs.repr
      (4*memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) values))),
      block,offset,loaded; split; [|split; [exact POINTER|split; [|exact READ]]].
    + eapply memory_affine_write_address_eval with (valuation:=valuation); [|exact OUT].
      split; [exists other,base; auto|split; [exact MATH|split; assumption]].
    + rewrite memory_pointer_buffer_address; exact ACCESS.
  - intros entry [READY LOADED] [other [address [bound [offset [EVAL [BOUND APART]]]]]].
    inversion READY as [|item rest PREP REST]; subst.
    intros block base POINTER item MEMBER write_block write_base WRITE.
    cbn in MEMBER; destruct MEMBER as [<-|[]].
    assert (EXPECTED := @memory_affine_write_address_eval row column i j valuation values entry
      operation write_block write_base PREP WRITE).
    pose proof (proj1 (expressions_determinate (entry_ge entry) (entry_env entry)
      (entry_temps entry) (entry_memory entry)) _ _ EVAL _ EXPECTED) as SAME.
    assert (SAME_BOUND : Vptr bound offset = Vptr block base) by congruence.
    inversion SAME; inversion SAME_BOUND; subst.
    rewrite memory_pointer_buffer_address in APART; exact APART.
Defined.

Definition memory_affine_writes_condition fe O (observe : fragment_observation -> O -> Prop)
  row column i j valuation values parameter operations :
  readonly_condition (readonly_clight_host fe observe)
    (memory_affine_write_domain row column i j valuation values parameter operations)
    (memory_affine_writes_separated values parameter operations)
    (memory_affine_writes_probe row column i j parameter operations).
Proof.
  induction operations as [|operation rest IH]; cbn [memory_affine_writes_probe].
  - eapply readonly_condition_entails;
      [apply readonly_constant_condition with (A:=clight_readonly_check_algebra fe observe)|].
    intros entry DOMAIN PROPERTY block offset POINTER item MEMBER; contradiction.
  - eapply readonly_condition_entails.
    + eapply sequence_readonly_conditions with (A:=clight_readonly_check_algebra fe observe).
      * eapply readonly_condition_restrict;
          [exact (@memory_affine_single_write_condition fe O observe row column i j valuation values parameter operation)|].
        intros entry [READY LOAD]; inversion READY; subst; split; [constructor; [assumption|constructor]|exact LOAD].
      * eapply readonly_condition_restrict; [exact IH|].
        intros entry [[READY LOAD] FIRST]; inversion READY; subst; split; assumption.
    + intros entry DOMAIN [FIRST REST] block offset POINTER item MEMBER write_block write_base WRITE.
      cbn in MEMBER; destruct MEMBER as [<-|MEMBER].
      * apply FIRST with (block:=block) (offset:=offset) (operation:=operation);
          [exact POINTER|cbn; auto|exact WRITE].
      * apply REST with (block:=block) (offset:=offset) (operation:=item); assumption.
Defined.

Print Assumptions memory_affine_write_address_eval.
Print Assumptions memory_affine_checked_write_ready.
Print Assumptions memory_affine_single_write_condition.
Print Assumptions memory_affine_writes_condition.
