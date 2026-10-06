From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Clight.
From Guard Require Import ClightCondition ClightPureExpr CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryNaryCompute GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions
  GuardMemoryAffineWriteSeparation GuardMemoryObservationStability GuardMemoryMultiPointerSequence GuardMemoryBufferOffsets.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyConditionComposition ClightReadonlyRewrite ClightConditionComposition
  ClightReadonlyLoadedTreeSynthesis ClightWordChunkSeparation ClightQuietDeterminacy
  ClightLoadedBoundSyntax ClightDependentHeaderObservations.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_chunk_domain row column i j valuation values address wide operations entry :=
  Forall (memory_affine_write_ready row column i j valuation values entry) operations /\
  exists block offset loaded,
    eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry) address (Vptr block offset) /\
    Mem.loadv (word_observation_chunk wide) (entry_memory entry) (Vptr block offset) = Some loaded.
Definition memory_affine_chunk_separated values address wide operations entry :=
  forall block offset,
    eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry) address (Vptr block offset) ->
    memory_pointer_writes_apart_observation (entry_temps entry) values operations
      (MemoryLocation (word_observation_chunk wide) block (Ptrofs.unsigned offset)).
Fixpoint memory_affine_chunk_probe row column i j address wide operations :=
  match operations with
  | [] => Decision true
  | operation::rest => decision_bind
      (word_chunk_separation (memory_affine_write_address row column i j operation) address wide)
      (memory_affine_chunk_probe row column i j address wide rest) (Decision false)
  end.

Definition memory_affine_single_chunk_condition fe O (observe : fragment_observation -> O -> Prop)
  row column i j valuation values address wide operation :
  typeof address = Tpointer type_int32s noattr ->
  readonly_condition (readonly_clight_host fe observe)
    (memory_affine_chunk_domain row column i j valuation values address wide [operation])
    (memory_affine_chunk_separated values address wide [operation])
    (word_chunk_separation (memory_affine_write_address row column i j operation) address wide).
Proof.
  intro TYPE; eapply readonly_condition_entails.
  - eapply readonly_condition_restrict; [apply word_chunk_separation_condition; [reflexivity|exact TYPE]|].
    intros entry [READY [block [offset [loaded [ADDRESS READ]]]]].
    inversion READY as [|item rest PREP REST]; subst.
    destruct PREP as [[other [base [OUT ACCESS]]] [MATH [RANGE WORDS]]].
    exists other,(Ptrofs.add base (Ptrofs.repr
      (4*memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) values))),block,offset,loaded.
    split; [|split; [exact ADDRESS|split; [|exact READ]]].
    + eapply memory_affine_write_address_eval with (valuation:=valuation); [|exact OUT].
      split; [exists other,base; auto|split; [exact MATH|split; assumption]].
    + rewrite memory_pointer_buffer_address; exact ACCESS.
  - intros entry [READY LOADED] [other [actual [block [offset [WRITE_ADDRESS [ADDRESS APART]]]]]].
    inversion READY as [|item rest PREP REST]; subst.
    intros target address_offset OBSERVED item MEMBER write_block write_base WRITE.
    cbn in MEMBER; destruct MEMBER as [<-|[]].
    pose proof (@memory_affine_write_address_eval row column i j valuation values entry operation write_block write_base PREP WRITE) as EXPECTED.
    pose proof (proj1 (expressions_determinate (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry))
      _ _ WRITE_ADDRESS _ EXPECTED) as SAME_WRITE.
    pose proof (proj1 (expressions_determinate (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry))
      _ _ ADDRESS _ OBSERVED) as SAME_OBSERVATION.
    inversion SAME_WRITE; inversion SAME_OBSERVATION; subst; rewrite memory_pointer_buffer_address in APART; exact APART.
Defined.

Definition memory_affine_chunk_condition fe O (observe : fragment_observation -> O -> Prop)
  row column i j valuation values address wide operations :
  typeof address = Tpointer type_int32s noattr ->
  readonly_condition (readonly_clight_host fe observe)
    (memory_affine_chunk_domain row column i j valuation values address wide operations)
    (memory_affine_chunk_separated values address wide operations)
    (memory_affine_chunk_probe row column i j address wide operations).
Proof.
  intro TYPE; induction operations as [|operation rest IH]; cbn [memory_affine_chunk_probe].
  - eapply readonly_condition_entails; [apply readonly_constant_condition with (A:=clight_readonly_check_algebra fe observe)|].
    intros entry DOMAIN PROPERTY block offset ADDRESS item MEMBER; contradiction.
  - eapply readonly_condition_entails.
    + eapply sequence_readonly_conditions with (A:=clight_readonly_check_algebra fe observe).
      * eapply readonly_condition_restrict;
          [exact (@memory_affine_single_chunk_condition fe O observe row column i j valuation values address wide operation TYPE)|].
        intros entry [READY LOAD]; inversion READY; subst; split; [constructor; [assumption|constructor]|exact LOAD].
      * eapply readonly_condition_restrict; [exact IH|].
        intros entry [[READY LOAD] FIRST]; inversion READY; subst; split; assumption.
    + intros entry DOMAIN [FIRST REST] block offset ADDRESS item MEMBER write_block write_base WRITE.
      cbn in MEMBER; destruct MEMBER as [<-|MEMBER].
      * apply FIRST with (block:=block) (offset:=offset) (operation:=operation); [exact ADDRESS|cbn; auto|exact WRITE].
      * apply REST with (block:=block) (offset:=offset) (operation:=item); assumption.
Defined.

Definition memory_affine_dependent_write_domain row column i j valuation values root pointer_cache cache operations entry :=
  Forall (memory_affine_write_ready row column i j valuation values entry) operations /\
  dependent_cached_header root pointer_cache cache entry.
Definition memory_affine_dependent_write_separated values root pointer_cache cache operations entry :=
  forall observation, In observation (dependent_header_observations root pointer_cache cache entry) ->
    memory_pointer_writes_apart_observation (entry_temps entry) values operations (fst observation).
Definition memory_affine_dependent_write_probe row column i j root pointer_cache operations :=
  decision_bind (memory_affine_chunk_probe row column i j (dependent_pointer_cell_address root) Archi.ptr64 operations)
    (memory_affine_chunk_probe row column i j (signed_pointer_temp pointer_cache) false operations) (Decision false).

Definition memory_affine_dependent_write_condition fe O (observe : fragment_observation -> O -> Prop)
  row column i j valuation values root pointer_cache cache operations :
  readonly_condition (readonly_clight_host fe observe)
    (memory_affine_dependent_write_domain row column i j valuation values root pointer_cache cache operations)
    (memory_affine_dependent_write_separated values root pointer_cache cache operations)
    (memory_affine_dependent_write_probe row column i j root pointer_cache operations).
Proof.
  eapply readonly_condition_entails.
  - eapply sequence_readonly_conditions with (A:=clight_readonly_check_algebra fe observe).
    + eapply readonly_condition_restrict;
        [exact (@memory_affine_chunk_condition fe O observe row column i j valuation values
          (dependent_pointer_cell_address root) Archi.ptr64 operations eq_refl)|].
      intros entry [READY [block [offset [target [address [bound [ROOT [POINTER [CACHE [READ_POINTER READ_BOUND]]]]]]]]]].
      split; [exact READY|exists block,offset,(Vptr target address); split; [apply dependent_pointer_cell_address_eval; exact ROOT|exact READ_POINTER]].
    + eapply readonly_condition_restrict;
        [exact (@memory_affine_chunk_condition fe O observe row column i j valuation values
          (signed_pointer_temp pointer_cache) false operations eq_refl)|].
      intros entry [[READY [block [offset [target [address [bound [ROOT [POINTER [CACHE [READ_POINTER READ_BOUND]]]]]]]]]] FIRST].
      split; [exact READY|exists target,address,(Vint bound); split; [constructor; exact POINTER|exact READ_BOUND]].
  - intros entry [READY [block [offset [target [address [bound [ROOT [POINTER [CACHE [READ_POINTER READ_BOUND]]]]]]]]]] [FIRST SECOND].
    intros observation MEMBER; unfold dependent_header_observations in MEMBER; rewrite ROOT,POINTER,CACHE in MEMBER.
    cbn in MEMBER; destruct MEMBER as [<-|[<-|[]]]; cbn [fst].
    + apply FIRST; apply dependent_pointer_cell_address_eval; exact ROOT.
    + apply SECOND; constructor; exact POINTER.
Defined.

Theorem memory_affine_dependent_write_preserves
  (fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop)
  O (observe : fragment_observation -> O -> Prop)
  row column i j valuation values root pointer_cache cache operations entry before after :
  memory_affine_dependent_write_domain row column i j valuation values root pointer_cache cache operations entry ->
  decision_run entry (memory_affine_dependent_write_probe row column i j root pointer_cache operations) true ->
  memory_multi_pointer_sequence_physical (entry_temps entry) values operations before after ->
  forall observation, In observation (dependent_header_observations root pointer_cache cache entry) ->
    location_load (fst observation) after = location_load (fst observation) before.
Proof.
  intros DOMAIN RUN STEP observation MEMBER.
  destruct (readonly_sound (@memory_affine_dependent_write_condition fe O observe row column i j valuation values
    root pointer_cache cache operations) entry true entry DOMAIN (conj RUN eq_refl)) as [SAME SOUND].
  eapply memory_pointer_sequence_observation_preserved; [apply (SOUND eq_refl observation MEMBER)|exact STEP].
Qed.

Print Assumptions memory_affine_single_chunk_condition.
Print Assumptions memory_affine_chunk_condition.
Print Assumptions memory_affine_dependent_write_condition.
Print Assumptions memory_affine_dependent_write_preserves.
