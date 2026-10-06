From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightCountedLoop CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryNaryCompute GuardMemoryAffineSourceExpressions
  GuardMemoryAffineAddressSpecialization GuardMemoryAffineWriteSeparation
  GuardMemoryObservationStability GuardMemoryMultiPointerSequence.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite
  ClightReadonlyExpressionScan.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_row_bound row column i expression :=
  memory_source_affine_code (memory_affine_at row column i 0 expression).
Definition memory_affine_row_probe row column i expression parameter operations cap :=
  readonly_bound_expression_scan (memory_affine_row_bound row column i expression)
    (fun j => memory_affine_writes_probe row column i j parameter operations) cap 0.

(** This domain concerns one reached source row only. The actual row decoder
    supplies its write receipts, and existing arithmetic/range certificates
    supply the other fields. Future rows and bound stability are absent. *)
Definition memory_affine_row_domain row column i expression parameter operations cap
  (valuation : clight_entry -> ident -> Z) (values : clight_entry -> Z -> list Z)
  (width : clight_entry -> Z) entry :=
  0 <= width entry <= Z.of_nat cap /\
  memory_source_affine_math (memory_affine_at_value row column i 0 (valuation entry)) expression = width entry /\
  (forall identifier, In identifier (memory_source_affine_reads expression) ->
    identifier <> row -> identifier <> column ->
    (entry_temps entry) ! identifier = Some (Vint (Int.repr (valuation entry identifier)))) /\
  (forall j, 0 <= j < width entry ->
    Forall (memory_affine_write_ready row column i j (valuation entry) (values entry j) entry) operations) /\
  exists block offset loaded, (entry_temps entry) ! parameter = Some (Vptr block offset) /\
    Mem.loadv Mint32 (entry_memory entry) (Vptr block offset) = Some loaded.

Section ROW.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Variables row column parameter : ident.
Variable i : Z.
Variable expression : memory_source_affine.
Variable operations : list memory_nary_compute.
Variable cap : nat.
Variables valuation : clight_entry -> ident -> Z.
Variable values : clight_entry -> Z -> list Z.
Variable width : clight_entry -> Z.
Hypothesis CAP : Z.of_nat cap <= Int.max_signed.
Let domain := memory_affine_row_domain row column i expression parameter operations cap valuation values width.
Let property := fun j entry => memory_affine_writes_separated (values entry j) parameter operations entry.

Lemma memory_affine_row_bound_value entry : domain entry ->
  eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (memory_affine_row_bound row column i expression) (Vint (Int.repr (width entry))).
Proof.
  intros [RANGE [MATH [WORDS REST]]]; rewrite <- MATH; apply memory_affine_at_evaluation; exact WORDS.
Qed.

Definition memory_affine_row_point_condition j : readonly_condition (readonly_clight_host fe observe)
  (fun entry => domain entry /\ 0 <= j < width entry) (property j)
  (memory_affine_writes_probe row column i j parameter operations).
Proof.
  assert (DOMAIN : forall entry, domain entry -> 0 <= j < width entry ->
    memory_affine_write_domain row column i j (valuation entry) (values entry j) parameter operations entry).
  { intros entry [RANGE [MATH [WORDS [READY LOAD]]]] J; split; [apply READY; exact J|exact LOAD]. }
  constructor.
  - intros entry [D J]; apply (readonly_safe (@memory_affine_writes_condition fe O observe
      row column i j (valuation entry) (values entry j) parameter operations)); apply DOMAIN; assumption.
  - intros entry [D J]; apply (readonly_available (@memory_affine_writes_condition fe O observe
      row column i j (valuation entry) (values entry j) parameter operations)); apply DOMAIN; assumption.
  - intros entry answer checked [D J] RUN; apply (readonly_sound (@memory_affine_writes_condition fe O observe
      row column i j (valuation entry) (values entry j) parameter operations)); [apply DOMAIN; assumption|exact RUN].
Defined.

Definition memory_affine_row_separation_condition : readonly_condition (readonly_clight_host fe observe)
  domain (fun entry => forall j, 0 <= j < width entry -> property j entry)
  (memory_affine_row_probe row column i expression parameter operations cap).
Proof.
  eapply readonly_condition_restrict.
  - exact (@readonly_expression_scan_condition fe O observe (memory_affine_row_bound row column i expression)
      width domain (fun j => memory_affine_writes_probe row column i j parameter operations) property
      (memory_source_affine_type _) memory_affine_row_bound_value
      ltac:(intros entry [RANGE REST]; lia) memory_affine_row_point_condition cap).
  - intros entry D; split; [exact D|destruct D as [RANGE REST]; lia].
Defined.

Theorem memory_affine_row_probe_preserves_bound entry block offset loaded :
  domain entry -> (entry_temps entry) ! parameter = Some (Vptr block offset) ->
  Mem.loadv Mint32 (entry_memory entry) (Vptr block offset) = Some loaded ->
  decision_run entry (memory_affine_row_probe row column i expression parameter operations cap) true ->
  forall j before after, 0 <= j < width entry ->
    memory_multi_pointer_sequence_physical (entry_temps entry) (values entry j) operations before after ->
    location_load (MemoryLocation Mint32 block (Ptrofs.unsigned offset)) after =
    location_load (MemoryLocation Mint32 block (Ptrofs.unsigned offset)) before.
Proof.
  intros DOMAIN POINTER READ RUN j before after J STEP.
  destruct (readonly_sound memory_affine_row_separation_condition entry true entry DOMAIN
    (conj RUN eq_refl)) as [SAME SOUND].
  eapply memory_pointer_sequence_observation_preserved; [|exact STEP].
  apply (SOUND eq_refl j J); exact POINTER.
Qed.
End ROW.

Print Assumptions memory_affine_row_bound_value.
Print Assumptions memory_affine_row_point_condition.
Print Assumptions memory_affine_row_separation_condition.
Print Assumptions memory_affine_row_probe_preserves_bound.
