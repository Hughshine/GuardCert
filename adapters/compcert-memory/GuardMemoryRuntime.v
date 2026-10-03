From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers Maps.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From polcert.lib Require Import Linalg.
From Guard Require Import CompCertMemoryActions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition cell_locations := MemCell -> option memory_location.
Definition locations_nonalias (locations : cell_locations) :=
  forall first second first_location second_location,
    locations first = Some first_location -> locations second = Some second_location ->
    cell_neq first second -> location_disjoint first_location second_location.
Fixpoint resolve_cells cells (locations : cell_locations) : option (list memory_location) :=
  match cells with
  | [] => Some []
  | cell :: rest => match locations cell, resolve_cells rest locations with
      | Some loc, Some locs => Some (loc :: locs) | _, _ => None end
  end.
Record runtime_state := RuntimeState {
  runtime_locations : cell_locations;
  runtime_memory : mem
}.

(** The registry is a language view, not an emitted runtime query. A concrete
    source/guard bridge must provide it and prove its physical alias contract. *)
Definition footprint_run write_cell read_cells compute before after :=
  exists write reads,
    runtime_locations before write_cell = Some write /\
    resolve_cells read_cells (runtime_locations before) = Some reads /\
    runtime_locations after = runtime_locations before /\
    memory_action_run (MemoryAction reads write compute) (runtime_memory before) (runtime_memory after).
Definition cells_independent write1 reads1 write2 reads2 :=
  cell_neq write1 write2 /\ Forall (cell_neq write1) reads2 /\ Forall (cell_neq write2) reads1.

Lemma resolve_cells_disjoint locations write_cell write cells reads :
  locations_nonalias locations -> locations write_cell = Some write ->
  resolve_cells cells locations = Some reads -> Forall (cell_neq write_cell) cells ->
  Forall (location_disjoint write) reads.
Proof.
  intros NONALIAS WRITE; revert reads; induction cells as [|cell rest IH]; intros reads RESOLVE DIFFERENT.
  - cbn in RESOLVE; inversion RESOLVE; constructor.
  - cbn in RESOLVE; destruct (locations cell) as [loc|] eqn:LOC; try discriminate.
    destruct (resolve_cells rest locations) as [locs|] eqn:LOCS; try discriminate.
    inversion RESOLVE; subst reads; inversion DIFFERENT; subst; constructor.
    + eapply NONALIAS; eauto.
    + eapply IH; eauto.
Qed.

Theorem independent_footprints_reorder write1 reads1 compute1 write2 reads2 compute2 before middle after :
  locations_nonalias (runtime_locations before) ->
  cells_independent write1 reads1 write2 reads2 ->
  footprint_run write1 reads1 compute1 before middle ->
  footprint_run write2 reads2 compute2 middle after ->
  exists swapped,
    footprint_run write2 reads2 compute2 before swapped /\
    footprint_run write1 reads1 compute1 swapped after.
Proof.
  intros NONALIAS [WW [WR RW]] [first_write [first_reads [WRITE1 [READS1 [REG1 RUN1]]]]]
    [second_write [second_reads [WRITE2 [READS2 [REG2 RUN2]]]]].
  rewrite REG1 in WRITE2, READS2.
  assert (INDEPENDENT : memory_actions_independent
    (MemoryAction first_reads first_write compute1) (MemoryAction second_reads second_write compute2)).
  { split; [eapply NONALIAS; eauto|]; split.
    - eapply resolve_cells_disjoint; eauto.
    - eapply resolve_cells_disjoint; eauto. }
  destruct (independent_memory_actions_reorder INDEPENDENT RUN1 RUN2) as [swapped [SECOND FIRST]].
  exists (RuntimeState (runtime_locations before) swapped); split.
  - exists second_write,second_reads; repeat split; assumption || reflexivity.
  - exists first_write,first_reads; repeat split; cbn; try assumption.
    rewrite REG2, REG1; reflexivity.
Qed.

Inductive value_expression :=
| ConstantValue : Z -> value_expression
| ParameterValue : nat -> value_expression
| LoadedValue : nat -> value_expression
| AddValue : value_expression -> value_expression -> value_expression
| SubValue : value_expression -> value_expression -> value_expression
| MulValue : value_expression -> value_expression -> value_expression.
Fixpoint evaluate_value parameters loaded expression : option val :=
  match expression with
  | ConstantValue z => Some (Vint (Int.repr z))
  | ParameterValue n => match nth_error parameters n with Some z => Some (Vint (Int.repr z)) | None => None end
  | LoadedValue n => nth_error loaded n
  | AddValue first second => match evaluate_value parameters loaded first, evaluate_value parameters loaded second with
      | Some (Vint a), Some (Vint b) => Some (Vint (Int.add a b)) | _, _ => None end
  | SubValue first second => match evaluate_value parameters loaded first, evaluate_value parameters loaded second with
      | Some (Vint a), Some (Vint b) => Some (Vint (Int.sub a b)) | _, _ => None end
  | MulValue first second => match evaluate_value parameters loaded first, evaluate_value parameters loaded second with
      | Some (Vint a), Some (Vint b) => Some (Vint (Int.mul a b)) | _, _ => None end
  end.
Print Assumptions independent_footprints_reorder.

Definition flat_array_locations array block extent (cell : MemCell) : option memory_location :=
  if Pos.eqb (arr_id cell) array then match arr_index cell with
    | [index] => if (0 <=? index) && (index <? extent)
        then Some (MemoryLocation Mint32 block (4 * index)) else None
    | _ => None end
  else None.
Lemma flat_array_locations_nonalias array block extent : locations_nonalias (flat_array_locations array block extent).
Proof.
  intros [first_id first_indices] [second_id second_indices] first_location second_location FIRST SECOND DIFFERENT.
  unfold flat_array_locations in FIRST, SECOND; cbn [arr_id arr_index] in FIRST, SECOND.
  destruct (Pos.eqb first_id array) eqn:FIRST_ID; try discriminate FIRST.
  destruct (Pos.eqb second_id array) eqn:SECOND_ID; try discriminate SECOND.
  apply Pos.eqb_eq in FIRST_ID, SECOND_ID; subst first_id second_id.
  destruct first_indices as [|first_index [|first_rest first_tail]]; try discriminate FIRST.
  destruct second_indices as [|second_index [|second_rest second_tail]]; try discriminate SECOND.
  destruct ((0 <=? first_index) && (first_index <? extent)); try discriminate FIRST.
  destruct ((0 <=? second_index) && (second_index <? extent)); try discriminate SECOND.
  inversion FIRST; inversion SECOND; subst first_location second_location.
  assert (DISTINCT : first_index <> second_index).
  { intro SAME; subst second_index; unfold cell_neq in DIFFERENT; cbn in DIFFERENT.
    destruct DIFFERENT as [BAD|BAD]; [congruence|apply BAD; apply veq_refl]. }
  change (block <> block \/ 4 * first_index + 4 <= 4 * second_index \/
    4 * second_index + 4 <= 4 * first_index).
  right; destruct (Z.lt_trichotomy first_index second_index) as [LT|[EQ|GT]]; [left|exfalso|right]; lia.
Qed.
Print Assumptions flat_array_locations_nonalias.
