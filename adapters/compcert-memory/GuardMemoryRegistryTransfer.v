From Stdlib Require Import List Bool ZArith.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles
  GuardMemoryLoops GuardMemoryClightRectangles GuardMemoryMultipleArrays.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_array_registry_member entries entry cell :
  NoDup (map memory_array_id entries) -> In entry entries -> arr_id cell = memory_array_id entry ->
  memory_array_registry entries cell =
    flat_array_locations (memory_array_id entry) (memory_array_block entry) (memory_array_extent entry) cell.
Proof.
  induction entries as [|head rest IH]; intros UNIQUE MEMBER ID; [contradiction|].
  inversion UNIQUE as [|id ids FRESH TAIL]; subst.
  cbn in MEMBER; destruct MEMBER as [SAME|MEMBER].
  - subst head; cbn [memory_array_registry]; rewrite ID,Pos.eqb_refl; reflexivity.
  - cbn [memory_array_registry]; rewrite ID.
    assert (DISTINCT : memory_array_id entry <> memory_array_id head).
    { intro SAME; apply FRESH; rewrite <- SAME; apply in_map; exact MEMBER. }
    rewrite (proj2 (Pos.eqb_neq _ _) DISTINCT); apply IH; assumption.
Qed.

Lemma memory_resolve_cells_agree first second cells :
  Forall (fun cell => first cell = second cell) cells ->
  resolve_cells cells first = resolve_cells cells second.
Proof.
  intro RELATED; induction RELATED; cbn [resolve_cells]; [reflexivity|].
  rewrite H,IHRELATED; reflexivity.
Qed.
Theorem memory_instruction_registry_transfer instruction parameters first second before after :
  first (exact_cell (instruction_write instruction) parameters) =
    second (exact_cell (instruction_write instruction) parameters) ->
  Forall (fun cell => first cell = second cell) (memory_read_cells instruction parameters) ->
  (GuardMemoryInstr.instr_semantics instruction parameters (memory_write_cells instruction parameters)
    (memory_read_cells instruction parameters) (RuntimeState first before) (RuntimeState first after) <->
   GuardMemoryInstr.instr_semantics instruction parameters (memory_write_cells instruction parameters)
    (memory_read_cells instruction parameters) (RuntimeState second before) (RuntimeState second after)).
Proof.
  intros WRITE READS; pose proof (@memory_resolve_cells_agree first second _ READS) as READ.
  unfold GuardMemoryInstr.instr_semantics,footprint_run; cbn [runtime_locations runtime_memory].
  rewrite WRITE,READ; split;
    intros [WRITES [READ_CELLS [write [reads [LOOKUP [READ_LOOKUP [_ ACTION]]]]]]].
  all: split; [exact WRITES|].
  all: split; [exact READ_CELLS|].
  all: exists write,reads; split; [exact LOOKUP|].
  all: split; [exact READ_LOOKUP|].
  all: split; [reflexivity|exact ACTION].
Qed.

Lemma memory_mode_read_array mode shape array i j :
  Forall (fun cell => arr_id cell = array) (memory_read_cells (mode_instruction mode shape array) [i;j]).
Proof. destruct mode; cbn; repeat constructor. Qed.
Lemma memory_mode_write_array mode shape array i j :
  arr_id (exact_cell (instruction_write (mode_instruction mode shape array)) [i;j]) = array.
Proof. destruct mode; reflexivity. Qed.

Theorem memory_mode_registry_execution entries entry mode shape i j before after :
  NoDup (map memory_array_id entries) -> In entry entries ->
  memory_array_extent entry = rectangle_extent shape ->
  0 <= i*rectangle_stride shape+j < rectangle_extent shape ->
  0 <= i*rectangle_stride shape < rectangle_extent shape ->
  (mode_physical mode shape (memory_array_block entry) i j before after <->
   memory_point (mode_instruction mode shape (memory_array_id entry)) i j
     (RuntimeState (memory_array_registry entries) before)
     (RuntimeState (memory_array_registry entries) after)).
Proof.
  intros UNIQUE MEMBER EXTENT INDEX READ_INDEX.
  rewrite (@mode_instruction_execution mode shape (memory_array_id entry) (memory_array_block entry)
    i j before after INDEX READ_INDEX).
  unfold memory_point; symmetry; apply memory_instruction_registry_transfer.
  - rewrite (@memory_array_registry_member entries entry _ UNIQUE MEMBER
      (memory_mode_write_array mode shape (memory_array_id entry) i j)),EXTENT; reflexivity.
  - apply Forall_forall; intros cell IN.
    rewrite (@memory_array_registry_member entries entry cell UNIQUE MEMBER
      (proj1 (Forall_forall _ _) (memory_mode_read_array mode shape (memory_array_id entry) i j) cell IN)),EXTENT.
    reflexivity.
Qed.

Print Assumptions memory_array_registry_member.
Print Assumptions memory_instruction_registry_transfer.
Print Assumptions memory_mode_registry_execution.
