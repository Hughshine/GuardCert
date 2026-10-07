From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight Ctypes.
From Guard Require Import ClightCondition ClightSameAddress CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryFiniteAliasCondition
  GuardMemoryFootprintCapabilities GuardMemoryPointerCellComparison.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightStableLoadBody.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** An observation is a physical word, not a logical cell. In particular a
    write to the very same logical cell must not pass an identity shortcut. *)
Definition observed_word_location_check first second :=
  negb(Pos.eqb(location_block first)(location_block second) && Z.eqb(location_offset first)(location_offset second)).
Definition observed_word_cell_check (locations : cell_locations) observation cell :=
  match locations cell with Some write=>observed_word_location_check write observation|None=>false end.

Lemma observed_word_location_check_apart first second :
  location_chunk first=Mint32 -> location_chunk second=Mint32 ->
  (4|location_offset first) -> (4|location_offset second) ->
  observed_word_location_check first second=true -> location_disjoint first second.
Proof.
  intros FIRST SECOND [left LEFT] [right RIGHT] CHECK.
  unfold observed_word_location_check in CHECK; apply negb_true_iff in CHECK.
  apply andb_false_iff in CHECK as [BLOCKS|OFFSETS]; unfold location_disjoint.
  - left; apply Pos.eqb_neq; exact BLOCKS.
  - apply Z.eqb_neq in OFFSETS; rewrite FIRST,SECOND; cbn [size_chunk].
    right; rewrite LEFT,RIGHT in *; lia.
Qed.

Theorem observed_word_cell_check_sound locations memory cell observation write :
  memory_cell_capable locations memory cell -> locations cell=Some write ->
  location_chunk observation=Mint32 -> (4|location_offset observation) ->
  observed_word_cell_check locations observation cell=true -> location_disjoint write observation.
Proof.
  intros [actual [RESOLVE [CHUNK [VALID ALIGN]]]] WRITE OBSERVED OBSERVED_ALIGN CHECK.
  assert(actual=write) by congruence; subst actual.
  unfold observed_word_cell_check in CHECK; rewrite WRITE in CHECK.
  eapply observed_word_location_check_apart; eassumption.
Qed.

Theorem observed_word_cell_check_evaluation code locations cell ge locals checked memory pointer block offset loaded :
  memory_cell_address_binding code locations(Entry ge locals checked memory) cell ->
  checked!pointer=Some(Vptr block offset) -> Mem.loadv Mint32 memory(Vptr block offset)=Some loaded ->
  expression_test (memory_pointer_cells_test(code cell)(signed_pointer_temp pointer))
    (Entry ge locals checked memory)
    (observed_word_cell_check locations(MemoryLocation Mint32 block(Ptrofs.unsigned offset)) cell).
Proof.
  intros [write [address BINDING]] POINTER READ.
  destruct BINDING as [RESOLVE [CHUNK [OFFSET [PURE [TYPE [EVAL [VALID ALIGN]]]]]]].
  unfold observed_word_cell_check; rewrite RESOLVE.
  unfold observed_word_location_check; cbn [location_block location_offset]; rewrite OFFSET.
  rewrite <-memory_pointer_eq_unsigned.
  eapply memory_pointer_cells_test_evaluation;
    [exact TYPE|reflexivity|exact EVAL|constructor; exact POINTER|exact VALID|].
  eapply loaded_address_valid; exact READ.
Qed.

Print Assumptions observed_word_location_check_apart.
Print Assumptions observed_word_cell_check_sound.
Print Assumptions observed_word_cell_check_evaluation.
