From Stdlib Require Import List ZArith.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles GuardMemoryLoops GuardMemoryNaryCompute GuardMemoryNaryLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_pad_access extra (access : AccessFunction) : AccessFunction :=
  (fst access,map (fun term => (fst term++repeat 0 extra,snd term)) (snd access)).
Definition memory_pad_instruction extra instruction := MemoryInstruction
  (memory_pad_access extra (instruction_write instruction))
  (map (memory_pad_access extra) (instruction_reads instruction)) (instruction_value instruction).
Definition memory_pad_instructions extra instructions := map (memory_pad_instruction extra) instructions.
Lemma memory_dot_product_append_zeros coefficients extra values :
  dot_product (coefficients++repeat 0 extra) values = dot_product coefficients values.
Proof.
  rewrite dot_product_app_left,dot_product_repeat_zero_left,dot_product_resize_right; ring.
Qed.
Lemma memory_pad_access_cell extra access values : exact_cell (memory_pad_access extra access) values = exact_cell access values.
Proof.
  destruct access as [identifier rows]; unfold exact_cell,memory_pad_access; cbn [fst snd].
  unfold affine_product; rewrite map_map; f_equal.
  apply map_ext; intros [coefficients bias]; cbn; rewrite memory_dot_product_append_zeros; reflexivity.
Qed.
Lemma memory_pad_instruction_write_cells extra instruction values :
  memory_write_cells (memory_pad_instruction extra instruction) values = memory_write_cells instruction values.
Proof. unfold memory_write_cells; cbn [memory_pad_instruction instruction_write]; rewrite memory_pad_access_cell; reflexivity. Qed.
Lemma memory_pad_instruction_read_cells extra instruction values :
  memory_read_cells (memory_pad_instruction extra instruction) values = memory_read_cells instruction values.
Proof.
  unfold memory_read_cells; cbn [memory_pad_instruction instruction_reads]; rewrite map_map.
  apply map_ext; intro access; apply memory_pad_access_cell.
Qed.
Lemma memory_pad_instruction_semantics extra instruction values writes reads before after :
  GuardMemoryInstr.instr_semantics (memory_pad_instruction extra instruction) values writes reads before after <->
  GuardMemoryInstr.instr_semantics instruction values writes reads before after.
Proof.
  unfold GuardMemoryInstr.instr_semantics; cbn [memory_pad_instruction instruction_write instruction_reads instruction_value].
  rewrite memory_pad_access_cell,map_map.
  assert (READS : map (fun access => exact_cell (memory_pad_access extra access) values) (instruction_reads instruction) =
    map (fun access => exact_cell access values) (instruction_reads instruction))
    by (apply map_ext; intro access; apply memory_pad_access_cell).
  rewrite READS; reflexivity.
Qed.
Lemma memory_pad_instruction_point extra instruction values before after :
  memory_nary_point (memory_pad_instruction extra instruction) values before after <-> memory_nary_point instruction values before after.
Proof.
  unfold memory_nary_point; rewrite memory_pad_instruction_write_cells,memory_pad_instruction_read_cells.
  apply memory_pad_instruction_semantics.
Qed.
Theorem memory_pad_sequence_point extra instructions values : forall before after,
  memory_nary_sequence_point (memory_pad_instructions extra instructions) values before after <->
  memory_nary_sequence_point instructions values before after.
Proof.
  unfold memory_pad_instructions,memory_nary_sequence_point; induction instructions; intros before after; cbn; split; intro RUN.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; econstructor.
    + apply (proj1 (@memory_pad_instruction_point extra a values before _)); eassumption.
    + apply (proj1 (IHinstructions _ after)); eassumption.
  - inversion RUN; subst; econstructor.
    + apply (proj2 (@memory_pad_instruction_point extra a values before _)); eassumption.
    + apply (proj2 (IHinstructions _ after)); eassumption.
Qed.
Print Assumptions memory_pad_access_cell.
Print Assumptions memory_pad_sequence_point.
