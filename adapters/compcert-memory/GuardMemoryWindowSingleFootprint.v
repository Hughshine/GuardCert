From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryLoopTrace
  GuardMemoryFootprintRestriction GuardMemoryScalarLoops GuardMemoryNaryLoops GuardMemoryStartedScalarLoop
  GuardMemoryInstructionPadding GuardMemoryNaryCompute GuardMemoryNaryAffineAccess GuardMemoryMultiPointerIdentifiers.
Import ListNotations.
Set Implicit Arguments.
Definition window_instruction_single pointer instruction :=
  fst (instruction_write instruction) = pointer /\
  Forall (fun access => fst access = pointer) (instruction_reads instruction).
Fixpoint window_loop_single pointer (loop : L.stmt) : Prop :=
  match loop with
  | L.Instr instruction _ => window_instruction_single pointer instruction
  | L.Seq loops => window_list_single pointer loops
  | L.Guard _ body => window_loop_single pointer body
  | L.Loop _ _ body => window_loop_single pointer body
  end
with window_list_single pointer (loops : L.stmt_list) : Prop :=
  match loops with
  | L.SNil => True
  | L.SCons first rest => window_loop_single pointer first /\ window_list_single pointer rest
  end.
Lemma window_instruction_single_cells pointer instruction values :
  window_instruction_single pointer instruction ->
  memory_instruction_cells_covered (fun cell => Pos.eqb (arr_id cell) pointer) instruction values.
Proof.
  intros [WRITE READS].
  assert (ARRAY : forall access values, arr_id (exact_cell access values) = fst access).
  { intros [identifier rows] point; reflexivity. }
  unfold memory_instruction_cells_covered; split.
  - rewrite ARRAY,WRITE; apply Pos.eqb_refl.
  - apply Forall_forall; intros cell MEMBER; apply in_map_iff in MEMBER as [access [<- MEMBER]].
    rewrite ARRAY; apply Pos.eqb_eq.
    apply Forall_forall with (x := access) in READS; assumption.
Qed.
Theorem window_single_trace_covered pointer :
  (forall loop, window_loop_single pointer loop -> forall values,
    memory_loop_cells_covered (fun cell => Pos.eqb (arr_id cell) pointer) loop values) /\
  (forall loops, window_list_single pointer loops -> forall values,
    Forall (fun event => memory_instruction_cells_covered (fun cell => Pos.eqb (arr_id cell) pointer)
      (event_instruction event) (event_arguments event)) (memory_loop_list_trace loops values)).
Proof.
  apply trace_stmt_list_ind.
  - intros lower upper body IH COVERED values; unfold memory_loop_cells_covered; cbn [memory_loop_trace].
    apply Forall_forall; intros event MEMBER; apply in_flat_map in MEMBER as [point [_ MEMBER]].
    pose proof (IH COVERED (point::values)) as CHILD; apply Forall_forall with (x := event) in CHILD; assumption.
  - intros instruction arguments COVERED values; unfold memory_loop_cells_covered; cbn [memory_loop_trace].
    constructor; [apply window_instruction_single_cells; exact COVERED|constructor].
  - intros loops IH COVERED values; apply IH; exact COVERED.
  - intros test body IH COVERED values; unfold memory_loop_cells_covered; cbn [memory_loop_trace].
    destruct (L.eval_test values test); [apply IH; exact COVERED|constructor].
  - intros COVERED values; constructor.
  - intros first IH rest REST [FIRST TAIL] values; cbn [memory_loop_list_trace]; apply Forall_app; split.
    + apply IH; exact FIRST.
    + apply REST; exact TAIL.
Qed.
Lemma window_pad_single pointer extra instruction :
  window_instruction_single pointer instruction -> window_instruction_single pointer (memory_pad_instruction extra instruction).
Proof.
  intros [WRITE READS]; split; [exact WRITE|].
  cbn [memory_pad_instruction instruction_reads]; apply Forall_map.
  eapply Forall_impl; [|exact READS]; intros access OWNED; exact OWNED.
Qed.
Lemma window_operation_single pointer operation :
  memory_multi_pointer_operation_covered [pointer] operation ->
  window_instruction_single pointer (memory_nary_compute_instruction operation).
Proof.
  intros [WRITE READS]; split.
  - change (memory_nary_access_array (memory_nary_compute_write operation) = pointer); cbn in WRITE; intuition.
  - cbn [memory_nary_compute_instruction instruction_reads]; apply Forall_map.
    eapply Forall_impl; [|exact READS]; intros access OWNED; change (memory_nary_access_array access = pointer); cbn in OWNED; intuition.
Qed.
Print Assumptions window_single_trace_covered.
Lemma window_scalar_sequence_single pointer depth scalars instructions :
  Forall (window_instruction_single pointer) instructions ->
  window_list_single pointer (memory_scalar_instruction_sequence depth scalars instructions).
Proof. intro COVERED; induction COVERED; cbn; [exact I|split; assumption]. Qed.
Lemma window_scalar_rectangle_single pointer dimensions instructions :
  Forall (window_instruction_single pointer) instructions -> forall depth scalars,
  window_loop_single pointer (memory_scalar_rectangle depth dimensions scalars instructions).
Proof.
  intro COVERED; induction dimensions; intros depth scalars; cbn.
  - apply window_scalar_sequence_single; exact COVERED.
  - apply IHdimensions.
Qed.
Theorem window_started_scalar_single_covered pointer dimensions scalars extra operations values :
  Forall (memory_multi_pointer_operation_covered [pointer]) operations ->
  memory_loop_cells_covered (fun cell => Pos.eqb (arr_id cell) pointer)
    (memory_started_scalar_loop dimensions scalars
      (memory_pad_instructions extra (map memory_nary_compute_instruction operations))) values.
Proof.
  intro COVERED; apply (proj1 (window_single_trace_covered pointer)).
  cbn [memory_started_scalar_loop window_loop_single]; apply window_scalar_rectangle_single.
  unfold memory_pad_instructions; rewrite map_map; apply Forall_map.
  eapply Forall_impl; [|exact COVERED]; intros operation OWNED.
  apply window_pad_single,window_operation_single; exact OWNED.
Qed.
Print Assumptions window_started_scalar_single_covered.
