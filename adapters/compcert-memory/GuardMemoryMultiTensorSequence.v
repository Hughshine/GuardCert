From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightFiniteRegion ClightStraightLine ClightLoopSyntax ClightRegionProgress ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryNaryLoops GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend GuardMemoryMultiTensorBackend GuardMemoryMultiTensorSource.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A heterogeneous list retains each checked source statement. These packages
    are checker output, not semantic callbacks supplied by a source user. *)
Record multi_tensor_source_statement dimensions layout := MultiTensorSourceStatement {
  mt_statement:statement;
  mt_operation:multi_tensor_source_operation dimensions layout mt_statement
}.
Arguments mt_statement {dimensions layout} _.
Arguments mt_operation {dimensions layout} _.
Definition mt_instruction dimensions layout(item:multi_tensor_source_statement dimensions layout) :=
  multi_tensor_source_instruction(mt_operation item).
Definition mt_available dimensions layout(item:multi_tensor_source_statement dimensions layout)values sizes :=
  Forall(fun access=>multi_tensor_source_available access values sizes)
    (mts_write(mt_operation item)::mts_reads(mt_operation item)).
Arguments mt_instruction {dimensions layout} item.
Arguments mt_available {dimensions layout} item values sizes.

Definition check_multi_tensor_source_statement dimensions layout source write reads value :
  option(multi_tensor_source_statement dimensions layout) :=
  match @check_multi_tensor_source_operation dimensions layout source write reads value with
  | Some operation=>Some(@MultiTensorSourceStatement dimensions layout source operation)
  | None=>None end.

Lemma multi_tensor_sequence_normal dimensions layout(items:list(multi_tensor_source_statement dimensions layout))body :
  flatten_region body=map mt_statement items -> normal_statement body=true.
Proof.
  intro BODY; apply flatten_normal_certificate; rewrite BODY; apply Forall_map,Forall_forall; intros item MEMBER.
  rewrite(mts_exact(mt_operation item)); reflexivity.
Qed.
Lemma multi_tensor_sequence_quiet dimensions layout(items:list(multi_tensor_source_statement dimensions layout))body :
  flatten_region body=map mt_statement items -> quiet_statement body=true.
Proof.
  intro BODY; apply flatten_quiet_certificate; rewrite BODY; apply Forall_map,Forall_forall; intros item MEMBER.
  rewrite(mts_exact(mt_operation item)); reflexivity.
Qed.
Lemma multi_tensor_sequence_writes dimensions layout(items:list(multi_tensor_source_statement dimensions layout))body :
  flatten_region body=map mt_statement items -> writes_only [] body.
Proof.
  intro BODY; apply flatten_writes_certificate; rewrite BODY; apply Forall_map,Forall_forall; intros item MEMBER.
  rewrite(mts_exact(mt_operation item)); constructor.
Qed.

Theorem multi_tensor_sequence_tail_decode dimensions layout
    (items:list(multi_tensor_source_statement dimensions layout))fe ge locals valuation sizes temps memory after final :
  tensor_layout_flag sizes=true -> tensor_dimension_view dimensions sizes temps ->
  (forall id,In id layout -> temps!id=Some(Vint(Int.repr(valuation id)))) ->
  Forall(fun item=>mt_available item(map valuation layout)sizes)items ->
  tail_execution fe ge locals(map mt_statement items)temps memory after final ->
  memory_nary_sequence_point(map mt_instruction items)(map valuation layout)
    (RuntimeState(multi_tensor_locations temps sizes)memory)(RuntimeState(multi_tensor_locations temps sizes)final) /\ after=temps.
Proof.
  intros LAYOUT DIMENSIONS WORDS AVAILABLE; revert memory after final;
    induction AVAILABLE as [|item items HEAD AVAILABLE IH]; intros memory after final RUN; cbn in RUN; inversion RUN; subst.
  - split; [constructor|reflexivity].
  - match goal with POINT:exec_stmt _ _ _ _ _ (mt_statement item) _ _ _ _ |- _=>
      destruct(@multi_tensor_source_operation_decode dimensions layout(mt_statement item)(mt_operation item)
        fe ge locals temps memory _ _ valuation sizes LAYOUT DIMENSIONS WORDS HEAD POINT)as [ACTION EXIT]; subst end.
    match goal with TAIL:tail_execution _ _ _ _ _ _ _ _ |- _=>
      destruct(IH _ _ _ TAIL)as [REST EXIT] end.
    split; [unfold memory_nary_sequence_point; cbn [map]; econstructor; eauto|exact EXIT].
Qed.

Theorem multi_tensor_body_source_decode dimensions layout body
    (items:list(multi_tensor_source_statement dimensions layout))fe ge locals valuation sizes temps memory after final :
  flatten_region body=map mt_statement items ->
  tensor_layout_flag sizes=true -> tensor_dimension_view dimensions sizes temps ->
  (forall id,In id layout -> temps!id=Some(Vint(Int.repr(valuation id)))) ->
  Forall(fun item=>mt_available item(map valuation layout)sizes)items ->
  exec_stmt fe ge locals temps memory body E0 after final Out_normal ->
  memory_nary_sequence_point(map mt_instruction items)(map valuation layout)
    (RuntimeState(multi_tensor_locations temps sizes)memory)(RuntimeState(multi_tensor_locations temps sizes)final) /\ after=temps.
Proof.
  intros BODY LAYOUT DIMENSIONS WORDS AVAILABLE SOURCE.
  apply flatten_region_execution in SOURCE; rewrite BODY in SOURCE.
  exact(@multi_tensor_sequence_tail_decode dimensions layout items fe ge locals valuation sizes temps memory after final
    LAYOUT DIMENSIONS WORDS AVAILABLE SOURCE).
Qed.

Print Assumptions check_multi_tensor_source_statement.
Print Assumptions multi_tensor_sequence_normal.
Print Assumptions multi_tensor_sequence_quiet.
Print Assumptions multi_tensor_sequence_writes.
Print Assumptions multi_tensor_sequence_tail_decode.
Print Assumptions multi_tensor_body_source_decode.
