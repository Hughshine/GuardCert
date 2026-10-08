From Stdlib Require Import List ZArith.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightStraightLine.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryAffineSourceExpressions
  GuardMemoryDynamicTensorBackend GuardMemoryTensorSource GuardMemoryMultiTensorSource GuardMemoryMultiTensorSequence.
Import ListNotations.
Set Implicit Arguments.

(** Untrusted metadata contains ordinary identifiers, affine coordinate syntax
    and value expressions. The checker creates every semantic source package. *)
Record multi_tensor_assignment_data := MultiTensorAssignmentData {
  mta_write : ident * list memory_source_affine;
  mta_reads : list (ident * list memory_source_affine);
  mta_value : value_expression
}.

Definition describe_multi_tensor_access dimensions layout (access : ident * list memory_source_affine) :=
  option_map (fun coordinates => (fst access,coordinates))
    (describe_tensor_source_access dimensions layout (snd access)).

Fixpoint describe_multi_tensor_accesses dimensions layout accesses :
    option (list (multi_tensor_source_access dimensions layout)) :=
  match accesses with
  | [] => Some []
  | access::rest => match describe_multi_tensor_access dimensions layout access,
      describe_multi_tensor_accesses dimensions layout rest with
    | Some head,Some tail => Some (head::tail)
    | _,_ => None end
  end.

Definition check_multi_tensor_assignment_data dimensions layout source data :=
  match describe_multi_tensor_access dimensions layout (mta_write data),
    describe_multi_tensor_accesses dimensions layout (mta_reads data) with
  | Some write,Some reads => @check_multi_tensor_source_statement dimensions layout source write reads (mta_value data)
  | _,_ => None end.

Fixpoint check_multi_tensor_body_data dimensions layout sources data :
    option (list (multi_tensor_source_statement dimensions layout)) :=
  match sources,data with
  | [],[] => Some []
  | source::sources,description::data =>
    match check_multi_tensor_assignment_data dimensions layout source description,
      check_multi_tensor_body_data dimensions layout sources data with
    | Some item,Some items => Some (item::items)
    | _,_ => None end
  | _,_ => None end.

Definition describe_multi_tensor_body dimensions layout source data :=
  check_multi_tensor_body_data dimensions layout (flatten_region source) data.

Lemma check_multi_tensor_assignment_data_exact dimensions layout source data item :
  check_multi_tensor_assignment_data dimensions layout source data = Some item -> mt_statement item = source.
Proof.
  unfold check_multi_tensor_assignment_data.
  destruct (describe_multi_tensor_access dimensions layout (mta_write data)) as [write|]; [|discriminate].
  destruct (describe_multi_tensor_accesses dimensions layout (mta_reads data)) as [reads|]; [|discriminate].
  unfold check_multi_tensor_source_statement.
  destruct (@check_multi_tensor_source_operation dimensions layout source write reads (mta_value data)) as [operation|];
    intro RUN; inversion RUN; reflexivity.
Qed.

Theorem check_multi_tensor_body_data_exact dimensions layout sources data items :
  check_multi_tensor_body_data dimensions layout sources data = Some items -> map mt_statement items = sources.
Proof.
  revert data items; induction sources as [|source sources IH]; intros [|description data] items RUN;
    cbn [check_multi_tensor_body_data] in RUN; try discriminate.
  - inversion RUN; reflexivity.
  - destruct (check_multi_tensor_assignment_data dimensions layout source description) as [item|] eqn:ITEM;
      [|discriminate].
    destruct (check_multi_tensor_body_data dimensions layout sources data) as [tail|] eqn:TAIL;
      [|discriminate].
    inversion RUN; subst items; cbn [map].
    rewrite (@check_multi_tensor_assignment_data_exact dimensions layout source description item ITEM),
      (IH data tail TAIL); reflexivity.
Qed.

Theorem describe_multi_tensor_body_exact dimensions layout source data items :
  describe_multi_tensor_body dimensions layout source data = Some items ->
  flatten_region source = map mt_statement items.
Proof. intro RUN; symmetry; eapply check_multi_tensor_body_data_exact; exact RUN. Qed.

Theorem check_multi_tensor_body_data_length dimensions layout sources data items :
  check_multi_tensor_body_data dimensions layout sources data = Some items -> length items = length data.
Proof.
  revert data items; induction sources as [|source sources IH]; intros [|description data] items RUN;
    cbn [check_multi_tensor_body_data] in RUN; try discriminate.
  - inversion RUN; reflexivity.
  - destruct (check_multi_tensor_assignment_data dimensions layout source description); [|discriminate].
    destruct (check_multi_tensor_body_data dimensions layout sources data) as [tail|] eqn:TAIL; [|discriminate].
    inversion RUN; subst; cbn; f_equal; eapply IH; exact TAIL.
Qed.

Print Assumptions check_multi_tensor_assignment_data_exact.
Print Assumptions check_multi_tensor_body_data_exact.
Print Assumptions describe_multi_tensor_body_exact.
Print Assumptions check_multi_tensor_body_data_length.
