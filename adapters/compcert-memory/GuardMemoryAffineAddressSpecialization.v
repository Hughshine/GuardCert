From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightPureExpr ClightCountedLoop.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryPointerAccess
  GuardMemoryBufferOffsets.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Coordinate substitution creates address probes in the original entry
    environment. It does not overwrite public loop counters or execute stores.
    Other affine parameters remain runtime reads of their original temporaries. *)
Fixpoint memory_affine_at row column i j expression :=
  match expression with
  | MemorySourceTemp identifier =>
      if peq identifier row then MemorySourceConstant i else
      if peq identifier column then MemorySourceConstant j else expression
  | MemorySourceConstant _ => expression
  | MemorySourceAdd first second => MemorySourceAdd
      (memory_affine_at row column i j first) (memory_affine_at row column i j second)
  | MemorySourceSub first second => MemorySourceSub
      (memory_affine_at row column i j first) (memory_affine_at row column i j second)
  | MemorySourceScale factor value => MemorySourceScale factor (memory_affine_at row column i j value)
  | MemorySourceScaleLeft factor value => MemorySourceScaleLeft factor (memory_affine_at row column i j value)
  end.
Definition memory_affine_at_value row column i j (valuation : ident -> Z) identifier :=
  if peq identifier row then i else if peq identifier column then j else valuation identifier.

Lemma memory_affine_at_math row column i j expression valuation :
  memory_source_affine_math valuation (memory_affine_at row column i j expression) =
  memory_source_affine_math (memory_affine_at_value row column i j valuation) expression.
Proof.
  induction expression; cbn [memory_affine_at memory_source_affine_math];
    try rewrite IHexpression1,IHexpression2; try rewrite IHexpression; try reflexivity.
  unfold memory_affine_at_value; destruct (peq identifier row); [reflexivity|].
  destruct (peq identifier column); reflexivity.
Qed.

Lemma memory_affine_at_reads row column i j expression identifier :
  In identifier (memory_source_affine_reads (memory_affine_at row column i j expression)) ->
  In identifier (memory_source_affine_reads expression) /\ identifier <> row /\ identifier <> column.
Proof.
  induction expression; cbn [memory_affine_at memory_source_affine_reads].
  - destruct (peq identifier0 row) as [SAME|OTHER]; [contradiction|].
    destruct (peq identifier0 column) as [SAME|ANOTHER]; [contradiction|].
    intros [SAME|[]]; subst identifier; split; [cbn; auto|split; assumption].
  - contradiction.
  - intro MEMBER; apply in_app_or in MEMBER as [MEMBER|MEMBER].
    + destruct (IHexpression1 MEMBER) as [READ REST]; split; [apply in_or_app; auto|exact REST].
    + destruct (IHexpression2 MEMBER) as [READ REST]; split; [apply in_or_app; auto|exact REST].
  - intro MEMBER; apply in_app_or in MEMBER as [MEMBER|MEMBER].
    + destruct (IHexpression1 MEMBER) as [READ REST]; split; [apply in_or_app; auto|exact REST].
    + destruct (IHexpression2 MEMBER) as [READ REST]; split; [apply in_or_app; auto|exact REST].
  - exact IHexpression.
  - exact IHexpression.
Qed.

Theorem memory_affine_at_evaluation row column i j expression valuation ge locals temps memory :
  (forall identifier, In identifier (memory_source_affine_reads expression) ->
    identifier <> row -> identifier <> column ->
    temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  eval_expr ge locals temps memory
    (memory_source_affine_code (memory_affine_at row column i j expression))
    (Vint (Int.repr (memory_source_affine_math (memory_affine_at_value row column i j valuation) expression))).
Proof.
  intro WORDS; rewrite <- memory_affine_at_math; apply memory_source_affine_evaluation.
  intros identifier MEMBER; destruct (@memory_affine_at_reads row column i j expression identifier MEMBER)
    as [READ [ROW COLUMN]]; apply WORDS; assumption.
Qed.

Definition memory_affine_address_at row column i j pointer expression :=
  Ebinop Oadd (Etempvar pointer (Tpointer type_int32s noattr))
    (memory_source_affine_code (memory_affine_at row column i j expression)) (Tpointer type_int32s noattr).

Theorem memory_affine_address_at_evaluation row column i j pointer expression valuation ge locals temps memory block base :
  temps ! pointer = Some (Vptr block base) ->
  (forall identifier, In identifier (memory_source_affine_reads expression) ->
    identifier <> row -> identifier <> column ->
    temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  signed_range (memory_source_affine_math (memory_affine_at_value row column i j valuation) expression) ->
  eval_expr ge locals temps memory (memory_affine_address_at row column i j pointer expression)
    (Vptr block (Ptrofs.add base (Ptrofs.repr
      (4*memory_source_affine_math (memory_affine_at_value row column i j valuation) expression)))).
Proof.
  intros POINTER WORDS RANGE; unfold memory_affine_address_at.
  eapply eval_Ebinop; [constructor; exact POINTER|apply memory_affine_at_evaluation; exact WORDS|].
  cbn [typeof]; rewrite memory_source_affine_type; apply memory_pointer_add; exact RANGE.
Qed.

Print Assumptions memory_affine_at_math.
Print Assumptions memory_affine_at_reads.
Print Assumptions memory_affine_at_evaluation.
Print Assumptions memory_affine_address_at_evaluation.
