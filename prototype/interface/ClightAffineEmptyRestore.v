From Stdlib Require Import List ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation
  GuardMemoryParametricSourceClight GuardMemoryParametricRestore.
From GuardInterface Require Import ClightAffineEmptyExecution.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Restore the actual empty child exit. The old nonnegative-child restore
    sets the public child counter to its bound, which is wrong for a negative
    bound. This successor explicitly restores it to zero. *)
Definition affine_empty_restore row bound column inner_bound expression:=
  Ssequence(memory_parametric_restore row bound column inner_bound expression)(rectangle_reset column).

Theorem affine_empty_restore_execution fe ge locals temps memory row bound column inner_bound expression valuation N :
  row<>bound -> row<>column -> row<>inner_bound -> bound<>column -> bound<>inner_bound ->
  column<>inner_bound -> temps!bound=Some(Vint(Int.repr N)) ->
  (forall id,In id(memory_source_affine_parameters row expression) ->
    temps!id=Some(Vint(Int.repr(valuation id)))) ->
  exec_stmt fe ge locals temps memory(affine_empty_restore row bound column inner_bound expression)E0
    (PTree.set row(Vint(Int.repr N))(affine_empty_settle column inner_bound
      (fun i=>memory_source_affine_math(memory_source_set_valuation valuation row i)expression)(N-1)temps))
    memory Out_normal.
Proof.
  intros RN RC RK NC NK CK BOUND WORDS.
  pose(upper:=fun i=>memory_source_affine_math(memory_source_set_valuation valuation row i)expression).
  pose(before:=PTree.set row(Vint(Int.repr N))(memory_parametric_settle column inner_bound upper(N-1)temps)).
  assert(EXIT:PTree.set column(Vint Int.zero)before=
    PTree.set row(Vint(Int.repr N))(affine_empty_settle column inner_bound upper(N-1)temps)).
  { unfold before,memory_parametric_settle,affine_empty_settle.
    apply PTree.extensionality; intro id; rewrite !PTree.gsspec.
    destruct(peq id row), (peq id column), (peq id inner_bound); try congruence; reflexivity. }
  fold upper; rewrite <-EXIT; unfold affine_empty_restore.
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=before)(m1:=memory).
  - exact(@memory_parametric_restore_execution fe ge locals temps memory row bound column inner_bound
      expression valuation N RN RC RK NC NK BOUND WORDS).
  - constructor; constructor.
Qed.

Lemma affine_empty_exit_frame live row column inner_bound upper N first second :
  temp_agree live first second ->
  temp_agree live
    (PTree.set row(Vint(Int.repr N))(affine_empty_settle column inner_bound upper(N-1)first))
    (PTree.set row(Vint(Int.repr N))(affine_empty_settle column inner_bound upper(N-1)second)).
Proof.
  unfold affine_empty_settle; intros FRAME id MEMBER; rewrite !PTree.gsspec.
  destruct(peq id row), (peq id column), (peq id inner_bound); auto.
Qed.

Print Assumptions affine_empty_restore_execution.
Print Assumptions affine_empty_exit_frame.
