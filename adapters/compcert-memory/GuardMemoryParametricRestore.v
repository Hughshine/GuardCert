From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightNoWrap ClightRectangularStore.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation GuardMemoryParametricSourceClight.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_parametric_restore row bound column inner_bound expression :=
  Ssequence (Sset row (Ebinop Oadd (Etempvar bound type_int32s) (Econst_int (Int.repr (-1)) type_int32s) type_int32s))
    (Ssequence (memory_parametric_setup inner_bound (memory_source_affine_code expression))
      (Ssequence (Sset column (Etempvar inner_bound type_int32s)) (Sset row (Etempvar bound type_int32s)))).
Lemma memory_parametric_restore_execution fe ge locals temps memory row bound column inner_bound expression valuation N :
  row <> bound -> row <> column -> row <> inner_bound -> bound <> column -> bound <> inner_bound ->
  temps ! bound = Some (Vint (Int.repr N)) ->
  (forall identifier, In identifier (memory_source_affine_parameters row expression) ->
    temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  exec_stmt fe ge locals temps memory (memory_parametric_restore row bound column inner_bound expression) E0
    (PTree.set row (Vint (Int.repr N))
      (memory_parametric_settle column inner_bound
        (fun i => memory_source_affine_math (memory_source_set_valuation valuation row i) expression) (N-1) temps)) memory Out_normal.
Proof.
  intros RN RC RK NC NK BOUND WORDS.
  set (last := memory_source_affine_math (memory_source_set_valuation valuation row (N-1)) expression).
  unfold memory_parametric_restore,memory_parametric_setup,memory_parametric_settle.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0)
    (le1 := PTree.set row (Vint (Int.repr (N-1))) temps) (m1 := memory).
  - constructor; eapply eval_Ebinop; [constructor; exact BOUND|constructor|].
    change (Some (Vint (Int.add (Int.repr N) (Int.repr (-1)))) = Some (Vint (Int.repr (N-1)))).
    rewrite rect_integer_add; replace (N + -1) with (N-1) by lia; reflexivity.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0)
      (le1 := PTree.set inner_bound (Vint (Int.repr last)) (PTree.set row (Vint (Int.repr (N-1))) temps)) (m1 := memory).
    + constructor; unfold last; apply memory_source_affine_evaluation; intros identifier MEMBER.
      unfold memory_source_set_valuation; destruct (peq identifier row) as [->|OTHER]; [apply PTree.gss|].
      rewrite PTree.gso by exact OTHER; apply WORDS,memory_source_affine_parameter_member; auto.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0)
        (le1 := PTree.set column (Vint (Int.repr last))
          (PTree.set inner_bound (Vint (Int.repr last)) (PTree.set row (Vint (Int.repr (N-1))) temps))) (m1 := memory).
      * constructor; constructor; apply PTree.gss.
      * assert (EXIT : PTree.set row (Vint (Int.repr N))
          (PTree.set column (Vint (Int.repr last)) (PTree.set inner_bound (Vint (Int.repr last))
            (PTree.set row (Vint (Int.repr (N-1))) temps))) =
          PTree.set row (Vint (Int.repr N)) (PTree.set column (Vint (Int.repr last)) (PTree.set inner_bound (Vint (Int.repr last)) temps))).
        { apply PTree.extensionality; intro identifier; rewrite !PTree.gsspec.
          destruct (peq identifier row), (peq identifier column), (peq identifier inner_bound); reflexivity. }
        cbn beta; fold last; rewrite <- EXIT; constructor; constructor; rewrite !PTree.gso by congruence; exact BOUND.
Qed.
Lemma memory_parametric_exit_frame live row column inner_bound N upper first second :
  temp_agree live first second ->
  temp_agree live (PTree.set row (Vint (Int.repr N)) (memory_parametric_settle column inner_bound upper (N-1) first))
    (PTree.set row (Vint (Int.repr N)) (memory_parametric_settle column inner_bound upper (N-1) second)).
Proof.
  unfold memory_parametric_settle; intros FRAME id MEMBER; rewrite !PTree.gsspec.
  destruct (peq id row), (peq id column), (peq id inner_bound); auto.
Qed.
Print Assumptions memory_parametric_restore_execution.
