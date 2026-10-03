From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightPureExpr ClightTempFrame.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_source_word_valuation temps identifier :=
  match temps ! identifier with Some (Vint word) => Int.signed word | _ => 0 end.
Theorem memory_source_affine_decode expression ge locals temps memory word :
  eval_expr ge locals temps memory (memory_source_affine_code expression) (Vint word) ->
  word = Int.repr (memory_source_affine_math (memory_source_word_valuation temps) expression).
Proof.
  intro RUN.
  assert (VALUE : eval_expr ge locals temps memory (memory_source_affine_code expression)
    (Vint (Int.repr (memory_source_affine_math (memory_source_word_valuation temps) expression)))).
  { apply memory_source_affine_evaluation; intros identifier MEMBER.
    destruct (@memory_source_affine_defined_words expression ge locals temps memory word RUN identifier MEMBER)
      as [value WORD].
    unfold memory_source_word_valuation; rewrite WORD,Int.repr_signed; reflexivity. }
  assert (SAME : Vint word = Vint (Int.repr (memory_source_affine_math (memory_source_word_valuation temps) expression)))
    by (eapply pure_scalar_determinate; [apply memory_source_affine_pure|exact RUN|exact VALUE]).
  inversion SAME; reflexivity.
Qed.
Definition memory_source_set_valuation (valuation : ident -> Z) row value identifier :=
  if peq identifier row then value else valuation identifier.
Fixpoint memory_source_row_coefficient row expression :=
  match expression with
  | MemorySourceTemp identifier => if peq identifier row then 1 else 0
  | MemorySourceConstant _ => 0
  | MemorySourceAdd first second => memory_source_row_coefficient row first + memory_source_row_coefficient row second
  | MemorySourceSub first second => memory_source_row_coefficient row first - memory_source_row_coefficient row second
  | MemorySourceScale factor value => memory_source_row_coefficient row value * factor
  | MemorySourceScaleLeft factor value => factor * memory_source_row_coefficient row value end.
Theorem memory_source_affine_row_linear expression valuation row value :
  memory_source_affine_math (memory_source_set_valuation valuation row value) expression =
    memory_source_affine_math (memory_source_set_valuation valuation row 0) expression +
    memory_source_row_coefficient row expression * value.
Proof.
  induction expression; cbn [memory_source_affine_math memory_source_row_coefficient].
  - unfold memory_source_set_valuation; destruct (peq identifier row); ring.
  - ring.
  - rewrite IHexpression1,IHexpression2; ring.
  - rewrite IHexpression1,IHexpression2; ring.
  - rewrite IHexpression; ring.
  - rewrite IHexpression; ring.
Qed.
Theorem memory_source_affine_row_extrema expression valuation row last low high :
  0 <= last ->
  low <= memory_source_affine_math (memory_source_set_valuation valuation row 0) expression <= high ->
  low <= memory_source_affine_math (memory_source_set_valuation valuation row last) expression <= high ->
  forall value, 0 <= value <= last ->
    low <= memory_source_affine_math (memory_source_set_valuation valuation row value) expression <= high.
Proof.
  intros LAST FIRST FINAL value RANGE.
  rewrite memory_source_affine_row_linear in FINAL|-*.
  destruct (Z_le_dec 0 (memory_source_row_coefficient row expression)); nia.
Qed.
Print Assumptions memory_source_affine_decode.
Print Assumptions memory_source_affine_row_extrema.

Definition memory_source_affine_parameters row expression :=
  filter (fun identifier => if peq identifier row then false else true) (memory_source_affine_reads expression).
Lemma memory_source_affine_parameter_member row expression identifier :
  In identifier (memory_source_affine_parameters row expression) <->
    In identifier (memory_source_affine_reads expression) /\ identifier <> row.
Proof.
  unfold memory_source_affine_parameters; rewrite filter_In.
  destruct (peq identifier row); cbn; intuition congruence.
Qed.
Theorem memory_source_affine_iteration_value expression valuation row value ge locals base temps memory :
  temps ! row = Some (Vint (Int.repr value)) ->
  (forall identifier, In identifier (memory_source_affine_parameters row expression) ->
    base ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  temp_agree (memory_source_affine_parameters row expression) base temps ->
  eval_expr ge locals temps memory (memory_source_affine_code expression)
    (Vint (Int.repr (memory_source_affine_math (memory_source_set_valuation valuation row value) expression))).
Proof.
  intros ROW WORDS FRAME; apply memory_source_affine_evaluation; intros identifier MEMBER.
  unfold memory_source_set_valuation; destruct (peq identifier row) as [->|OTHER]; [exact ROW|].
  assert (PARAMETER : In identifier (memory_source_affine_parameters row expression))
    by (apply memory_source_affine_parameter_member; auto).
  rewrite FRAME by exact PARAMETER; apply WORDS; exact PARAMETER.
Qed.
Print Assumptions memory_source_affine_iteration_value.
