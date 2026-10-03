From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightPureExpr ClightRectangularStore.
From GuardMemory Require Import GuardMemoryArrayBackend.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The source adapter needs both directions: machine evaluation corresponds
    to an affine integer value, and a defined source bound establishes that
    every eagerly read parameter contains an integer word. *)
Inductive memory_source_affine :=
| MemorySourceTemp (identifier : ident)
| MemorySourceConstant (value : Z)
| MemorySourceAdd (first second : memory_source_affine)
| MemorySourceSub (first second : memory_source_affine)
| MemorySourceScale (factor : Z) (value : memory_source_affine)
| MemorySourceScaleLeft (factor : Z) (value : memory_source_affine).
Fixpoint memory_source_affine_code expression :=
  match expression with
  | MemorySourceTemp identifier => Etempvar identifier type_int32s
  | MemorySourceConstant value => rect_constant value
  | MemorySourceAdd first second => operand_sum (memory_source_affine_code first) (memory_source_affine_code second)
  | MemorySourceSub first second => Ebinop Osub (memory_source_affine_code first) (memory_source_affine_code second) type_int32s
  | MemorySourceScale factor value => operand_product (memory_source_affine_code value) factor
  | MemorySourceScaleLeft factor value => Ebinop Omul (rect_constant factor) (memory_source_affine_code value) type_int32s end.
Fixpoint memory_source_affine_math (valuation : ident -> Z) expression :=
  match expression with
  | MemorySourceTemp identifier => valuation identifier
  | MemorySourceConstant value => value
  | MemorySourceAdd first second => memory_source_affine_math valuation first + memory_source_affine_math valuation second
  | MemorySourceSub first second => memory_source_affine_math valuation first - memory_source_affine_math valuation second
  | MemorySourceScale factor value => memory_source_affine_math valuation value * factor
  | MemorySourceScaleLeft factor value => factor * memory_source_affine_math valuation value end.
Fixpoint memory_source_affine_reads expression :=
  match expression with
  | MemorySourceTemp identifier => [identifier]
  | MemorySourceConstant _ => []
  | MemorySourceAdd first second | MemorySourceSub first second =>
    memory_source_affine_reads first ++ memory_source_affine_reads second
  | MemorySourceScale _ value | MemorySourceScaleLeft _ value => memory_source_affine_reads value end.
Lemma memory_source_affine_type expression : typeof (memory_source_affine_code expression) = type_int32s.
Proof. destruct expression; cbn [memory_source_affine_code]; try reflexivity; apply rect_constant_type. Qed.
Lemma memory_source_affine_pure expression : pure_scalar (memory_source_affine_code expression).
Proof.
  induction expression; cbn [memory_source_affine_code operand_sum operand_product].
  - constructor.
  - unfold rect_constant; destruct (value <? 0); repeat constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; [exact IHexpression|unfold rect_constant; destruct (factor <? 0); repeat constructor].
  - constructor; [unfold rect_constant; destruct (factor <? 0); repeat constructor|exact IHexpression].
Qed.
Lemma memory_source_integer_subtract x y : Int.sub (Int.repr x) (Int.repr y) = Int.repr (x-y).
Proof. unfold Int.sub; apply Int.eqm_samerepr,Int.eqm_sub; apply Int.eqm_sym,Int.eqm_unsigned_repr. Qed.
Theorem memory_source_affine_evaluation expression valuation ge locals temps memory :
  (forall identifier, In identifier (memory_source_affine_reads expression) ->
    temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  eval_expr ge locals temps memory (memory_source_affine_code expression)
    (Vint (Int.repr (memory_source_affine_math valuation expression))).
Proof.
  induction expression; intro WORDS; cbn [memory_source_affine_code memory_source_affine_math].
  - constructor; apply WORDS; cbn; auto.
  - apply rect_constant_evaluation.
  - apply operand_sum_evaluation; try apply memory_source_affine_type;
      [apply IHexpression1|apply IHexpression2]; intros identifier MEMBER;
      apply WORDS; apply in_or_app; auto.
  - eapply eval_Ebinop with (v1 := Vint (Int.repr (memory_source_affine_math valuation expression1)))
      (v2 := Vint (Int.repr (memory_source_affine_math valuation expression2))).
    + apply IHexpression1; intros identifier MEMBER; apply WORDS,in_or_app; auto.
    + apply IHexpression2; intros identifier MEMBER; apply WORDS,in_or_app; auto.
    + rewrite !memory_source_affine_type.
      change (Some (Vint (Int.sub (Int.repr (memory_source_affine_math valuation expression1))
        (Int.repr (memory_source_affine_math valuation expression2)))) =
        Some (Vint (Int.repr (memory_source_affine_math valuation expression1-memory_source_affine_math valuation expression2)))).
      rewrite memory_source_integer_subtract; reflexivity.
  - apply operand_product_evaluation; [apply memory_source_affine_type|apply IHexpression; exact WORDS].
  - eapply eval_Ebinop with (v1 := Vint (Int.repr factor))
      (v2 := Vint (Int.repr (memory_source_affine_math valuation expression))).
    + apply rect_constant_evaluation.
    + apply IHexpression; exact WORDS.
    + rewrite rect_constant_type,memory_source_affine_type.
      change (Some (Vint (Int.mul (Int.repr factor) (Int.repr (memory_source_affine_math valuation expression)))) =
        Some (Vint (Int.repr (factor * memory_source_affine_math valuation expression)))).
      rewrite rect_integer_multiply; reflexivity.
Qed.

Lemma memory_source_binary_words ge op first second memory result :
  op = Oadd \/ op = Osub \/ op = Omul ->
  sem_binary_operation ge op first type_int32s second type_int32s memory = Some (Vint result) ->
  exists a b, first = Vint a /\ second = Vint b.
Proof.
  intros [SAME|[SAME|SAME]]; subst op; destruct first,second; cbn; try discriminate; eauto.
Qed.
Theorem memory_source_affine_defined_words expression ge locals temps memory result :
  eval_expr ge locals temps memory (memory_source_affine_code expression) (Vint result) ->
  forall identifier, In identifier (memory_source_affine_reads expression) ->
    exists word, temps ! identifier = Some (Vint word).
Proof.
  revert result; induction expression; intros result RUN read MEMBER.
  - cbn in MEMBER; destruct MEMBER as [<-|[]]; exists result; eapply scalar_temp_inv; exact RUN.
  - contradiction.
  - apply scalar_binary_inv in RUN as [first [second [FIRST [SECOND OP]]]].
    rewrite !memory_source_affine_type in OP.
    destruct (@memory_source_binary_words ge Oadd first second memory result ltac:(auto) OP) as [a [b [-> ->]]].
    apply in_app_or in MEMBER as [MEMBER|MEMBER]; [eapply IHexpression1|eapply IHexpression2]; eassumption.
  - apply scalar_binary_inv in RUN as [first [second [FIRST [SECOND OP]]]].
    rewrite !memory_source_affine_type in OP.
    destruct (@memory_source_binary_words ge Osub first second memory result ltac:(auto) OP) as [a [b [-> ->]]].
    apply in_app_or in MEMBER as [MEMBER|MEMBER]; [eapply IHexpression1|eapply IHexpression2]; eassumption.
  - apply scalar_binary_inv in RUN as [first [second [FIRST [SECOND OP]]]].
    rewrite memory_source_affine_type,rect_constant_type in OP.
    destruct (@memory_source_binary_words ge Omul first second memory result ltac:(auto) OP) as [a [b [-> ->]]].
    eapply IHexpression; eassumption.
  - apply scalar_binary_inv in RUN as [first [second [FIRST [SECOND OP]]]].
    rewrite rect_constant_type,memory_source_affine_type in OP.
    destruct (@memory_source_binary_words ge Omul first second memory result ltac:(auto) OP) as [a [b [-> ->]]].
    eapply IHexpression; eassumption.
Qed.
Print Assumptions memory_source_affine_defined_words.
Print Assumptions memory_source_affine_evaluation.
