From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From polcert.lib Require Import Linalg.
From Guard Require Import ClightSyntaxEquality.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryLongControl
  GuardMemoryDoubleAffineLong GuardMemoryAffineSourceExpressions GuardMemoryNaryAffineExpressions
  GuardMemoryLongSourceAffine GuardMemoryDoubleHeaderFrame.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The distinguished coordinate is an actual global observation. The other
    coordinates are actual source temporaries. The operation tree is retained. *)
Fixpoint long_header_affine_code header expression := match expression with
| LongSourceTemp identifier => if Pos.eqb identifier header
    then Evar identifier memory_long_type else Etempvar identifier memory_long_type
| LongSourceLiteral value => Econst_long value memory_long_type
| LongSourceCastI32 value => Ecast (Econst_int value memory_signed_int_type) memory_long_type
| LongSourceBinary operation first second => Ebinop
    (match operation with LongSourceSum => Oadd | LongSourceDifference => Osub end)
    (long_header_affine_code header first) (long_header_affine_code header second) memory_long_type
| LongSourceConstantBinary operation on_left constant child =>
    long_source_constant_binary_code operation on_left constant (long_header_affine_code header child)
end.
Lemma long_header_affine_type header expression :
  typeof (long_header_affine_code header expression)=memory_long_type.
Proof.
  destruct expression; cbn; try reflexivity.
  - destruct (Pos.eqb identifier header); reflexivity.
  - destruct on_left; reflexivity.
Qed.
Theorem long_header_affine_execution header expression valuation ge locals temps memory :
  eval_expr ge locals temps memory (Evar header memory_long_type)
    (Vlong (Int64.repr (valuation header))) ->
  (forall identifier, In identifier (memory_source_affine_reads (long_source_affine_math expression)) ->
    identifier<>header -> temps ! identifier=Some (Vlong (Int64.repr (valuation identifier)))) ->
  eval_expr ge locals temps memory (long_header_affine_code header expression)
    (Vlong (Int64.repr (memory_source_affine_math valuation (long_source_affine_math expression)))).
Proof.
  intro HEADER; induction expression; intro WORDS;
    cbn [long_header_affine_code long_source_affine_math memory_source_affine_math].
  - destruct (Pos.eqb identifier header) eqn:SAME.
    + apply Pos.eqb_eq in SAME; subst identifier; exact HEADER.
    + constructor; apply WORDS; [cbn; auto|apply Pos.eqb_neq; exact SAME].
  - rewrite Int64.repr_signed; constructor.
  - eapply eval_Ecast; [constructor|reflexivity].
  - destruct operation; cbn [memory_source_affine_math].
    + apply double_long_add_execution; [apply long_header_affine_type|apply long_header_affine_type| |].
      * apply IHexpression1; intros id MEMBER DIFFERENT; apply WORDS; [apply in_or_app; auto|exact DIFFERENT].
      * apply IHexpression2; intros id MEMBER DIFFERENT; apply WORDS; [apply in_or_app; auto|exact DIFFERENT].
    + eapply eval_Ebinop.
      * apply IHexpression1; intros id MEMBER DIFFERENT; apply WORDS; [apply in_or_app; auto|exact DIFFERENT].
      * apply IHexpression2; intros id MEMBER DIFFERENT; apply WORDS; [apply in_or_app; auto|exact DIFFERENT].
      * rewrite !long_header_affine_type;
          change (Some (Vlong (Int64.sub
            (Int64.repr (memory_source_affine_math valuation (long_source_affine_math expression1)))
            (Int64.repr (memory_source_affine_math valuation (long_source_affine_math expression2))))) =
            Some (Vlong (Int64.repr
              (memory_source_affine_math valuation (long_source_affine_math expression1)-
               memory_source_affine_math valuation (long_source_affine_math expression2)))));
          rewrite long_source_repr_sub; reflexivity.
  - rewrite long_source_constant_binary_math_value; apply long_source_constant_binary_execution;
      [apply long_header_affine_type|].
    apply IHexpression; intros id MEMBER DIFFERENT; apply WORDS; [|exact DIFFERENT].
    cbn [long_source_affine_math]; rewrite long_source_constant_binary_reads; exact MEMBER.
Qed.

(** This proposal is only a parser aid. Reconstruction against the original
    expression is the authority; no source rewriting is performed here. *)
Fixpoint propose_header_coordinate header code := match code with
| Evar identifier ty => if Pos.eqb identifier header then Etempvar identifier ty else code
| Ecast child ty => Ecast (propose_header_coordinate header child) ty
| Ebinop operation first second ty => Ebinop operation
    (propose_header_coordinate header first) (propose_header_coordinate header second) ty
| _ => code end.
Definition describe_long_header_affine header source :=
  match propose_long_source_affine (propose_header_coordinate header source) with
  | Some expression => if expression_eq source (long_header_affine_code header expression)
      then Some expression else None
  | None => None end.
Lemma describe_long_header_affine_exact header source expression :
  describe_long_header_affine header source=Some expression ->
  source=long_header_affine_code header expression.
Proof.
  unfold describe_long_header_affine.
  destruct (propose_long_source_affine (propose_header_coordinate header source)) as [proposed|]; [|discriminate].
  destruct (expression_eq source (long_header_affine_code header proposed)) as [EXACT|]; [|discriminate].
  intro RESULT; inversion RESULT; subst proposed; exact EXACT.
Qed.
Definition decode_long_header_index header layout source : option constraint :=
  match describe_long_header_affine header source with
  | Some expression => memory_encode_nary_index layout (long_source_affine_math expression)
  | None => None end.
Theorem decoded_long_header_index_execution header layout source term valuation ge locals temps memory :
  decode_long_header_index header layout source=Some term ->
  eval_expr ge locals temps memory (Evar header memory_long_type)
    (Vlong (Int64.repr (valuation header))) ->
  (forall identifier, In identifier layout -> identifier<>header ->
    temps ! identifier=Some (Vlong (Int64.repr (valuation identifier)))) ->
  typeof source=memory_long_type /\ eval_expr ge locals temps memory source
    (Vlong (Int64.repr (memory_nary_index_value term (map valuation layout)))).
Proof.
  unfold decode_long_header_index.
  destruct (describe_long_header_affine header source) as [expression|] eqn:DESCRIBE; [|discriminate].
  intros ENCODE HEADER WORDS; rewrite (@describe_long_header_affine_exact header source expression DESCRIBE).
  split; [apply long_header_affine_type|].
  replace (memory_nary_index_value term (map valuation layout))
    with (memory_source_affine_math valuation (long_source_affine_math expression))
    by exact (@memory_encode_nary_index_value (long_source_affine_math expression) layout term valuation ENCODE).
  apply long_header_affine_execution; [exact HEADER|].
  intros identifier MEMBER DIFFERENT; apply WORDS; [|exact DIFFERENT].
  eapply memory_encode_nary_index_reads; eassumption.
Qed.
Fixpoint decode_long_header_indices header layout codes := match codes with
| [] => Some []
| code::rest => match decode_long_header_index header layout code,decode_long_header_indices header layout rest with
    | Some row,Some rows => Some (row::rows) | _,_ => None end end.
Theorem decoded_long_header_indices_execution header layout codes rows valuation ge locals temps memory :
  decode_long_header_indices header layout codes=Some rows ->
  eval_expr ge locals temps memory (Evar header memory_long_type)
    (Vlong (Int64.repr (valuation header))) ->
  (forall identifier, In identifier layout -> identifier<>header ->
    temps ! identifier=Some (Vlong (Int64.repr (valuation identifier)))) ->
  Forall2 (fun code value => typeof code=memory_long_type /\
    eval_expr ge locals temps memory code (Vlong (Int64.repr value))) codes (affine_product rows (map valuation layout)).
Proof.
  intro ENCODE; revert rows ENCODE; induction codes as [|code rest IH]; intros rows ENCODE HEADER WORDS;
    cbn [decode_long_header_indices] in ENCODE.
  - inversion ENCODE; constructor.
  - destruct (decode_long_header_index header layout code) as [row|] eqn:ROW; [|discriminate].
    destruct (decode_long_header_indices header layout rest) as [tail|] eqn:TAIL; [|discriminate].
    inversion ENCODE; subst rows; cbn [affine_product map]; constructor.
    + eapply decoded_long_header_index_execution; eassumption.
    + apply IH; [reflexivity|exact HEADER|exact WORDS].
Qed.

Print Assumptions long_header_affine_execution.
Print Assumptions describe_long_header_affine_exact.
Print Assumptions decoded_long_header_index_execution.
Print Assumptions decoded_long_header_indices_execution.
