From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightIndexedArray ClightRectangularStore.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record memory_affine_index := MemoryAffineIndex {
  memory_index_row : Z;
  memory_index_column : Z;
  memory_index_bias : Z
}.
Definition memory_index_value term i j :=
  memory_index_row term*i + memory_index_column term*j + memory_index_bias term.
Definition memory_index_add a b := MemoryAffineIndex
  (memory_index_row a+memory_index_row b)
  (memory_index_column a+memory_index_column b)
  (memory_index_bias a+memory_index_bias b).
Definition memory_index_scale factor a := MemoryAffineIndex
  (factor*memory_index_row a) (factor*memory_index_column a) (factor*memory_index_bias a).
Fixpoint memory_encode_index row column expression : option memory_affine_index :=
  match expression with
  | MemorySourceTemp identifier => if peq identifier row then Some (MemoryAffineIndex 1 0 0)
      else if peq identifier column then Some (MemoryAffineIndex 0 1 0) else None
  | MemorySourceConstant value => Some (MemoryAffineIndex 0 0 value)
  | MemorySourceAdd first second | MemorySourceSub first second =>
      match memory_encode_index row column first,memory_encode_index row column second with
      | Some first,Some second => Some (memory_index_add first
          (match expression with MemorySourceSub _ _ => memory_index_scale (-1) second | _ => second end))
      | _,_ => None end
  | MemorySourceScale factor value | MemorySourceScaleLeft factor value =>
      option_map (memory_index_scale factor) (memory_encode_index row column value)
  end.
Lemma memory_encode_index_value expression row column term valuation i j :
  memory_encode_index row column expression = Some term ->
  valuation row = i -> valuation column = j ->
  memory_source_affine_math valuation expression = memory_index_value term i j.
Proof.
  revert term; induction expression; intros term ENCODE ROW COLUMN; cbn [memory_encode_index] in ENCODE.
  - destruct (peq identifier row) as [->|OTHER].
    + inversion ENCODE; subst term; cbn [memory_source_affine_math memory_index_value]; rewrite ROW; unfold memory_index_value; cbn; ring.
    + destruct (peq identifier column) as [->|BAD]; [|discriminate].
      inversion ENCODE; subst term; cbn [memory_source_affine_math memory_index_value]; rewrite COLUMN; unfold memory_index_value; cbn; ring.
  - inversion ENCODE; subst term; cbn [memory_source_affine_math]; unfold memory_index_value; cbn; ring.
  - destruct (memory_encode_index row column expression1) as [first|] eqn:FIRST; [|discriminate].
    destruct (memory_encode_index row column expression2) as [second|] eqn:SECOND; [|discriminate].
    inversion ENCODE; subst term; cbn [memory_source_affine_math].
    rewrite (IHexpression1 _ eq_refl ROW COLUMN),(IHexpression2 _ eq_refl ROW COLUMN).
    unfold memory_index_value,memory_index_add; cbn; ring.
  - destruct (memory_encode_index row column expression1) as [first|] eqn:FIRST; [|discriminate].
    destruct (memory_encode_index row column expression2) as [second|] eqn:SECOND; [|discriminate].
    inversion ENCODE; subst term; cbn [memory_source_affine_math].
    rewrite (IHexpression1 _ eq_refl ROW COLUMN),(IHexpression2 _ eq_refl ROW COLUMN).
    unfold memory_index_value,memory_index_add,memory_index_scale; cbn; ring.
  - destruct (memory_encode_index row column expression) as [first|] eqn:FIRST; cbn in ENCODE; [|discriminate].
    inversion ENCODE; subst term; cbn [memory_source_affine_math].
    rewrite (IHexpression _ eq_refl ROW COLUMN); unfold memory_index_value,memory_index_scale; cbn; ring.
  - destruct (memory_encode_index row column expression) as [first|] eqn:FIRST; cbn in ENCODE; [|discriminate].
    inversion ENCODE; subst term; cbn [memory_source_affine_math].
    rewrite (IHexpression _ eq_refl ROW COLUMN); unfold memory_index_value,memory_index_scale; cbn; ring.
Qed.
Lemma memory_encode_index_reads expression row column term :
  memory_encode_index row column expression = Some term ->
  forall identifier, In identifier (memory_source_affine_reads expression) -> identifier = row \/ identifier = column.
Proof.
  revert term; induction expression; intros term ENCODE read MEMBER; cbn [memory_encode_index] in ENCODE.
  - cbn in MEMBER; destruct MEMBER as [<-|[]].
    destruct (peq identifier row); [auto|].
    destruct (peq identifier column); [auto|discriminate].
  - contradiction.
  - destruct (memory_encode_index row column expression1) as [first|] eqn:FIRST; [|discriminate].
    destruct (memory_encode_index row column expression2) as [second|] eqn:SECOND; [|discriminate].
    apply in_app_or in MEMBER as [MEMBER|MEMBER]; [eapply IHexpression1|eapply IHexpression2]; eauto.
  - destruct (memory_encode_index row column expression1) as [first|] eqn:FIRST; [|discriminate].
    destruct (memory_encode_index row column expression2) as [second|] eqn:SECOND; [|discriminate].
    apply in_app_or in MEMBER as [MEMBER|MEMBER]; [eapply IHexpression1|eapply IHexpression2]; eauto.
  - destruct (memory_encode_index row column expression) as [first|] eqn:FIRST; [|discriminate].
    eapply IHexpression; eauto.
  - destruct (memory_encode_index row column expression) as [first|] eqn:FIRST; [|discriminate].
    eapply IHexpression; eauto.
Qed.
Theorem memory_index_expression_evaluation expression row column term ge locals temps memory i j :
  row <> column -> memory_encode_index row column expression = Some term ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  eval_expr ge locals temps memory (memory_source_affine_code expression)
    (Vint (Int.repr (memory_index_value term i j))).
Proof.
  intros DISTINCT ENCODE ROW COLUMN.
  set (valuation := fun identifier => if peq identifier row then i else j).
  assert (VR : valuation row = i) by (unfold valuation; destruct (peq row row); congruence).
  assert (VC : valuation column = j) by (unfold valuation; destruct (peq column row); congruence).
  rewrite <- (@memory_encode_index_value expression row column term valuation i j ENCODE VR VC).
  apply memory_source_affine_evaluation; intros identifier MEMBER.
  destruct (@memory_encode_index_reads expression row column term ENCODE identifier MEMBER) as [SAME|SAME]; subst identifier;
    [rewrite VR; exact ROW|rewrite VC; exact COLUMN].
Qed.

Definition memory_affine_access_lvalue shape array expression :=
  indexed_array_lvalue shape array (memory_source_affine_code expression).
Lemma memory_affine_access_inverse shape array expression row column term ge locals temps memory i j block offset field :
  rectangle_layout_valid shape -> row <> column ->
  memory_encode_index row column expression = Some term ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  0 <= memory_index_value term i j < rectangle_extent shape ->
  eval_lvalue ge locals temps memory (memory_affine_access_lvalue shape array expression) block offset field ->
  rect_array_binding shape ge locals array block /\
    offset = Ptrofs.repr (4*memory_index_value term i j) /\ field = Full.
Proof.
  intros VALID DISTINCT ENCODE ROW COLUMN BOUND RUN.
  eapply indexed_array_lvalue_inverse; [exact VALID|apply memory_source_affine_type|
    apply memory_source_affine_pure|eapply memory_index_expression_evaluation; eassumption|exact BOUND|exact RUN].
Qed.
Lemma memory_affine_access_load_inverse shape array expression row column term ge locals temps memory i j value :
  rectangle_layout_valid shape -> row <> column ->
  memory_encode_index row column expression = Some term ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  0 <= memory_index_value term i j < rectangle_extent shape ->
  eval_expr ge locals temps memory (memory_affine_access_lvalue shape array expression) value ->
  exists block, rect_array_binding shape ge locals array block /\
    Mem.load Mint32 memory block (4*memory_index_value term i j) = Some value.
Proof.
  intros VALID DISTINCT ENCODE ROW COLUMN BOUND RUN.
  eapply indexed_array_load_inverse; [exact VALID|apply memory_source_affine_type|
    apply memory_source_affine_pure|eapply memory_index_expression_evaluation; eassumption|exact BOUND|exact RUN].
Qed.
Print Assumptions memory_index_expression_evaluation.
Print Assumptions memory_affine_access_load_inverse.
