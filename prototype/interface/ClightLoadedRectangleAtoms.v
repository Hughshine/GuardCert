From Stdlib Require Import Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Globalenvs.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightCondition ClightNoWrap ClightPureExpr ClightSameAddress
  ClightCountedLoop ClightRectangularStore ClightRectangularGuard.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightStableLoadBody ClightReadonlyCellSwap
  ClightLoadedRectangleMemory.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition loaded_rectangle_word bound entry :=
  match (entry_temps entry) ! bound with
  | Some (Vptr block offset) =>
    match Mem.loadv Mint32 (entry_memory entry) (Vptr block offset) with
    | Some (Vint word) => word | _ => Int.zero end
  | _ => Int.zero end.
Definition loaded_rectangle_block array entry :=
  match (entry_env entry) ! array with Some (block, _) => Some block
  | None => Genv.find_symbol (entry_ge entry) array end.
Definition loaded_rectangle_alias_expr d array bound i j :=
  Ebinop Oeq (Ebinop Oadd (Evar array (rect_array_type d))
    (rect_constant (i*rectangle_stride d+j)) (Tpointer type_int32s noattr))
    (signed_pointer_temp bound) type_int32s.
Definition loaded_rectangle_alias_flag d array bound i j entry :=
  match loaded_rectangle_block array entry, (entry_temps entry) ! bound with
  | Some block, Some (Vptr q qofs) => address_flag block (loaded_rectangle_offset d i j) q qofs
  | _, _ => false end.
Definition loaded_rectangle_active_expr bound i :=
  Ebinop Olt (rect_constant i) (signed_load bound) type_int32s.
Definition loaded_rectangle_active_flag bound i entry := (i <? Int.signed (loaded_rectangle_word bound entry)).
Definition loaded_rectangle_limit_expr bound limit :=
  Ebinop Ole (signed_load bound) (rect_constant limit) type_int32s.
Definition loaded_rectangle_limit_flag bound limit entry := (Int.signed (loaded_rectangle_word bound entry) <=? limit).

Lemma loaded_rectangle_block_known d array entry block :
  rect_array_binding d (entry_ge entry) (entry_env entry) array block -> loaded_rectangle_block array entry = Some block.
Proof. intros [LOCAL|[ABSENT GLOBAL]]; unfold loaded_rectangle_block; [rewrite LOCAL|rewrite ABSENT]; auto. Qed.

Lemma loaded_rectangle_alias_test d (VALID : rectangle_layout_valid d) array bound i j entry block q qofs word :
  0 <= i*rectangle_stride d+j < rectangle_extent d ->
  rect_array_binding d (entry_ge entry) (entry_env entry) array block ->
  (entry_temps entry) ! bound = Some (Vptr q qofs) ->
  Mem.loadv Mint32 (entry_memory entry) (Vptr q qofs) = Some word ->
  writable_word (entry_memory entry) block (loaded_rectangle_offset d i j) ->
  expression_test (loaded_rectangle_alias_expr d array bound i j) entry (loaded_rectangle_alias_flag d array bound i j entry).
Proof.
  intros RANGE ARRAY BOUND READ WORD; exists (Val.of_bool (address_flag block (loaded_rectangle_offset d i j) q qofs)); split.
  - eapply eval_Ebinop with (v1 := Vptr block (loaded_rectangle_offset d i j)) (v2 := Vptr q qofs).
    + eapply eval_Ebinop with (v1 := Vptr block Ptrofs.zero) (v2 := Vint (Int.repr (i*rectangle_stride d+j)));
        [apply rect_reference_evaluation; exact ARRAY|apply rect_constant_evaluation|].
      rewrite rect_constant_type; exact (@rect_pointer_add d VALID (entry_ge entry) (entry_memory entry) block _ RANGE).
    + constructor; exact BOUND.
    + change (cmp_ptr (entry_memory entry) Ceq (Vptr block (loaded_rectangle_offset d i j)) (Vptr q qofs) =
        Some (Val.of_bool (address_flag block (loaded_rectangle_offset d i j) q qofs))).
      apply pointer_equality_value; [apply writable_word_valid_pointer; exact WORD|eapply loaded_address_valid; exact READ].
  - unfold loaded_rectangle_alias_flag; rewrite (@loaded_rectangle_block_known d array entry block ARRAY), BOUND;
      apply bool_of_bool.
Qed.

Lemma loaded_rectangle_limit_test bound limit entry q qofs upper : signed_range limit ->
  (entry_temps entry) ! bound = Some (Vptr q qofs) ->
  Mem.loadv Mint32 (entry_memory entry) (Vptr q qofs) = Some (Vint upper) ->
  expression_test (loaded_rectangle_limit_expr bound limit) entry (loaded_rectangle_limit_flag bound limit entry).
Proof.
  intros RANGE BOUND READ; unfold loaded_rectangle_limit_flag, loaded_rectangle_word; rewrite BOUND, READ.
  exists (Val.of_bool (Int.signed upper <=? limit)); split; [|apply bool_of_bool].
  eapply eval_Ebinop with (v1 := Vint upper) (v2 := Vint (Int.repr limit)).
  - apply eval_Elvalue with (loc := q) (ofs := qofs) (bf := Full).
    + apply eval_Ederef, eval_Etempvar; exact BOUND.
    + apply deref_loc_value with (chunk := Mint32); [reflexivity|exact READ].
  - apply rect_constant_evaluation.
  - rewrite rect_constant_type; change (Some (Val.of_bool (negb (Int.lt (Int.repr limit) upper))) =
      Some (Val.of_bool (Int.signed upper <=? limit))).
    unfold Int.lt; rewrite Int.signed_repr by exact RANGE.
    destruct (zlt limit (Int.signed upper)) as [LT|GE].
    + assert (FLAG : (Int.signed upper <=? limit) = false) by (apply Z.leb_gt; lia); rewrite FLAG; reflexivity.
    + assert (FLAG : (Int.signed upper <=? limit) = true) by (apply Z.leb_le; lia); rewrite FLAG; reflexivity.
Qed.
Lemma loaded_rectangle_alias_apart d array bound i j entry block q qofs :
  rect_array_binding d (entry_ge entry) (entry_env entry) array block ->
  (entry_temps entry) ! bound = Some (Vptr q qofs) -> loaded_rectangle_alias_flag d array bound i j entry = false ->
  Vptr block (loaded_rectangle_offset d i j) <> Vptr q qofs.
Proof.
  intros ARRAY BOUND APART SAME; inversion SAME; subst.
  unfold loaded_rectangle_alias_flag, address_flag in APART;
    rewrite (@loaded_rectangle_block_known d array entry _ ARRAY), BOUND, Pos.eqb_refl, Ptrofs.eq_true in APART; discriminate.
Qed.

Lemma loaded_rectangle_active_test bound i entry q qofs upper : signed_range i ->
  (entry_temps entry) ! bound = Some (Vptr q qofs) ->
  Mem.loadv Mint32 (entry_memory entry) (Vptr q qofs) = Some (Vint upper) ->
  expression_test (loaded_rectangle_active_expr bound i) entry (loaded_rectangle_active_flag bound i entry).
Proof.
  intros RANGE BOUND READ; unfold loaded_rectangle_active_flag, loaded_rectangle_word; rewrite BOUND, READ.
  exists (Val.of_bool (i <? Int.signed upper)); split.
  - eapply eval_Ebinop with (v1 := Vint (Int.repr i)) (v2 := Vint upper).
    + apply rect_constant_evaluation.
    + apply eval_Elvalue with (loc := q) (ofs := qofs) (bf := Full).
      * apply eval_Ederef, eval_Etempvar; exact BOUND.
      * apply deref_loc_value with (chunk := Mint32); [reflexivity|exact READ].
    + rewrite rect_constant_type; change (Some (Val.of_bool (Int.lt (Int.repr i) upper)) =
        Some (Val.of_bool (i <? Int.signed upper))).
      unfold Int.lt; rewrite Int.signed_repr by exact RANGE.
      destruct (zlt i (Int.signed upper)) as [LT|GE].
      * assert (FLAG : (i <? Int.signed upper) = true) by (apply Z.ltb_lt; exact LT); rewrite FLAG; reflexivity.
      * assert (FLAG : (i <? Int.signed upper) = false) by (apply Z.ltb_ge; lia); rewrite FLAG; reflexivity.
  - apply bool_of_bool.
Qed.

Print Assumptions loaded_rectangle_alias_test.
Print Assumptions loaded_rectangle_alias_apart.
Print Assumptions loaded_rectangle_active_test.
Print Assumptions loaded_rectangle_limit_test.
