From Stdlib Require Import ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightRectangularStore ClightTempFrame.
From GuardInterface Require Import ClightQuietDeterminacy.
Set Implicit Arguments.

Definition runtime_stride_index row column stride :=
  Ebinop Oadd (Ebinop Omul (Etempvar row type_int32s) (Etempvar stride type_int32s) type_int32s)
    (Etempvar column type_int32s) type_int32s.
Definition runtime_stride_lvalue d array row column stride :=
  Ederef (Ebinop Oadd (Evar array (rect_array_type d)) (runtime_stride_index row column stride)
    (Tpointer type_int32s noattr)) type_int32s.
Definition runtime_stride_store d array row column stride :=
  Sassign (runtime_stride_lvalue d array row column stride) (rect_value d row column).

Theorem runtime_stride_index_constant ge locals le memory d row column stride value :
  le ! stride = Some (Vint (Int.repr (rectangle_stride d))) ->
  (eval_expr ge locals le memory (runtime_stride_index row column stride) value <->
   eval_expr ge locals le memory (rect_index d row column) value).
Proof.
  intro STRIDE; split; intro RUN.
  - unfold runtime_stride_index in RUN; apply scalar_binary_inv in RUN.
    destruct RUN as [product [col [MUL [COL ADD]]]].
    apply scalar_binary_inv in MUL; destruct MUL as [row_value [step [ROW [STEP OP]]]].
    apply scalar_temp_inv in STEP; assert (SAME : step = Vint (Int.repr (rectangle_stride d))) by congruence; subst step.
    unfold rect_index; eapply eval_Ebinop.
    + eapply eval_Ebinop; [exact ROW|apply rect_constant_evaluation|].
      rewrite rect_constant_type; exact OP.
    + exact COL.
    + exact ADD.
  - unfold rect_index in RUN; apply scalar_binary_inv in RUN.
    destruct RUN as [product [col [MUL [COL ADD]]]].
    apply scalar_binary_inv in MUL; destruct MUL as [row_value [step [ROW [STEP OP]]]].
    pose proof (proj1 (expressions_determinate ge locals le memory) _ _ STEP _
      (@rect_constant_evaluation ge locals le memory (rectangle_stride d))) as SAME; subst step.
    unfold runtime_stride_index; eapply eval_Ebinop.
    + eapply eval_Ebinop; [exact ROW|constructor; exact STRIDE|].
      rewrite rect_constant_type in OP; exact OP.
    + exact COL.
    + exact ADD.
Qed.

Theorem runtime_stride_lvalue_constant ge locals le memory d array row column stride block offset field :
  le ! stride = Some (Vint (Int.repr (rectangle_stride d))) ->
  (eval_lvalue ge locals le memory (runtime_stride_lvalue d array row column stride) block offset field <->
   eval_lvalue ge locals le memory (rect_lvalue d array row column) block offset field).
Proof.
  intro STRIDE; split; intro RUN; inversion RUN; subst.
  all: match goal with POINTER : eval_expr _ _ _ _ (Ebinop Oadd _ _ _) _ |- _ =>
    apply scalar_binary_inv in POINTER; destruct POINTER as [base [index [BASE [INDEX ADD]]]] end.
  - apply eval_Ederef; eapply eval_Ebinop; [exact BASE| |exact ADD].
    apply (proj1 (@runtime_stride_index_constant ge locals le memory d row column stride index STRIDE)); exact INDEX.
  - apply eval_Ederef; eapply eval_Ebinop; [exact BASE| |exact ADD].
    apply (proj2 (@runtime_stride_index_constant ge locals le memory d row column stride index STRIDE)); exact INDEX.
Qed.

Theorem runtime_stride_store_constant fe ge locals le memory d array row column stride trace after final outcome :
  le ! stride = Some (Vint (Int.repr (rectangle_stride d))) ->
  (exec_stmt fe ge locals le memory (runtime_stride_store d array row column stride) trace after final outcome <->
   exec_stmt fe ge locals le memory (rect_store d array row column) trace after final outcome).
Proof.
  intro STRIDE; split; intro RUN; inversion RUN; subst; eapply exec_Sassign; try eassumption.
  - apply (proj1 (@runtime_stride_lvalue_constant ge locals _ memory d array row column stride _ _ _ STRIDE)); eassumption.
  - apply (proj2 (@runtime_stride_lvalue_constant ge locals _ memory d array row column stride _ _ _ STRIDE)); eassumption.
Qed.
Print Assumptions runtime_stride_index_constant.
Print Assumptions runtime_stride_lvalue_constant.
Print Assumptions runtime_stride_store_constant.

Theorem runtime_stride_lvalue_domain ge locals le memory d array row column stride block offset field :
  eval_lvalue ge locals le memory (runtime_stride_lvalue d array row column stride) block offset field ->
  exists word, le ! stride = Some (Vint word).
Proof.
  intro RUN; inversion RUN; subst.
  match goal with POINTER : eval_expr _ _ _ _ (Ebinop Oadd _ _ _) _ |- _ =>
    apply scalar_binary_inv in POINTER; destruct POINTER as [base [index [BASE [INDEX ADD]]]] end.
  apply scalar_binary_inv in INDEX; destruct INDEX as [product [col [MUL [COL ADD_INDEX]]]].
  apply scalar_binary_inv in MUL; destruct MUL as [row_value [step [ROW [STEP OP]]]].
  apply scalar_temp_inv in STEP.
  destruct row_value; destruct step; try discriminate OP; eexists; exact STEP.
Qed.
Print Assumptions runtime_stride_lvalue_domain.
