From Stdlib Require Import Bool List.
From compcert.lib Require Import Maps.
From compcert.common Require Import Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightCondition.
Set Implicit Arguments.

(** These expressions read temporaries and fixed type metadata, without loads.
    Their evaluation can fail, but every successful evaluation is unique. *)
Inductive pure_scalar : expr -> Prop :=
| pure_int : forall n ty, pure_scalar (Econst_int n ty)
| pure_temp : forall id ty, pure_scalar (Etempvar id ty)
| pure_unary : forall op a ty, pure_scalar a -> pure_scalar (Eunop op a ty)
| pure_binary : forall op a b ty, pure_scalar a -> pure_scalar b ->
    pure_scalar (Ebinop op a b ty)
| pure_cast : forall a ty, pure_scalar a -> pure_scalar (Ecast a ty)
| pure_sizeof : forall a ty, pure_scalar (Esizeof a ty)
| pure_alignof : forall a ty, pure_scalar (Ealignof a ty).

Lemma scalar_const_inv ge e le m n ty v :
  eval_expr ge e le m (Econst_int n ty) v -> v = Vint n.
Proof.
  intro RUN; inversion RUN; subst; auto.
  match goal with H : eval_lvalue _ _ _ _ (Econst_int _ _) _ _ _ |- _ => inversion H end.
Qed.

Lemma scalar_temp_inv ge e le m id ty v :
  eval_expr ge e le m (Etempvar id ty) v -> le ! id = Some v.
Proof.
  intro RUN; inversion RUN; subst; auto.
  match goal with H : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inversion H end.
Qed.

Lemma scalar_binary_inv ge e le m op a b ty v :
  eval_expr ge e le m (Ebinop op a b ty) v ->
  exists va vb, eval_expr ge e le m a va /\ eval_expr ge e le m b vb /\
    sem_binary_operation ge op va (typeof a) vb (typeof b) m = Some v.
Proof.
  intro RUN; inversion RUN; subst; eauto.
  match goal with H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H end.
Qed.

Lemma pure_scalar_determinate a : pure_scalar a -> forall ge e le m v v',
  eval_expr ge e le m a v -> eval_expr ge e le m a v' -> v = v'.
Proof.
  intro PURE; induction PURE; intros ge e le m v v' RUN RUN'.
  - apply scalar_const_inv in RUN, RUN'; congruence.
  - apply scalar_temp_inv in RUN, RUN'; congruence.
  - inversion RUN; subst; try match goal with
      H : eval_lvalue _ _ _ _ (Eunop _ _ _) _ _ _ |- _ => inversion H end.
    inversion RUN'; subst; try match goal with
      H : eval_lvalue _ _ _ _ (Eunop _ _ _) _ _ _ |- _ => inversion H end.
    match goal with
      A : eval_expr _ _ _ _ a ?x, B : eval_expr _ _ _ _ a ?y |- _ =>
      pose proof (IHPURE _ _ _ _ _ _ A B); subst y end.
    congruence.
  - apply scalar_binary_inv in RUN, RUN'.
    destruct RUN as [va [vb [A [B OP]]]], RUN' as [va' [vb' [A' [B' OP']]]].
    pose proof (IHPURE1 _ _ _ _ _ _ A A'); subst va'.
    pose proof (IHPURE2 _ _ _ _ _ _ B B'); subst vb'. congruence.
  - inversion RUN; subst; try match goal with
      H : eval_lvalue _ _ _ _ (Ecast _ _) _ _ _ |- _ => inversion H end.
    inversion RUN'; subst; try match goal with
      H : eval_lvalue _ _ _ _ (Ecast _ _) _ _ _ |- _ => inversion H end.
    match goal with
      A : eval_expr _ _ _ _ a ?x, B : eval_expr _ _ _ _ a ?y |- _ =>
      pose proof (IHPURE _ _ _ _ _ _ A B); subst y end.
    congruence.
  - inversion RUN; subst; try match goal with
      H : eval_lvalue _ _ _ _ (Esizeof _ _) _ _ _ |- _ => inversion H end.
    inversion RUN'; subst; try match goal with
      H : eval_lvalue _ _ _ _ (Esizeof _ _) _ _ _ |- _ => inversion H end.
    reflexivity.
  - inversion RUN; subst; try match goal with
      H : eval_lvalue _ _ _ _ (Ealignof _ _) _ _ _ |- _ => inversion H end.
    inversion RUN'; subst; try match goal with
      H : eval_lvalue _ _ _ _ (Ealignof _ _) _ _ _ |- _ => inversion H end.
    reflexivity.
Qed.

Lemma pure_test_determinate a s b b' :
  pure_scalar a -> expression_test a s b -> expression_test a s b' -> b = b'.
Proof.
  intros PURE [v [EV BOOL]] [v' [EV' BOOL']].
  pose proof (pure_scalar_determinate PURE EV EV'); subst; congruence.
Qed.

Inductive pure_tree : decision_tree -> Prop :=
| pure_leaf : forall b, pure_tree (Decision b)
| pure_test : forall a yes no, pure_scalar a -> pure_tree yes -> pure_tree no ->
    pure_tree (Test a yes no).

Lemma pure_tree_determinate t : pure_tree t -> forall s b b',
  decision_run s t b -> decision_run s t b' -> b = b'.
Proof.
  intro PURE; induction PURE; intros s result result' RUN RUN'.
  - inversion RUN; inversion RUN'; subst; reflexivity.
  - inversion RUN; subst. inversion RUN'; subst.
    match goal with
      A : expression_test a s ?x, B : expression_test a s ?y |- _ =>
      pose proof (pure_test_determinate H A B); subst y end.
    match goal with CHECK : expression_test a s ?selected |- _ => destruct selected end; eauto.
Qed.

Fixpoint decision_bind (t yes no : decision_tree) : decision_tree :=
  match t with
  | Decision b => if b then yes else no
  | Test a l r => Test a (decision_bind l yes no) (decision_bind r yes no)
  end.

Lemma decision_bind_run s t b : decision_run s t b -> forall yes no result,
  decision_run s (if b then yes else no) result ->
  decision_run s (decision_bind t yes no) result.
Proof.
  intro RUN; induction RUN; intros yes0 no0 result0 LEAF; simpl; auto.
  econstructor; eauto. destruct b; simpl in *; eauto.
Qed.

Lemma pure_decision_bind t : pure_tree t -> forall yes no,
  pure_tree yes -> pure_tree no -> pure_tree (decision_bind t yes no).
Proof.
  intro PURE; induction PURE; intros yes0 no0 YES NO; simpl.
  - destruct b; auto.
  - constructor; auto.
Qed.

Print Assumptions pure_scalar_determinate.
Print Assumptions pure_tree_determinate.
