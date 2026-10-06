From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightNoWrap ClightCountedLoop.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightStrictLoopProgress
  ClightStableLoopCondition.
Import ListNotations.
Set Implicit Arguments.

(** An ordinary signed bound reached through a pointer stored in memory.
    Its first observation has chunk Mptr, not the bound's Mint32 chunk. *)
Definition signed_pointer_type := Tpointer type_int32s noattr.
Definition signed_pointer_cell_temp root := Etempvar root (Tpointer signed_pointer_type noattr).
Definition dependent_pointer_load root := Ederef (signed_pointer_cell_temp root) signed_pointer_type.
Definition dependent_signed_load root := Ederef (dependent_pointer_load root) type_int32s.
Definition dependent_bound_test row root :=
  Ebinop Olt (Etempvar row type_int32s) (dependent_signed_load root) type_int32s.
Definition dependent_bound_loop row root body := strict_frontend_loop row (dependent_bound_test row root) body.

Lemma dependent_pointer_load_inv ge locals temps memory root value :
  eval_expr ge locals temps memory (dependent_pointer_load root) value ->
  exists block offset, temps ! root = Some (Vptr block offset) /\
    Mem.loadv Mptr memory (Vptr block offset) = Some value.
Proof.
  intro RUN; inversion RUN; subst.
  match goal with LV : eval_lvalue _ _ _ _ (dependent_pointer_load root) _ _ _ |- _ => inversion LV; subst end.
  match goal with TEMP : eval_expr _ _ _ _ (signed_pointer_cell_temp root) _ |- _ =>
    apply scalar_temp_inv in TEMP end.
  match goal with LOAD : deref_loc _ _ _ _ _ _ |- _ => inversion LOAD; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ =>
    change (By_value Mptr = By_value chunk) in MODE; inversion MODE; subst end.
  do 2 eexists; split; eassumption.
Qed.

Lemma dependent_signed_load_inv ge locals temps memory root value :
  eval_expr ge locals temps memory (dependent_signed_load root) value ->
  exists block offset target address, temps ! root = Some (Vptr block offset) /\
    Mem.loadv Mptr memory (Vptr block offset) = Some (Vptr target address) /\
    Mem.loadv Mint32 memory (Vptr target address) = Some value.
Proof.
  intro RUN; inversion RUN; subst.
  match goal with LV : eval_lvalue _ _ _ _ (dependent_signed_load root) _ _ _ |- _ => inversion LV; subst end.
  match goal with PTR : eval_expr _ _ _ _ (dependent_pointer_load root) _ |- _ =>
    apply dependent_pointer_load_inv in PTR; destruct PTR as [block [offset [ROOT READ]]] end.
  match goal with LOAD : deref_loc _ _ _ _ _ _ |- _ => inversion LOAD; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  do 4 eexists; split; [exact ROOT|split; eassumption].
Qed.

Lemma dependent_bound_test_facts ge locals temps memory row root flag :
  expression_test (dependent_bound_test row root) (Entry ge locals temps memory) flag ->
  exists counter bound block offset target address,
    temps ! row = Some (Vint counter) /\ temps ! root = Some (Vptr block offset) /\
    Mem.loadv Mptr memory (Vptr block offset) = Some (Vptr target address) /\
    Mem.loadv Mint32 memory (Vptr target address) = Some (Vint bound) /\ flag = Int.lt counter bound.
Proof.
  intros [value [EVAL BOOL]]; apply scalar_binary_inv in EVAL.
  destruct EVAL as [counter [bound [ROW [BOUND OP]]]]; apply scalar_temp_inv in ROW.
  apply dependent_signed_load_inv in BOUND; destruct BOUND as [block [offset [target [address [ROOT [PTR READ]]]]]].
  destruct counter; destruct bound; try discriminate OP.
  change (Some (Val.of_bool (Int.lt i i0)) = Some value) in OP; injection OP as VALUE; subst value.
  rewrite bool_of_bool in BOOL; exists i,i0,block,offset,target,address; repeat split; try assumption; congruence.
Qed.

Lemma dependent_bound_test_eval ge locals temps memory row root counter bound block offset target address :
  temps ! row = Some (Vint counter) -> temps ! root = Some (Vptr block offset) ->
  Mem.loadv Mptr memory (Vptr block offset) = Some (Vptr target address) ->
  Mem.loadv Mint32 memory (Vptr target address) = Some (Vint bound) ->
  expression_test (dependent_bound_test row root) (Entry ge locals temps memory) (Int.lt counter bound).
Proof.
  intros ROW ROOT POINTER READ; exists (Val.of_bool (Int.lt counter bound)); split; [|apply bool_of_bool].
  eapply eval_Ebinop with (v1:=Vint counter) (v2:=Vint bound); [apply eval_Etempvar; exact ROW| |reflexivity].
  eapply eval_Elvalue with (loc:=target) (ofs:=address) (bf:=Full).
  - apply eval_Ederef; eapply eval_Elvalue with (loc:=block) (ofs:=offset) (bf:=Full).
    + apply eval_Ederef,eval_Etempvar; exact ROOT.
    + apply deref_loc_value with (chunk:=Mptr); [reflexivity|exact POINTER].
  - apply deref_loc_value with (chunk:=Mint32); [reflexivity|exact READ].
Qed.

Lemma dependent_bound_test_strict ge locals temps memory row root :
  expression_test (dependent_bound_test row root) (Entry ge locals temps memory) true ->
  strict_counter_active row temps.
Proof.
  intro TEST; destruct (dependent_bound_test_facts TEST) as [counter [bound [block [offset [target [address
    [ROW [ROOT [POINTER [READ LT]]]]]]]]]].
  exists counter; split; [exact ROW|].
  unfold Int.lt in LT; destruct (zlt (Int.signed counter) (Int.signed bound));
    [pose proof (Int.signed_range bound); lia|discriminate].
Qed.

Lemma dependent_bound_completed_header fe ge locals temps memory row root body trace after final outcome :
  exec_stmt fe ge locals temps memory (dependent_bound_loop row root body) trace after final outcome ->
  exists flag, expression_test (dependent_bound_test row root) (Entry ge locals temps memory) flag.
Proof.
  unfold dependent_bound_loop,strict_frontend_loop; intro SOURCE; inversion SOURCE; subst.
  all: match goal with HEADER : exec_stmt _ _ _ _ _
    (Ssequence (Ssequence Sskip (Sifthenelse _ _ _)) _) _ _ _ _ |- _ =>
      destruct (strict_header_execution HEADER) as [flag [TEST _]]; exists flag; exact TEST end.
Qed.

Print Assumptions dependent_pointer_load_inv.
Print Assumptions dependent_signed_load_inv.
Print Assumptions dependent_bound_test_facts.
Print Assumptions dependent_bound_test_eval.
Print Assumptions dependent_bound_test_strict.
Print Assumptions dependent_bound_completed_header.
