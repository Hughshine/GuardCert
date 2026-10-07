From Stdlib Require Import List ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightTempFrame CompCertMemoryActions.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightObservedHeaderPrefix.
Import ListNotations.
Set Implicit Arguments.

Definition signed_indexed_pointer pointer index :=
  Ebinop Oadd (signed_pointer_temp pointer) (Econst_int index type_int32s) (Tpointer type_int32s noattr).
Definition signed_indexed_load pointer index := Ederef (signed_indexed_pointer pointer index) type_int32s.
Definition signed_indexed_offset pointer index delta :=
  Ebinop Oadd (signed_indexed_load pointer index) (Econst_int delta type_int32s) type_int32s.
Definition signed_indexed_address offset index :=
  Ptrofs.add offset (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.repr (Int.signed index))).

Lemma signed_indexed_pointer_eval ge locals temps memory pointer index block offset :
  temps!pointer=Some(Vptr block offset) ->
  eval_expr ge locals temps memory (signed_indexed_pointer pointer index)
    (Vptr block (signed_indexed_address offset index)).
Proof. intro POINTER; eapply eval_Ebinop; [apply eval_Etempvar; exact POINTER|constructor|reflexivity]. Qed.
Lemma signed_indexed_load_eval ge locals temps memory pointer index block offset value :
  temps!pointer=Some(Vptr block offset) ->
  Mem.loadv Mint32 memory (Vptr block (signed_indexed_address offset index))=Some value ->
  eval_expr ge locals temps memory (signed_indexed_load pointer index) value.
Proof.
  intros POINTER READ; eapply eval_Elvalue with (loc:=block) (ofs:=signed_indexed_address offset index) (bf:=Full).
  - apply eval_Ederef,signed_indexed_pointer_eval; exact POINTER.
  - apply deref_loc_value with (chunk:=Mint32); [reflexivity|exact READ].
Qed.
Lemma signed_indexed_load_inv ge locals temps memory pointer index value :
  eval_expr ge locals temps memory (signed_indexed_load pointer index) value ->
  exists block offset, temps!pointer=Some(Vptr block offset) /\
    Mem.loadv Mint32 memory (Vptr block (signed_indexed_address offset index))=Some value.
Proof.
  intro EVAL; inversion EVAL; subst.
  match goal with LV : eval_lvalue _ _ _ _ (signed_indexed_load _ _) _ _ _ |- _ => inversion LV; subst end.
  match goal with ADDRESS : eval_expr _ _ _ _ (signed_indexed_pointer _ _) _ |- _ =>
    apply scalar_binary_inv in ADDRESS; destruct ADDRESS as [base [constant [POINTER [INDEX OP]]]] end.
  apply scalar_temp_inv in POINTER; apply scalar_const_inv in INDEX; subst constant.
  unfold Cop.sem_binary_operation in OP; cbn [typeof signed_pointer_temp] in OP.
  destruct base; try discriminate OP.
  change (Some(Vptr b (signed_indexed_address i index))=Some(Vptr loc ofs)) in OP.
  injection OP as BLOCK OFFSET; subst loc ofs.
  match goal with READ : deref_loc _ _ _ _ _ _ |- _ => inversion READ; subst; try discriminate end.
  match goal with MODE : access_mode _=By_value _ |- _ => inversion MODE; subst end.
  exists b,i; split; assumption.
Qed.
Lemma signed_indexed_offset_eval ge locals temps memory pointer index delta block offset raw :
  temps!pointer=Some(Vptr block offset) ->
  Mem.loadv Mint32 memory (Vptr block (signed_indexed_address offset index))=Some(Vint raw) ->
  eval_expr ge locals temps memory (signed_indexed_offset pointer index delta) (Vint(Int.add raw delta)).
Proof.
  intros POINTER READ; eapply eval_Ebinop; [eapply signed_indexed_load_eval; eassumption|constructor|reflexivity].
Qed.
Lemma signed_indexed_offset_inv ge locals temps memory pointer index delta upper :
  eval_expr ge locals temps memory (signed_indexed_offset pointer index delta) (Vint upper) ->
  exists block offset raw, temps!pointer=Some(Vptr block offset) /\
    Mem.loadv Mint32 memory (Vptr block (signed_indexed_address offset index))=Some(Vint raw) /\
    upper=Int.add raw delta.
Proof.
  intro EVAL; apply scalar_binary_inv in EVAL.
  destruct EVAL as [loaded [constant [LOAD [CONST OP]]]].
  apply scalar_const_inv in CONST; subst constant.
  unfold Cop.sem_binary_operation in OP; cbn [typeof signed_indexed_load] in OP.
  destruct loaded; try discriminate OP.
  change (Some(Vint(Int.add i delta))=Some(Vint upper)) in OP; injection OP as RESULT.
  destruct (signed_indexed_load_inv LOAD) as [block [offset [POINTER READ]]].
  exists block,offset,i; repeat split; try assumption; congruence.
Qed.

Definition indexed_offset_observations pointer index entry : list (memory_location * val) :=
  match (entry_temps entry)!pointer with
  | Some(Vptr block offset) =>
      let address:=signed_indexed_address offset index in
      match Mem.loadv Mint32 (entry_memory entry) (Vptr block address) with
      | Some value=>[(MemoryLocation Mint32 block (Ptrofs.unsigned address),value)]
      | None=>[] end
  | _=>[] end.
Definition indexed_offset_cached_header pointer index delta cache entry :=
  exists block offset raw, (entry_temps entry)!pointer=Some(Vptr block offset) /\
    Mem.loadv Mint32 (entry_memory entry) (Vptr block (signed_indexed_address offset index))=Some(Vint raw) /\
    (entry_temps entry)!cache=Some(Vint(Int.add raw delta)).

Lemma indexed_offset_observations_initial pointer index delta cache entry :
  indexed_offset_cached_header pointer index delta cache entry ->
  header_observations_match (indexed_offset_observations pointer index entry) (entry_memory entry).
Proof.
  intros [block [offset [raw [POINTER [READ CACHE]]]]].
  unfold indexed_offset_observations; rewrite POINTER,READ.
  unfold header_observations_match; constructor; [|constructor]; cbn [fst snd location_load].
  cbn [Mem.loadv] in READ; destruct (zle _ _); [exact READ|discriminate].
Qed.
Theorem indexed_offset_bound_from_observations pointer index delta cache stable entry current memory upper :
  In pointer stable -> indexed_offset_cached_header pointer index delta cache entry ->
  (entry_temps entry)!cache=Some(Vint upper) -> temp_agree stable (entry_temps entry) current ->
  header_observations_match (indexed_offset_observations pointer index entry) memory ->
  eval_expr (entry_ge entry) (entry_env entry) current memory (signed_indexed_offset pointer index delta) (Vint upper).
Proof.
  intros MEMBER [block [offset [raw [POINTER [INITIAL CACHE]]]]] WORD FRAME OBSERVED.
  assert (UPPER : upper=Int.add raw delta) by congruence; subst upper.
  unfold indexed_offset_observations in OBSERVED; rewrite POINTER,INITIAL in OBSERVED.
  inversion OBSERVED as [|first rest VALUE REST]; subst; cbn [fst snd location_load] in VALUE.
  assert (READ : Mem.loadv Mint32 memory (Vptr block (signed_indexed_address offset index))=Some(Vint raw)).
  { cbn [Mem.loadv] in INITIAL |- *; destruct (zle _ _); [exact VALUE|discriminate]. }
  eapply signed_indexed_offset_eval; [rewrite FRAME by exact MEMBER; exact POINTER|exact READ].
Qed.

Print Assumptions signed_indexed_pointer_eval.
Print Assumptions signed_indexed_load_eval.
Print Assumptions signed_indexed_load_inv.
Print Assumptions signed_indexed_offset_eval.
Print Assumptions signed_indexed_offset_inv.
Print Assumptions indexed_offset_observations_initial.
Print Assumptions indexed_offset_bound_from_observations.
