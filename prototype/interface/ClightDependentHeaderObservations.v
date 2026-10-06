From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightTempFrame ClightCountedLoop ClightNoWrap CompCertMemoryActions.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightDependentBoundSyntax ClightObservedHeaderPrefix.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition dependent_cached_header root pointer_cache cache entry :=
  exists block offset target address bound,
    (entry_temps entry) ! root = Some (Vptr block offset) /\
    (entry_temps entry) ! pointer_cache = Some (Vptr target address) /\
    (entry_temps entry) ! cache = Some (Vint bound) /\
    Mem.loadv Mptr (entry_memory entry) (Vptr block offset) = Some (Vptr target address) /\
    Mem.loadv Mint32 (entry_memory entry) (Vptr target address) = Some (Vint bound).

Definition dependent_header_observations root pointer_cache cache entry : list (memory_location * val) :=
  match (entry_temps entry) ! root, (entry_temps entry) ! pointer_cache, (entry_temps entry) ! cache with
  | Some (Vptr block offset),Some (Vptr target address),Some (Vint bound) =>
    [(MemoryLocation Mptr block (Ptrofs.unsigned offset),Vptr target address);
     (MemoryLocation Mint32 target (Ptrofs.unsigned address),Vint bound)]
  | _,_,_ => [] end.

Lemma dependent_header_initial_observations root pointer_cache cache entry :
  dependent_cached_header root pointer_cache cache entry ->
  header_observations_match (dependent_header_observations root pointer_cache cache entry) (entry_memory entry).
Proof.
  intros [block [offset [target [address [bound [ROOT [POINTER [CACHE [READ_POINTER READ_BOUND]]]]]]]]].
  unfold dependent_header_observations; rewrite ROOT,POINTER,CACHE.
  unfold header_observations_match; constructor; [|constructor; [|constructor]]; cbn [fst snd location_load].
  - cbn [Mem.loadv] in READ_POINTER; destruct (zle _ _); [exact READ_POINTER|discriminate].
  - cbn [Mem.loadv] in READ_BOUND; destruct (zle _ _); [exact READ_BOUND|discriminate].
Qed.

(** This fills the concrete HEADER obligation of the multi-observation prefix
    library. Only the root temp is needed in the actual source header; cached
    pointer/bound values belong to the immutable guard entry. *)
Theorem dependent_header_from_observations row root pointer_cache cache stable entry i current memory :
  In root stable -> dependent_cached_header root pointer_cache cache entry ->
  0 <= i <= Int.signed (temp_word cache (entry_temps entry)) ->
  current ! row = Some (Vint (Int.repr i)) -> temp_agree stable (entry_temps entry) current ->
  header_observations_match (dependent_header_observations root pointer_cache cache entry) memory ->
  expression_test (dependent_bound_test row root) (Entry (entry_ge entry) (entry_env entry) current memory)
    (i <? Int.signed (temp_word cache (entry_temps entry))).
Proof.
  intros MEMBER [block [offset [target [address [bound [ROOT [POINTER [CACHE [INITIAL_POINTER INITIAL_BOUND]]]]]]]]]
    RANGE ROW FRAME OBSERVED.
  unfold dependent_header_observations in OBSERVED; rewrite ROOT,POINTER,CACHE in OBSERVED.
  unfold header_observations_match in OBSERVED.
  inversion OBSERVED as [|first rest POINTER_VALUE REST]; subst.
  inversion REST as [|second tail BOUND_VALUE REST']; subst.
  cbn [fst snd location_load] in POINTER_VALUE,BOUND_VALUE.
  assert (READ_POINTER : Mem.loadv Mptr memory (Vptr block offset) = Some (Vptr target address)).
  { cbn [Mem.loadv] in INITIAL_POINTER |- *; destruct (zle _ _); [exact POINTER_VALUE|discriminate]. }
  assert (READ_BOUND : Mem.loadv Mint32 memory (Vptr target address) = Some (Vint bound)).
  { cbn [Mem.loadv] in INITIAL_BOUND |- *; destruct (zle _ _); [exact BOUND_VALUE|discriminate]. }
  unfold temp_word in RANGE |- *; rewrite CACHE in RANGE |- *.
  assert (SIGNED : signed_range i).
  { unfold signed_range; change (-2147483648 <= i <= 2147483647).
    pose proof (Int.signed_range bound) as BOUND_RANGE.
    change (-2147483648 <= Int.signed bound <= 2147483647) in BOUND_RANGE.
    change (0 <= i <= Int.signed bound) in RANGE; lia. }
  assert (FLAG : Int.lt (Int.repr i) bound = (i <? Int.signed bound)).
  { unfold Int.lt; rewrite Int.signed_repr by exact SIGNED.
    destruct (zlt i (Int.signed bound)); [symmetry; apply Z.ltb_lt|symmetry; apply Z.ltb_ge]; lia. }
  rewrite <- FLAG; eapply dependent_bound_test_eval; [exact ROW| |exact READ_POINTER|exact READ_BOUND].
  rewrite FRAME by exact MEMBER; exact ROOT.
Qed.

Definition dependent_header_capture root pointer_cache cache :=
  Ssequence (Sset pointer_cache (dependent_pointer_load root)) (Sset cache (signed_load pointer_cache)).

Theorem dependent_header_safe_capture fe ge locals temps memory row root pointer_cache cache flag :
  pointer_cache <> root -> cache <> root -> cache <> pointer_cache ->
  expression_test (dependent_bound_test row root) (Entry ge locals temps memory) flag ->
  exists after, exec_stmt fe ge locals temps memory (dependent_header_capture root pointer_cache cache)
    E0 after memory Out_normal /\ dependent_cached_header root pointer_cache cache (Entry ge locals after memory).
Proof.
  intros POINTER_ROOT CACHE_ROOT DISTINCT HEADER.
  destruct (dependent_bound_test_facts HEADER) as [counter [bound [block [offset [target [address
    [ROW [ROOT [POINTER [READ FLAG]]]]]]]]]].
  exists (PTree.set cache (Vint bound) (PTree.set pointer_cache (Vptr target address) temps)); split.
  - unfold dependent_header_capture; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
    + constructor; eapply eval_Elvalue with (loc:=block) (ofs:=offset) (bf:=Full).
      * apply eval_Ederef,eval_Etempvar; exact ROOT.
      * apply deref_loc_value with (chunk:=Mptr); [reflexivity|exact POINTER].
    + constructor; eapply eval_Elvalue with (loc:=target) (ofs:=address) (bf:=Full).
      * apply eval_Ederef,eval_Etempvar,PTree.gss.
      * apply deref_loc_value with (chunk:=Mint32); [reflexivity|exact READ].
  - exists block,offset,target,address,bound; cbn [entry_temps entry_memory].
    repeat rewrite PTree.gso by congruence; rewrite !PTree.gss.
    repeat split; assumption.
Qed.

Definition dependent_pointer_cell_address root := Ecast (signed_pointer_cell_temp root) signed_pointer_type.
Lemma dependent_pointer_cell_address_eval ge locals temps memory root block offset :
  temps ! root = Some (Vptr block offset) ->
  eval_expr ge locals temps memory (dependent_pointer_cell_address root) (Vptr block offset).
Proof.
  intro ROOT; eapply eval_Ecast with (v1:=Vptr block offset); [apply eval_Etempvar; exact ROOT|reflexivity].
Qed.

Print Assumptions dependent_header_initial_observations.
Print Assumptions dependent_header_from_observations.
Print Assumptions dependent_header_safe_capture.
Print Assumptions dependent_pointer_cell_address_eval.
