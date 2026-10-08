From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightPureExpr ClightTempFrame ClightSyntaxEquality.
From GuardInterface Require Import ClightQuietDeterminacy ClightAffineJointObservation.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** This capability preserves defined Mint32 observations. It does not assert
    equality of memories, bytes, pointer fragments, other chunks or traces. *)
Definition mint32_words_preserved before after := forall block offset word,
  Mem.load Mint32 before block offset=Some(Vint word) ->
  Mem.load Mint32 after block offset=Some(Vint word).

Lemma mint32_words_preserved_refl memory : mint32_words_preserved memory memory.
Proof. intros block offset word LOAD; exact LOAD. Qed.
Lemma mint32_words_preserved_trans before middle after :
  mint32_words_preserved before middle -> mint32_words_preserved middle after ->
  mint32_words_preserved before after.
Proof. intros FIRST SECOND block offset word LOAD; apply SECOND,FIRST; exact LOAD. Qed.

(** The stored value need only agree with the loaded value when that value is
    a defined word. Thus the law does not smuggle in data-load definedness. *)
Lemma mint32_loaded_store_preserves_words before after block offset loaded stored :
  Mem.load Mint32 before block offset=Some loaded ->
  (forall word,loaded=Vint word -> stored=Vint word) ->
  Mem.store Mint32 before block offset stored=Some after ->
  mint32_words_preserved before after.
Proof.
  intros LOAD SAME STORE observed_block observed_offset word OBSERVED.
  destruct(peq observed_block block)as [BLOCK|OTHER_BLOCK].
  - subst observed_block; destruct(Z.eq_dec observed_offset offset)as [OFFSET|OTHER_OFFSET].
    + subst observed_offset; assert(loaded=Vint word)by congruence.
      rewrite(SAME word H)in STORE.
      change(Some(Vint word))with(Some(Val.load_result Mint32(Vint word))).
      eapply Mem.load_store_same; exact STORE.
    + pose proof(Mem.load_valid_access _ _ _ _ _ OBSERVED)as LOAD_ACCESS.
      pose proof(Mem.store_valid_access_3 _ _ _ _ _ _ STORE)as STORE_ACCESS.
      destruct LOAD_ACCESS as [_ [read_multiple READ_ALIGN]];
        destruct STORE_ACCESS as [_ [write_multiple WRITE_ALIGN]].
      cbn [align_chunk]in READ_ALIGN,WRITE_ALIGN.
      erewrite Mem.load_store_other; [exact OBSERVED|exact STORE|cbn [size_chunk]; right; lia].
  - erewrite Mem.load_store_other; [exact OBSERVED|exact STORE|left; exact OTHER_BLOCK].
Qed.

Definition zero_rmw_rhs alpha lhs :=
  Ebinop Oadd lhs(Etempvar alpha type_int32s)type_int32s.

Lemma zero_rmw_assignment_preserves_words alpha address
  fe ge locals before memory trace after final outcome :
  before!alpha=Some(Vint Int.zero) ->
  exec_stmt fe ge locals before memory
    (Sassign(Ederef address type_int32s)(zero_rmw_rhs alpha(Ederef address type_int32s)))
    trace after final outcome ->
  mint32_words_preserved memory final /\ after=before.
Proof.
  intros ZERO RUN; inversion RUN; subst.
  match goal with VALUE:eval_expr _ _ _ _ (zero_rmw_rhs _ _) _ |- _ =>
    unfold zero_rmw_rhs in VALUE; apply scalar_binary_inv in VALUE as
      [loaded [delta [READ [DELTA OP]]]] end.
  apply scalar_temp_inv in DELTA; rewrite ZERO in DELTA; inversion DELTA; subst delta.
  inversion READ; subst; eliminate_impossible_lvalue.
  cbn [typeof]in *.
  match goal with LEFT:eval_lvalue ?g ?l ?t ?m (Ederef address type_int32s) _ _ _,
    RIGHT:eval_lvalue ?g ?l ?t ?m (Ederef address type_int32s) _ _ _ |- _ =>
    pose proof((proj2(expressions_determinate g l t m)) _ _ _ _ LEFT _ _ _ RIGHT)
      as [BLOCK [OFFSET FIELD]]; subst end.
  match goal with LEFT:eval_lvalue _ _ _ _ (Ederef address type_int32s) _ _ _ |- _ =>
    inversion LEFT; subst end.
  match goal with LOAD:deref_loc type_int32s _ _ _ _ _ |- _ =>
    inversion LOAD; subst; cbn [access_mode type_int32s]in *; try discriminate end.
  match goal with MODE:By_value Mint32=By_value _ |- _ => inversion MODE; subst end.
  match goal with STORE:assign_loc _ type_int32s _ _ _ _ _ _ |- _ =>
    inversion STORE; subst; cbn [access_mode type_int32s]in *; try discriminate end.
  match goal with MODE:By_value Mint32=By_value _ |- _ => inversion MODE; subst end.
  split; [|reflexivity].
  match goal with READ:Mem.loadv Mint32 _ (Vptr _ _) = Some _,
    STORE:Mem.storev Mint32 _ (Vptr _ _) _ = Some _ |- _ =>
    cbn [Mem.loadv]in READ; cbn [Mem.storev]in STORE;
    destruct(zle _ _)eqn:RANGE; [|discriminate];
    eapply mint32_loaded_store_preserves_words; [exact READ| |exact STORE] end.
  intros word SAME; subst loaded.
  change(Some(Vint(Int.add word Int.zero))=Some v2)in OP.
  rewrite Int.add_zero in OP; inversion OP; subst.
  match goal with CAST:sem_cast _ _ _ _=Some _ |- _ =>
    cbn [typeof zero_rmw_rhs sem_cast classify_cast cast_int_int type_int32s]in CAST;
    inversion CAST; reflexivity end.
Qed.

(** Source-only syntax certificate: arbitrary finite structured control,
    signed32 redundant RMWs, and assignments that cannot change alpha. *)
Fixpoint check_zero_rmw_control alpha(code:statement):bool := match code with
| Sskip | Sbreak | Scontinue => true
| Sset identifier _ => negb(Pos.eqb identifier alpha)
| Sassign (Ederef address ty) rhs =>
    if type_eq ty type_int32s then
      if expression_eq rhs(zero_rmw_rhs alpha(Ederef address type_int32s))then true else false
    else false
| Ssequence first second | Sloop first second =>
    check_zero_rmw_control alpha first && check_zero_rmw_control alpha second
| Sifthenelse _ yes no => check_zero_rmw_control alpha yes && check_zero_rmw_control alpha no
| _ => false end.

Theorem checked_zero_rmw_control_execution alpha
  fe ge locals before memory code trace after final outcome :
  exec_stmt fe ge locals before memory code trace after final outcome ->
  check_zero_rmw_control alpha code=true -> before!alpha=Some(Vint Int.zero) ->
  mint32_words_preserved memory final /\ after!alpha=Some(Vint Int.zero).
Proof.
  intro RUN; induction RUN; cbn [check_zero_rmw_control]; intros CHECK ZERO;
    try discriminate; try solve[split; [apply mint32_words_preserved_refl|exact ZERO]].
  - destruct a1; try discriminate CHECK.
    destruct(type_eq t type_int32s); [subst t|discriminate CHECK].
    destruct(expression_eq a2(zero_rmw_rhs alpha(Ederef a1 type_int32s)));
      [subst a2|discriminate CHECK].
    destruct(@zero_rmw_assignment_preserves_words alpha a1 fe ge e le m E0 le m' Out_normal
      ZERO ltac:(econstructor; eassumption))as [WORDS EXIT].
    split; [exact WORDS|exact ZERO].
  - apply negb_true_iff in CHECK; apply Pos.eqb_neq in CHECK.
    split; [apply mint32_words_preserved_refl|rewrite PTree.gso by congruence; exact ZERO].
  - apply andb_true_iff in CHECK as [FIRST SECOND].
    destruct(IHRUN1 FIRST ZERO)as [HEAD MID].
    destruct(IHRUN2 SECOND MID)as [TAIL EXIT].
    split; [eapply mint32_words_preserved_trans; eassumption|exact EXIT].
  - apply andb_true_iff in CHECK as [FIRST SECOND]; apply IHRUN; assumption.
  - apply andb_true_iff in CHECK as [YES NO]; destruct b; cbn in *; apply IHRUN; assumption.
  - apply andb_true_iff in CHECK as [FIRST SECOND]; apply IHRUN; assumption.
  - apply andb_true_iff in CHECK as [FIRST SECOND].
    destruct(IHRUN1 FIRST ZERO)as [HEAD MID].
    destruct(IHRUN2 SECOND MID)as [TAIL EXIT].
    split; [eapply mint32_words_preserved_trans; eassumption|exact EXIT].
  - apply andb_true_iff in CHECK as [FIRST SECOND].
    destruct(IHRUN1 FIRST ZERO)as [HEAD MID].
    destruct(IHRUN2 SECOND MID)as [STEP MID2].
    destruct(IHRUN3 ltac:(cbn [check_zero_rmw_control]; rewrite FIRST,SECOND; reflexivity)MID2)
      as [TAIL EXIT].
    split; [eapply mint32_words_preserved_trans; [exact HEAD|eapply mint32_words_preserved_trans; eassumption]|exact EXIT].
Qed.

Theorem checked_zero_rmw_control_preserves_header alpha
  fe ge locals before memory code trace after final outcome block offset word :
  check_zero_rmw_control alpha code=true -> before!alpha=Some(Vint Int.zero) ->
  Mem.load Mint32 memory block offset=Some(Vint word) ->
  exec_stmt fe ge locals before memory code trace after final outcome ->
  Mem.load Mint32 final block offset=Some(Vint word).
Proof.
  intros CHECK ZERO LOAD RUN.
  apply(proj1(@checked_zero_rmw_control_execution alpha fe ge locals before memory code trace after final outcome
    RUN CHECK ZERO)); exact LOAD.
Qed.

Print Assumptions mint32_words_preserved_refl.
Print Assumptions mint32_words_preserved_trans.
Print Assumptions mint32_loaded_store_preserves_words.
Print Assumptions zero_rmw_assignment_preserves_words.
Print Assumptions checked_zero_rmw_control_execution.
Print Assumptions checked_zero_rmw_control_preserves_header.
