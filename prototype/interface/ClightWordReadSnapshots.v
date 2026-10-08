From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes Cop ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightTempFrame ClightTempFootprint.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightWordArithmeticTransport ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.

(** A concrete language library for nonvolatile signed32 expression reads.
    Equalities below are machine-word equalities, not no-wrap claims. *)
Inductive snapshot_word_expression : expr -> Prop :=
| snapshot_word_constant : forall value,
    snapshot_word_expression (Econst_int value type_int32s)
| snapshot_word_temp : forall identifier,
    snapshot_word_expression (Etempvar identifier type_int32s)
| snapshot_word_read : forall pointer,
    snapshot_word_expression (signed_load pointer)
| snapshot_word_binary : forall op first second,
    op=Oadd \/ op=Osub \/ op=Omul ->
    snapshot_word_expression first -> snapshot_word_expression second ->
    snapshot_word_expression (Ebinop op first second type_int32s).

Fixpoint snapshot_word_reads code :=
  match code with
  | Ederef (Etempvar pointer _) _ => [pointer]
  | Ebinop _ first second _ => snapshot_word_reads first ++ snapshot_word_reads second
  | _ => [] end.

Fixpoint snapshot_word_replace (binding : ident -> option ident) code :=
  match code with
  | Ederef (Etempvar pointer _) ty =>
    match binding pointer with Some cache => Etempvar cache ty | None => code end
  | Ebinop op first second ty =>
    Ebinop op (snapshot_word_replace binding first) (snapshot_word_replace binding second) ty
  | _ => code end.

Lemma snapshot_word_type code : snapshot_word_expression code -> typeof code=type_int32s.
Proof. intro WORD; inversion WORD; reflexivity. Qed.

Lemma snapshot_word_replace_type binding code :
  snapshot_word_expression code -> typeof (snapshot_word_replace binding code)=typeof code.
Proof.
  intro WORD; induction WORD; cbn [snapshot_word_replace signed_load signed_pointer_temp];
    try reflexivity; destruct (binding pointer); reflexivity.
Qed.

(** The original expression's successful word result licenses every read leaf,
    including reads in a header whose resulting child domain is empty. *)
Theorem snapshot_word_reads_defined code : snapshot_word_expression code ->
  forall ge locals temps memory value,
  eval_expr ge locals temps memory code (Vint value) ->
  forall pointer, In pointer (snapshot_word_reads code) ->
  exists word, eval_expr ge locals temps memory (signed_load pointer) (Vint word).
Proof.
  intro WORD; induction WORD; intros ge locals temps memory result RUN observed_pointer MEMBER;
    cbn [snapshot_word_reads signed_load signed_pointer_temp] in MEMBER; try contradiction.
  - destruct MEMBER as [<-|[]]; exists result; exact RUN.
  - apply scalar_binary_inv in RUN as [left [right [FIRST [SECOND OP]]]].
    rewrite (snapshot_word_type WORD1),(snapshot_word_type WORD2) in OP.
    destruct (@memory_source_binary_words ge op left right memory result H OP)
      as [a [b [LEFT RIGHT]]]; subst left right.
    apply in_app_or in MEMBER as [MEMBER|MEMBER].
    + eapply IHWORD1; eassumption.
    + eapply IHWORD2; eassumption.
Qed.

Definition snapshot_word_receipts binding code ge locals temps memory :=
  forall pointer cache, In pointer (snapshot_word_reads code) -> binding pointer=Some cache ->
  exists word, temps!cache=Some (Vint word) /\
    eval_expr ge locals temps memory (signed_load pointer) (Vint word).

Theorem snapshot_word_replacement_evaluation code : snapshot_word_expression code ->
  forall binding ge locals temps memory value,
  snapshot_word_receipts binding code ge locals temps memory ->
  (eval_expr ge locals temps memory code value <->
   eval_expr ge locals temps memory (snapshot_word_replace binding code) value).
Proof.
  intro WORD; induction WORD; intros binding ge locals temps memory observed_value RECEIPTS;
    cbn [snapshot_word_replace signed_load signed_pointer_temp]; try tauto.
  - destruct (binding pointer) as [cache|] eqn:BIND; [|tauto].
    destruct (RECEIPTS pointer cache (or_introl eq_refl) BIND) as [word [CACHE READ]].
    split; intro RUN.
    + pose proof (proj1 (expressions_determinate ge locals temps memory) _ _ RUN _ READ) as SAME.
      subst observed_value; apply eval_Etempvar; exact CACHE.
    + apply scalar_temp_inv in RUN; assert (observed_value=Vint word) by congruence;
        subst observed_value; exact READ.
  - assert (FIRST_RECEIPTS : snapshot_word_receipts binding first ge locals temps memory).
    { intros pointer cache MEMBER BIND; apply RECEIPTS; [apply in_or_app; left; exact MEMBER|exact BIND]. }
    assert (SECOND_RECEIPTS : snapshot_word_receipts binding second ge locals temps memory).
    { intros pointer cache MEMBER BIND; apply RECEIPTS; [apply in_or_app; right; exact MEMBER|exact BIND]. }
    split; intro RUN; apply scalar_binary_inv in RUN as [left [right [FIRST [SECOND OP]]]];
      eapply eval_Ebinop.
    + apply (proj1 (IHWORD1 _ _ _ _ _ _ FIRST_RECEIPTS)); exact FIRST.
    + apply (proj1 (IHWORD2 _ _ _ _ _ _ SECOND_RECEIPTS)); exact SECOND.
    + rewrite !snapshot_word_replace_type by assumption; exact OP.
    + apply (proj2 (IHWORD1 _ _ _ _ _ _ FIRST_RECEIPTS)); exact FIRST.
    + apply (proj2 (IHWORD2 _ _ _ _ _ _ SECOND_RECEIPTS)); exact SECOND.
    + rewrite !snapshot_word_replace_type in OP by assumption; exact OP.
Qed.

(** Rewriting one setup expression preserves the actual subsequent execution,
    including every public temporary and memory effect of the unchanged tail. *)
Theorem snapshot_word_setup_execution fe ge locals temps memory result code tail binding trace after final outcome :
  snapshot_word_expression code -> snapshot_word_receipts binding code ge locals temps memory ->
  (exec_stmt fe ge locals temps memory (Ssequence (Sset result code) tail) trace after final outcome <->
   exec_stmt fe ge locals temps memory
     (Ssequence (Sset result (snapshot_word_replace binding code)) tail) trace after final outcome).
Proof.
  intros WORD RECEIPTS.
  assert (SAME : forall value, eval_expr ge locals temps memory code value <->
    eval_expr ge locals temps memory (snapshot_word_replace binding code) value).
  { intro value; apply snapshot_word_replacement_evaluation; assumption. }
  split; intro RUN; inversion RUN; subst.
  all: match goal with SET : exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ =>
    inversion SET; subst end.
  - eapply exec_Sseq_1; [constructor; apply (proj1 (SAME _)); eassumption|eassumption].
  - contradiction.
  - eapply exec_Sseq_1; [constructor; apply (proj2 (SAME _)); eassumption|eassumption].
  - contradiction.
Qed.

Print Assumptions snapshot_word_reads_defined.
Print Assumptions snapshot_word_replacement_evaluation.
Print Assumptions snapshot_word_setup_execution.
