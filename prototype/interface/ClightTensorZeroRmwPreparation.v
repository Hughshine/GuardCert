From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightNoWrap
  ClightRegionProgress ClightRectangularLoops ClightCountedLoop ClightPureExpr CompCertMemoryActions ClightSyntaxEquality
  ClightLoopSyntax ClightRectangularGuard.
From GuardInterface Require Import ClightTensorLoadedWordFactory ClightTensorLoadedWordDriver
  ClightZeroRmwObservation ClightZeroRmwCondition ClightNestedConstantSite ClightNestedConstantHeaders
  ClightNestedExpressionTransport ClightNestedExpressionCapture ClightNestedConstantFirstLeaf
  ClightExpressionHeaderCapture ClightLoadedBoundSyntax ClightLoadedOffsetHeader
  ClightSignedIndexedOffsetHeader ClightConstantBoundModel ClightTensorHeaderFirstPoint
  ClightAffineJointObservation ClightObservedHeaderPrefix ClightCheckPlanFrame ClightStrictLoopProgress
  ClightDirectWordObservation ClightLiteralBoundPreparation.
From GuardInterface Require Import ClightTensorRegionPackage.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition tzr_component d := constant_body_source(ncs_iterator(lwd_shape d))
  (Int.repr(ncs_upper(lwd_shape d)))(ncs_leaf(lwd_shape d)).
Record tensor_zero_rmw_static live d alpha := TensorZeroRmwStatic {
  tzr_base : loaded_word_static live d;
  tzr_rhs : lwd_rhs d=zero_rmw_rhs alpha(Ederef(direct_word_address(lwd_pointer d)(lwd_index d))type_int32s);
  tzr_alpha_stable : In alpha(lwd_stable live d);
  tzr_control : check_zero_rmw_control alpha(tzr_component d)=true;
  tzr_positive : 0<ncs_upper(lwd_shape d)
}.
Definition check_tensor_zero_rmw_static live d alpha : option(tensor_zero_rmw_static live d alpha).
Proof.
  destruct(check_loaded_word_static live d)as [base|]; [|exact None].
  destruct(expression_eq(lwd_rhs d)(zero_rmw_rhs alpha
    (Ederef(direct_word_address(lwd_pointer d)(lwd_index d))type_int32s)))as [RHS|]; [|exact None].
  destruct(in_dec peq alpha(lwd_stable live d))as [STABLE|]; [|exact None].
  destruct(check_zero_rmw_control alpha(tzr_component d))eqn:CONTROL; [|exact None].
  destruct(Z_lt_dec 0(ncs_upper(lwd_shape d)))as [POSITIVE|]; [|exact None].
  exact(Some(@TensorZeroRmwStatic live d alpha base RHS STABLE CONTROL POSITIVE)).
Defined.

Lemma tzr_component_effects live d alpha(static:tensor_zero_rmw_static live d alpha) :
  normal_statement(tzr_component d)=true /\ quiet_statement(tzr_component d)=true /\
  writes_only[ncs_iterator(lwd_shape d)](tzr_component d).
Proof.
  unfold tzr_component; rewrite(lws_leaf(tzr_base static)); split.
  - apply constant_literal_source_normal; reflexivity.
  - split; [apply constant_literal_source_quiet; reflexivity|].
    unfold constant_body_source,strict_frontend_loop,rectangle_reset,counter_increment,direct_word_store.
    repeat first[apply writes_sequence|apply writes_if|apply writes_loop|apply writes_set; cbn; auto 10|constructor].
Qed.

(** A receipt's actual snapshots contain defined Mint32 words. Dummy observer
    templates need no such property and are never used in this effect proof. *)
Lemma ncs_receipt_word_snapshots shape entry observers(receipt:ncs_observation_receipt shape entry observers) :
  Forall(fun pair=>location_chunk(fst pair)=Mint32 /\ exists word,snd pair=Vint word)
    (map word_observer_snapshot observers).
Proof.
  rewrite(ncs_receipt_snapshots receipt).
  destruct(ncs_receipt_ready receipt)as
    [[block [offset [raw [POINTER [READ CACHE]]]]]
     [child_block [child_offset [child_raw [CHILD_POINTER [CHILD_READ CHILD_CACHE]]]]]].
  assert(SAME:Some(Vptr child_block child_offset)=Some(Vptr block offset))by(congruence).
  inversion SAME; subst child_block child_offset.
  unfold ncs_observations,loaded_offset_observations,indexed_offset_observations.
  rewrite POINTER,READ,CHILD_READ; cbn.
  repeat constructor; eexists; reflexivity.
Qed.

Lemma mint32_words_preserve_snapshots observations before after :
  Forall(fun pair=>location_chunk(fst pair)=Mint32 /\ exists word,snd pair=Vint word)observations ->
  mint32_words_preserved before after -> header_observations_match observations before ->
  header_observations_match observations after.
Proof.
  intros WORDS PRESERVE OBSERVED; unfold header_observations_match in *.
  apply Forall_forall; intros pair MEMBER.
  apply Forall_forall with(x:=pair)in WORDS; [|exact MEMBER].
  apply Forall_forall with(x:=pair)in OBSERVED; [|exact MEMBER].
  destruct pair as [[chunk block offset]value]; cbn in *.
  destruct WORDS as [CHUNK [word VALUE]]; subst chunk value.
  apply PRESERVE; exact OBSERVED.
Qed.

Section PREPARATION.
Variables live : list ident.
Variable d : loaded_word_description.
Variable alpha : ident.
Variable static : tensor_zero_rmw_static live d alpha.
Let shape:=lwd_shape d.
Let stable:=lwd_stable live d.
Let row:=ncs_row shape.
Let column:=ncs_column shape.
Let iterator:=ncs_iterator shape.
Let root_cache:=ncs_root_cache shape.
Let child_cache:=ncs_child_cache shape.
Let upper:=ncs_upper shape.

Lemma tzr_coordinates_distinct : row<>column /\ iterator<>row /\ iterator<>column.
Proof.
  pose proof(@tensor_unique_sound _ (lws_coordinates_unique(tzr_base static)))as UNIQUE.
  unfold ncs_coordinates in UNIQUE; repeat rewrite NoDup_cons_iff in UNIQUE.
  cbn in UNIQUE; unfold row,column,iterator,shape; intuition congruence.
Qed.
Lemma tzr_stable_member id :
  In id[ncs_component_helper shape;root_cache;child_cache;lwd_pointer d;ncs_pointer shape] -> In id stable.
Proof. intro MEMBER; eapply tensor_subset_sound; [exact(lws_stable_members(tzr_base static))|exact MEMBER]. Qed.

(** A positive original source path supplies a real RMW execution before any
    memory-changing body action. No future cached-source execution licenses it. *)
Theorem tensor_zero_rmw_captured_scalar fe ge locals temps memory after final observers
  (receipt:ncs_observation_receipt shape(Entry ge locals temps memory)observers) :
  temps!row=Some(Vint Int.zero) ->
  tensor_word_driver_profile_flag shape(lwd_root_cap d)(lwd_child_cap d)(Entry ge locals temps memory)=true ->
  exec_stmt fe ge locals temps memory(ncs_original shape)E0 after final Out_normal ->
  exists word,temps!alpha=Some(Vint word).
Proof.
  intros ROW PROFILE SOURCE.
  unfold tensor_word_driver_profile_flag,register_range_flag in PROFILE.
  repeat rewrite andb_true_iff in PROFILE; destruct PROFILE as [[ROOT _][CHILD _]].
  pose proof(@ncs_root_header_from_receipt shape(Entry ge locals temps memory)observers receipt
    [ncs_pointer shape]temps memory(or_introl eq_refl)(temp_agree_refl _ _)(ncs_receipt_initial receipt))as ROOT_EVAL.
  pose proof(@ncs_child_header_from_receipt shape(Entry ge locals temps memory)observers receipt
    [ncs_pointer shape]temps memory(or_introl eq_refl)(temp_agree_refl _ _)(ncs_receipt_initial receipt))as CHILD_EVAL.
  assert(LITERAL:Int.lt Int.zero(Int.repr upper)=true).
  { unfold Int.lt; rewrite Int.signed_zero,Int.signed_repr by exact(lws_upper(tzr_base static)).
    pose proof(tzr_positive static)as POSITIVE; change(0<upper)in POSITIVE.
    destruct(zlt 0 upper); [reflexivity|lia]. }
  destruct(@nested_constant_original_first_leaf fe ge locals row
    (signed_load_offset(ncs_pointer shape)(ncs_delta shape))column
    (signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape))
    iterator(Int.repr upper)(ncs_leaf shape)temps memory after final
    (temp_word root_cache temps)(temp_word child_cache temps)
    eq_refl eq_refl ltac:(unfold shape; rewrite(lws_leaf(tzr_base static)); reflexivity)
    ltac:(unfold shape; rewrite(lws_leaf(tzr_base static)); reflexivity)
    ltac:(apply tensor_child_header_independent; change(column<>ncs_pointer shape); intro SAME;
      apply(@lwd_stable_coordinate_private live d column); [cbn; auto 10|
        change(In column stable); rewrite SAME; apply tzr_stable_member; cbn; auto 10])
    ROOT_EVAL CHILD_EVAL ltac:(unfold temp_word at 1; rewrite ROW; exact ROOT)CHILD LITERAL SOURCE)
    as [leaf_after [leaf_final LEAF]].
  unfold shape in LEAF; rewrite(lws_leaf(tzr_base static)),(tzr_rhs static)in LEAF.
  destruct(@zero_rmw_original_assignment_licenses_scalar alpha(direct_word_address(lwd_pointer d)(lwd_index d))
    fe ge locals(PTree.set iterator(Vint Int.zero)(PTree.set column(Vint Int.zero)temps))
    memory E0 leaf_after leaf_final Out_normal LEAF)as [word WORD].
  change((PTree.set iterator(Vint Int.zero)(PTree.set column(Vint Int.zero)temps))!alpha=Some(Vint word))in WORD.
  rewrite !PTree.gso in WORD.
  - exists word; exact WORD.
  - intro SAME; apply(@lwd_stable_coordinate_private live d column); [cbn; auto 10|
      change(In column stable); rewrite <-SAME; exact(tzr_alpha_stable static)].
  - intro SAME; apply(@lwd_stable_coordinate_private live d iterator); [cbn; auto 10|
      change(In iterator stable); rewrite <-SAME; exact(tzr_alpha_stable static)].
Qed.

(** Value preservation supplies the same original/cached execution, including
    final memory. No separation-tree acceptance or no-wrap premise is used. *)
Theorem tensor_zero_rmw_captured_cached fe ge locals temps memory after final observers
  (receipt:ncs_observation_receipt shape(Entry ge locals temps memory)observers) :
  temps!row=Some(Vint Int.zero) -> temps!alpha=Some(Vint Int.zero) ->
  0<=Int.signed(temp_word root_cache temps) -> 0<=Int.signed(temp_word child_cache temps) ->
  exec_stmt fe ge locals temps memory(ncs_original shape)E0 after final Out_normal ->
  exec_stmt fe ge locals temps memory(tensor_word_driver_cached shape)E0 after final Out_normal.
Proof.
  intros ROW ZERO ROOT_RANGE CHILD_RANGE SOURCE.
  assert(ROOT:temps!root_cache=Some(Vint(temp_word root_cache temps))).
  { destruct(proj1(ncs_receipt_ready receipt))as [b [o [raw [_ [_ CACHE]]]]]; change(temps!root_cache=Some(Vint(Int.add raw(ncs_delta shape))))in CACHE; unfold temp_word; rewrite CACHE; reflexivity. }
  assert(CHILD:temps!child_cache=Some(Vint(temp_word child_cache temps))).
  { destruct(proj2(ncs_receipt_ready receipt))as [b [o [raw [_ [_ CACHE]]]]]; change(temps!child_cache=Some(Vint(Int.add raw(ncs_child_delta shape))))in CACHE; unfold temp_word; rewrite CACHE; reflexivity. }
  destruct(tzr_component_effects static)as [NORMAL [QUIET WRITES]].
  destruct tzr_coordinates_distinct as [ROW_COLUMN [ITERATOR_ROW ITERATOR_COLUMN]].
  unfold ncs_original in SOURCE; fold shape row column iterator upper in SOURCE.
  edestruct nested_expression_initial_cached with
    (fe:=fe)(ge:=ge)(locals:=locals)(row:=row)(column:=column)(cache:=root_cache)(child_cache:=child_cache)
    (body:=tzr_component d)(stable:=stable)(written:=[iterator])(base:=temps)
    (observations:=map word_observer_snapshot observers)(upper:=temp_word root_cache temps)
    (child_upper:=temp_word child_cache temps)(memory:=memory)(after:=after)(final:=final)
    (bound:=signed_load_offset(ncs_pointer shape)(ncs_delta shape))
    (child_bound:=signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape))
    as [CACHED OBSERVED].
  all: try reflexivity; try assumption.
  all: try solve[apply tzr_stable_member; cbn; auto 10].
  all: try solve[eapply lwd_stable_coordinate_private; cbn; auto 10].
  all: try solve[cbn; intuition congruence].
  - intros id MEMBER [SAME|[]]; subst id.
    apply(@lwd_stable_coordinate_private live d iterator); [cbn; auto 10|exact MEMBER].
  - intros i current mem RANGE COUNTER FRAME OBSERVED.
    eapply(@ncs_root_header_from_receipt shape(Entry ge locals temps memory)observers receipt stable current mem);
      [apply tzr_stable_member; cbn; auto 10|exact FRAME|exact OBSERVED].
  - intros i j current mem RANGE COLUMNS COUNTER COLUMN FRAME OBSERVED.
    eapply(@ncs_child_header_from_receipt shape(Entry ge locals temps memory)observers receipt stable current mem);
      [apply tzr_stable_member; cbn; auto 10|exact FRAME|exact OBSERVED].
  - intros i j current mem exit last RANGE COLUMNS COUNTER COLUMN FRAME OBSERVED RUN.
    eapply mint32_words_preserve_snapshots; [exact(ncs_receipt_word_snapshots receipt)| |exact OBSERVED].
    apply(proj1(@checked_zero_rmw_control_execution alpha fe ge locals current mem(tzr_component d)
      E0 exit last Out_normal RUN(tzr_control static)ltac:(rewrite FRAME by exact(tzr_alpha_stable static); exact ZERO))).
  - exact(ncs_receipt_initial receipt).
Qed.
End PREPARATION.

Print Assumptions check_tensor_zero_rmw_static.
Print Assumptions tzr_component_effects.
Print Assumptions ncs_receipt_word_snapshots.
Print Assumptions mint32_words_preserve_snapshots.
Print Assumptions tensor_zero_rmw_captured_scalar.
Print Assumptions tensor_zero_rmw_captured_cached.
