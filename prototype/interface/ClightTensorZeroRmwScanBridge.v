From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightNoWrap ClightRedundantSet
  ClightRectangularGuard ClightLoopSyntax ClightRegionProgress ClightPureExpr.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardInterface Require Import ClightTensorZeroRmwPreparation ClightTensorPreparedGenerated
  ClightTensorLoadedWordFactory ClightTensorLoadedWordDriver ClightTensorRegionPackage
  ClightNestedConstantSite ClightNestedConstantHeaders ClightNestedExpressionCapture ClightTensorHeaderCapture
  ClightLiteralBoundPreparation ClightConstantBoundModel ClightCheckPlanFrame ClightExpressionHeaderCapture
  ClightNestedExpressionTransport ClightSignedExpressionProgress ClightLoadedOffsetHeader
  ClightSignedIndexedOffsetHeader ClightLoadedBoundSyntax ClightStrictLoopProgress ClightDirectWordObservation
  ClightZeroRmwCondition ClightWordArithmeticTransport ClightQuietDeterminacy ClightSharedGuard
  ClightReadonlyRewrite ClightAffineJointObservation.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition lwd_scan_code d := tensor_word_driver_scan(lwd_shape d)(lwd_pointer d)
  (lwd_row_cursor d)(lwd_row_limit d)(lwd_column_cursor d)(lwd_column_limit d)
  (lwd_component_cursor d)(lwd_component_limit d)(lwd_flag d)(lwd_index d)(lwd_rename d).
Definition lwd_zero_shortcut d := Ssequence
  (literal_bound_set(ncs_component_helper(lwd_shape d))(Int.repr(ncs_upper(lwd_shape d))))
  (Sset(lwd_flag d)(Econst_int Int.one type_int32s)).
Definition lwd_zero_code d alpha := tree_statement(register_tree(ncs_row(lwd_shape d))Int.zero)
  (Ssequence(tensor_header_capture(lwd_shape d))
    (tree_statement(tensor_word_driver_profile_tree(lwd_shape d)(lwd_root_cap d)(lwd_child_cap d))
      (tree_statement(zero_rmw_condition alpha)(lwd_zero_shortcut d)(lwd_scan_code d))
      (tensor_word_driver_refuse(lwd_flag d))))
  (tensor_word_driver_refuse(lwd_flag d)).

Section DRIVER.
Variables live : list ident.
Variable d : loaded_word_description.
Variable alpha : ident.
Variable static : tensor_zero_rmw_static live d alpha.
Let shape:=lwd_shape d.
Let base:=tzr_base static.
Let ports:=tensor_word_driver_ports shape live.
Let scan_live:=tensor_word_driver_scan_live shape live.
Let row:=ncs_row shape.
Let column:=ncs_column shape.
Let iterator:=ncs_iterator shape.
Let root_cache:=ncs_root_cache shape.
Let child_cache:=ncs_child_cache shape.
Let upper:=ncs_upper shape.
Let helper:=ncs_component_helper shape.
Let flag:=lwd_flag d.

Lemma lwd_zero_caches_private : forall id,
  In id[ncs_root_cache shape;ncs_child_cache shape;helper] -> ~In id ports.
Proof. intros id MEMBER; eapply tensor_disjoint_sound; [exact(lws_cache_private base)|exact MEMBER]. Qed.
Lemma lwd_zero_controls_private : forall id,In id(lwd_controls d) -> ~In id scan_live.
Proof. intros id MEMBER; eapply tensor_disjoint_sound; [exact(lws_controls_private base)|exact MEMBER]. Qed.
Lemma lwd_zero_flag_private : ~In flag ports.
Proof.
  intro MEMBER; apply(@lwd_zero_controls_private flag ltac:(unfold flag,lwd_controls; cbn; auto 10)).
  unfold scan_live,tensor_word_driver_scan_live; right; right; right; exact MEMBER.
Qed.
Lemma lwd_zero_private_unique : NoDup(lwd_private d).
Proof. apply tensor_unique_sound; exact(lws_private_unique base). Qed.
Lemma lwd_zero_row_scope : In(ncs_row shape)ports.
Proof. exact(@tensor_word_driver_row_scope shape live). Qed.
Lemma lwd_zero_header_private : ncs_column shape<>ncs_pointer shape.
Proof.
  intro SAME; apply(@lwd_stable_coordinate_private live d(ncs_column shape)); [cbn; auto|].
  rewrite SAME; eapply tensor_subset_sound; [exact(lws_stable_members base)|cbn; auto 10].
Qed.
Lemma lwd_zero_cached_scope : incl(statement_temps(tensor_word_driver_cached shape))scan_live.
Proof. intros id MEMBER; eapply tensor_subset_sound; [exact(lws_cached_scope base)|exact MEMBER]. Qed.
Lemma lwd_zero_helper_cached_private : ~In helper(statement_temps(tensor_word_driver_cached shape)++live).
Proof.
  rewrite in_app_iff; intros [MEMBER|MEMBER].
  - apply(@lwd_member_false helper(statement_temps(tensor_word_driver_cached shape))(lws_helper_cached base)); exact MEMBER.
  - apply(@lwd_zero_caches_private helper ltac:(cbn; auto)); unfold ports,tensor_word_driver_ports; apply in_or_app; right; exact MEMBER.
Qed.
Lemma lwd_zero_flag_cached_private : ~In flag(statement_temps(tensor_word_driver_cached shape)++live).
Proof.
  rewrite in_app_iff; intros [MEMBER|MEMBER].
  - apply(@lwd_zero_controls_private flag ltac:(unfold flag,lwd_controls; cbn; auto 10)),lwd_zero_cached_scope; exact MEMBER.
  - apply lwd_zero_flag_private; unfold ports,tensor_word_driver_ports; apply in_or_app; right; exact MEMBER.
Qed.

(** The existing source-licensed scan remains the nonzero branch, with one
    capture and one scan. Its static premises come from the same data checker. *)
Theorem lwd_zero_existing_scan fe ge locals temps memory after final observers
  (receipt:ncs_observation_receipt shape(Entry ge locals temps memory)observers) :
  temps!(ncs_row shape)=Some(Vint Int.zero) ->
  tensor_word_driver_profile_flag shape(lwd_root_cap d)(lwd_child_cap d)(Entry ge locals temps memory)=true ->
  exec_stmt fe ge locals temps memory(ncs_original shape)E0 after final Out_normal ->
  exists accepted checked,
    exec_stmt fe ge locals temps memory(lwd_scan_code d)E0 checked memory Out_normal /\
    temp_agree ports temps checked /\ checked!flag=Some(memory_boolean_word accepted) /\
    checked!helper=Some(Vint(Int.repr(ncs_upper shape))) /\
    (accepted=true -> exists exit,
      exec_stmt fe ge locals checked memory(tensor_word_driver_canonical shape)E0 exit final Out_normal /\ temp_agree live after exit).
Proof.
  intros ROW PROFILE SOURCE.
  pose proof(lws_private_unique base)as RAW_NAMES; apply tensor_unique_sound in RAW_NAMES.
  pose proof(@tensor_unique_sound _ (lws_coordinates_unique base))as COORDS.
  pose proof(@tensor_disjoint_sound _ _ (lws_cache_private base))as CACHES.
  pose proof(@tensor_disjoint_sound _ _ (lws_controls_private base))as CONTROLS.
  pose proof(@tensor_subset_sound _ _ (lws_stable_members base))as STABLE.
  unfold lwd_private,lwd_controls in RAW_NAMES,CONTROLS; unfold ncs_coordinates in COORDS.
  repeat match goal with H:NoDup(_::_) |- _=>inversion H; clear H; subst end.
  cbn [In] in H1,H3,H4,H6,H7,H8,H9,H10,H11,H12,H13,H14.
  assert(RC:~In(lwd_row_cursor d)scan_live)by(apply lwd_zero_controls_private; unfold lwd_controls; cbn; auto 10).
  assert(RL:~In(lwd_row_limit d)scan_live)by(apply lwd_zero_controls_private; unfold lwd_controls; cbn; auto 10).
  assert(CC:~In(lwd_column_cursor d)scan_live)by(apply lwd_zero_controls_private; unfold lwd_controls; cbn; auto 10).
  assert(CL:~In(lwd_column_limit d)scan_live)by(apply lwd_zero_controls_private; unfold lwd_controls; cbn; auto 10).
  assert(KC:~In(lwd_component_cursor d)scan_live)by(apply lwd_zero_controls_private; unfold lwd_controls; cbn; auto 10).
  assert(KL:~In(lwd_component_limit d)scan_live)by(apply lwd_zero_controls_private; unfold lwd_controls; cbn; auto 10).
  assert(FL:~In flag scan_live)by(apply lwd_zero_controls_private; unfold flag,lwd_controls; cbn; auto 10).
  eapply tensor_word_driver_captured_scan with(rhs:=lwd_rhs d)(stable:=lwd_stable live d)
    (root_cap:=lwd_root_cap d)(child_cap:=lwd_child_cap d).
  all: try solve[exact(lws_leaf base)|apply word_arithmetic_check_sound; exact(lws_word base)|
    exact(lws_nonnegative base)|exact(lws_upper base)|exact(lws_root_cap base)|exact(lws_child_cap base)|
    exact(lws_original_frame base)|exact(lws_cached_frame base)|exact receipt|exact ROW|exact PROFILE|exact SOURCE|
    apply lwd_stable_scope|apply lwd_rename_stable|exact lwd_zero_header_private].
  all: try solve[apply tensor_subset_sound; exact(lws_cached_scope base)|apply tensor_subset_sound; exact(lws_index_scope base)|
    apply lwd_member_false; exact(lws_helper_cached base)].
  all: try solve[eapply CACHES; cbn; auto 10|apply STABLE; cbn; auto 10|eapply lwd_stable_coordinate_private; cbn; auto].
  all: try solve[unfold incl; intros id MEMBER; eapply tensor_subset_sound; [exact(lws_cached_scope base)|exact MEMBER]].
  all: try solve[unfold incl; intros id MEMBER; eapply tensor_subset_sound; [exact(lws_index_scope base)|exact MEMBER]].
  all: try solve[unfold shape,flag in *; unfold lwd_rename; repeat destruct(peq _ _); intuition congruence].
  all: try solve[unfold shape,flag in *; cbn [In]; intuition congruence].
Qed.

End DRIVER.

Print Assumptions lwd_zero_existing_scan.
