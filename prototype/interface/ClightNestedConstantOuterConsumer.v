From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightNoWrap
  ClightRedundantSet ClightRectangularGuard ClightRegionProgress ClightPureExpr.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryWindowCells GuardMemoryBooleanScan
  GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestSourceDecode
  AffineNestLeafModel AffineNestLoopEncoding AffineNestScanModel AffineNestValuation AffineNestMathDomain.
From GuardInterface Require Import ClightNestedConstantSite ClightNestedConstantSiteFacts
  ClightNestedConstantSiteNumeric ClightNestedConstantSitePrepare ClightNestedConstantScanNames
  ClightNestedConstantScanStatic ClightNestedConstantHeaders ClightNestedConstantNumericInputs
  ClightNestedConstantNumericGuard ClightNestedConstantModel ClightConstantBoundModel
  ClightLoadedOffsetHeader ClightSignedIndexedOffsetHeader ClightAffineJointObservation
  ClightObservedHeaderPrefix ClightExpressionBodyPrefix ClightNestedExpressionCapture ClightConstantJointOuterScan
  ClightNestedExpressionPrefix.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition ncs_outer_statement shape proposal observers := constant_joint_outer_statement(ncs_root_cache shape)(ncs_child_cache shape)
  (ncs_scan_controls proposal(ncs_row shape))(ncs_scan_controls proposal(ncs_root_cache shape))
  (ncs_scan_controls proposal(ncs_column shape))(ncs_scan_controls proposal(ncs_child_helper shape))
  (affine_proposed_result proposal)(ncs_component shape)(ncs_scan_controls proposal)(ncs_scan_values shape proposal)
  observers(affine_proposed_operations proposal).
Definition ncs_outer_code shape proposal := ncs_outer_statement shape proposal(ncs_observer_templates shape).
Definition ncs_outer_result shape proposal entry observers := memory_boolean_scan_result
  (fun i=>memory_boolean_scan_result
    (fun j=>affine_scan_result(ncs_component shape)
      (nested_constant_point_valuation(entry_temps entry)(ncs_row shape)(ncs_column shape) i j) 0
      (affine_joint_observation_result
        (window_multi_pointer_locations(entry_temps(nested_expression_inner_entry(ncs_row shape)(ncs_column shape) i entry))
          (affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal)) observers(affine_proposed_operations proposal)))
    0(Z.to_nat(Int.signed(temp_word(ncs_child_cache shape)(entry_temps entry)))))
  0(Z.to_nat(Int.signed(temp_word(ncs_root_cache shape)(entry_temps entry)))).

Section CONSUMER.
Variables source : statement.
Variables parameters live : list ident.
Variable proposal : affine_guard_proposal.
Variable shape : nested_constant_shape.
Variable site : nested_constant_site source parameters live proposal shape.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable checked : temp_env.
Variable memory : mem.
Variable checked_source_after : temp_env.
Variable final : mem.
Variable receipt : ncs_prepared_receipt source parameters live proposal shape fe ge locals checked memory checked_source_after final.
Let entry:=Entry ge locals(ncs_prepared_temps shape checked) memory.
Variable observers : list clight_word_observer.
Variable headers : ncs_observation_receipt shape entry observers.
Let prefix:=expression_body_prefix fe(ncs_row shape)(ncs_root_cache shape)
  (signed_load_offset(ncs_pointer shape)(ncs_delta shape))
  (nested_expression_body(ncs_column shape)(signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape))
    (constant_body_source(ncs_iterator shape)(Int.repr(ncs_upper shape))(ncs_leaf shape)))
  (ncs_stable source parameters live shape)(ncs_header_ready shape)(fun _=>map word_observer_snapshot observers) 0 entry.

Lemma ncs_outer_child_positive : 0<Int.signed(temp_word(ncs_child_cache shape)(entry_temps entry)).
Proof.
  pose proof(ncs_prepare_accept receipt) as ACCEPT.
  change(ncs_numeric_flag parameters proposal shape entry=true) in ACCEPT.
  unfold ncs_numeric_flag,nested_constant_numeric_flag in ACCEPT.
  destruct(register_positive(ncs_root_cache shape) entry); [|discriminate].
  destruct(register_positive(ncs_child_cache shape) entry) eqn:CHILD; [|discriminate].
  exact(@register_positive_sound(ncs_child_cache shape) entry CHILD).
Qed.

Lemma ncs_outer_value_static identifier : In identifier([ncs_row shape;ncs_column shape]++parameters) ->
  identifier<>ncs_column shape -> identifier<>ncs_row shape -> ncs_scan_values shape proposal identifier=identifier.
Proof.
  intros MEMBER COLUMN ROW; apply in_app_iff in MEMBER as [COORDINATE|PARAMETER].
  - cbn [List.In] in COORDINATE; intuition congruence.
  - apply(ncs_scan_value_parameter site); exact PARAMETER.
Qed.

(** All premises of the original-source outer service are discharged here.
    The static facts come from the site checker, and dynamic facts come from
    the actual prepared execution receipt. There is no additional callback. *)
Local Ltac solve_outer :=
  cbn zeta;
  try reflexivity;
  try exact(proj1(ncs_scan_component_shape site));
  try exact(proj1(proj2(ncs_scan_component_shape site)));
  try exact(proj2(proj2(ncs_scan_component_shape site)));
  try exact(ncs_scan_component_protected site);
  try exact(ncs_component_lower site);
  try exact(ncs_scan_word_scope site);
  try exact(ncs_scan_helpers_stable site ltac:(right; left; reflexivity));
  try exact(ncs_prepare_component receipt);
  try exact(affine_leaf_writes(ncs_scan_leaf site));
  try exact(proj1(ncs_scan_source_effects site));
  try exact(proj1(proj2(ncs_scan_source_effects site)));
  try exact(proj2(proj2(ncs_scan_source_effects site)));
  try exact(ncs_scan_stable_live source parameters live shape);
  try exact(ncs_scan_component_unique site);
  try exact(ncs_scan_flag_word site);
  try exact ncs_outer_value_static;
  try solve[intros identifier MEMBER; apply(ncs_scan_value_iterator proposal); exact MEMBER];
  try solve[intros i j ROWS COLUMNS; exact(proj1(ncs_prepare_scan_inputs receipt ROWS COLUMNS))];
  try solve[intros i j ROWS COLUMNS; exact(proj2(ncs_prepare_scan_inputs receipt ROWS COLUMNS))];
  try solve[intros identifier MEMBER; apply(ncs_site_pointer_stable site); right; exact MEMBER];
  try solve[apply(@ncs_scan_coordinate_not_stable source parameters live shape _); unfold ncs_coordinates; cbn [List.In]; tauto];
  try solve[intros identifier MEMBER BAD; cbn [List.In] in BAD; destruct BAD as [SAME|[]]; subst identifier;
    apply(@ncs_scan_coordinate_not_stable source parameters live shape (ncs_iterator shape)) in MEMBER; [exact MEMBER|unfold ncs_coordinates; cbn [List.In]; tauto]];
  try solve[intros identifier MEMBER; exact MEMBER];
  try solve[apply(ncs_site_caches_stable site); unfold ncs_caches; cbn [List.In]; tauto];
  try solve[intros observer ACTIVE MEMBER; pose proof(ncs_receipt_reads headers) as READS;
    rewrite Forall_forall in READS; exact(READS observer MEMBER)];
  try solve[intros observer MEMBER; exact(ncs_scan_observer_scope site headers observer MEMBER)];
  try solve[intros i j ROWS COLUMNS; apply nested_constant_point_column;
    pose proof(ncs_scan_coordinate_unique site) as FRESH; unfold ncs_coordinates in FRESH;
    repeat match goal with H : NoDup(_::_) |- _ => apply NoDup_cons_iff in H as [? H] end;
    cbn [List.In] in *; intuition congruence];
  try solve[intros i j identifier ROWS COLUMNS MEMBER DISTINCT; apply nested_constant_point_other; exact DISTINCT];
  try solve[intros ACTIVE; pose proof(proj2(ncs_receipt_ready headers)) as [b [o [r [P [READ WORD]]]]];
    exists(Int.add r(ncs_child_delta shape)); exact WORD];
  try solve[intros ACTIVE; pose proof ncs_outer_child_positive; lia];
  try solve[cbn [List.In]; tauto].

Local Ltac finish_outer :=
  solve_outer;
  try solve[intros identifier MEMBER; apply(ncs_scan_value_iterator proposal); unfold ncs_coordinates; cbn [affine_nest_iterators List.In] in *; tauto];
  try solve[apply(ncs_scan_value_iterator proposal); unfold ncs_coordinates; cbn [List.In]; tauto];
  try solve[intros i current mem READY RANGE ROW FRAME OBSERVED;
    eapply ncs_root_header_from_receipt; [exact headers| |exact FRAME|exact OBSERVED];
    apply(ncs_site_pointer_stable site); left; reflexivity];
  try solve[intros i j current mem ROWS COLUMNS ROW COLUMN FRAME OBSERVED;
    eapply ncs_child_header_from_receipt; [exact headers| |exact FRAME|exact OBSERVED];
    apply(ncs_site_pointer_stable site); left; reflexivity];
  try solve[intros identifier MEMBER; destruct(ncs_scan_component_private site MEMBER) as [PRIVATE FLAG];
    split; [|exact FLAG]; unfold ncs_outer_controls in PRIVATE; cbn [app List.In] in *; tauto];
  try solve[pose proof(ncs_scan_coordinate_unique site) as FRESH; unfold ncs_coordinates in FRESH;
    repeat match goal with H : NoDup(_::_) |- _ => apply NoDup_cons_iff in H as [? H] end;
    cbn [List.In] in *; intuition congruence];
  try solve[pose proof(ncs_scan_outer_unique site) as FRESH; unfold ncs_outer_controls in FRESH;
    repeat match goal with H : NoDup(_::_) |- _ => apply NoDup_cons_iff in H as [? H] end;
    pose proof(ncs_scan_outer_private site(identifier:=ncs_scan_controls proposal(ncs_row shape))
      ltac:(unfold ncs_outer_controls; cbn [List.In]; tauto)) as [ROW_PRIVATE ROW_FLAG];
    pose proof(ncs_scan_outer_private site(identifier:=ncs_scan_controls proposal(ncs_root_cache shape))
      ltac:(unfold ncs_outer_controls; cbn [List.In]; tauto)) as [ROOT_PRIVATE ROOT_FLAG];
    pose proof(ncs_scan_outer_private site(identifier:=ncs_scan_controls proposal(ncs_column shape))
      ltac:(unfold ncs_outer_controls; cbn [List.In]; tauto)) as [COLUMN_PRIVATE COLUMN_FLAG];
    pose proof(ncs_scan_outer_private site(identifier:=ncs_scan_controls proposal(ncs_child_helper shape))
      ltac:(unfold ncs_outer_controls; cbn [List.In]; tauto)) as [CHILD_PRIVATE CHILD_FLAG];
    pose proof(ncs_scan_flag_private site) as FLAG_PRIVATE; unfold ncs_outer_controls in FLAG_PRIVATE;
    cbn [app List.In] in *; intuition congruence].

Theorem ncs_outer_scan_execution : prefix -> exists after,
  exec_stmt fe ge locals(entry_temps entry) memory(ncs_outer_code shape proposal) E0 after memory Out_normal /\
  temp_agree(ncs_ports source parameters live shape)(entry_temps entry) after /\
  after!(affine_proposed_result proposal)=Some(memory_boolean_word(ncs_outer_result shape proposal entry observers)).
Proof.
  intro PREFIX.
  unfold ncs_outer_code,ncs_outer_statement.
  rewrite <-(ncs_outer_syntax_uses_templates headers
    (ncs_scan_controls proposal(ncs_row shape))(ncs_scan_controls proposal(ncs_root_cache shape))
    (ncs_scan_controls proposal(ncs_column shape))(ncs_scan_controls proposal(ncs_child_helper shape))
    (affine_proposed_result proposal)(ncs_component shape)(ncs_scan_controls proposal)(ncs_scan_values shape proposal)
    (affine_proposed_operations proposal)).
  edestruct constant_joint_outer_scan_execution with
    (iterator:=ncs_iterator shape)(helper:=ncs_component_helper shape)(row:=ncs_row shape)(column:=ncs_column shape)
    (root_cache:=ncs_root_cache shape)(child_cache:=ncs_child_cache shape)(upper:=ncs_upper shape)(body:=ncs_leaf shape)
    (child:=AffineSourceLeaf(ncs_leaf shape))(coordinates:=ncs_coordinates shape)(prefix:=[ncs_row shape;ncs_column shape])
    (parameters:=parameters)(pointers:=affine_proposed_pointers proposal)(bounds:=affine_proposed_leaf_bounds proposal)
    (window_lower:=affine_proposed_window_lower proposal)(window_upper:=affine_proposed_window_upper proposal)
    (certificate:=ncs_scan_leaf site)(code:=ncs_component_code site)
    (stable:=ncs_stable source parameters live shape)(public:=ncs_stable source parameters live shape)
    (live:=ncs_ports source parameters live shape)(leaf_written:=([]:list ident))(source_written:=[ncs_iterator shape])
    (observers:=observers)(fe:=fe)(entry:=entry)(ready:=ncs_header_ready shape)
    (root_bound:=signed_load_offset(ncs_pointer shape)(ncs_delta shape))
    (child_bound:=signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape))
    (valuation:=nested_constant_point_valuation(entry_temps entry)(ncs_row shape)(ncs_column shape))
    (controls:=ncs_scan_controls proposal)(values:=ncs_scan_values shape proposal)
    (row_cursor:=ncs_scan_controls proposal(ncs_row shape))(row_limit:=ncs_scan_controls proposal(ncs_root_cache shape))
    (column_cursor:=ncs_scan_controls proposal(ncs_column shape))(column_limit:=ncs_scan_controls proposal(ncs_child_helper shape))
    (flag:=affine_proposed_result proposal)(checked:=entry_temps entry)
    as [after [RUN [KEEP [FLAG SOUND]]]].
  all: try finish_outer.
  all: try exact PREFIX.
  all: try apply temp_agree_refl.
  all: try (exists after; repeat split; assumption).
Qed.


Theorem ncs_outer_accepted_model : prefix -> ncs_outer_result shape proposal entry observers=true -> exists after,
  exec_stmt fe ge locals(entry_temps entry) memory(ncs_model shape) E0 after final Out_normal /\
  temp_agree(ncs_scope source live) checked_source_after after.
Proof.
  intros PREFIX ACCEPT.
  destruct(ncs_prepare_source receipt) as [after [SOURCE [PUBLIC [CHILD COMPONENT]]]].
  pose proof SOURCE as ORIGINAL; rewrite(ncs_exact site) in ORIGINAL.
  edestruct constant_joint_outer_cached_source with
    (iterator:=ncs_iterator shape)(helper:=ncs_component_helper shape)(row:=ncs_row shape)(column:=ncs_column shape)
    (root_cache:=ncs_root_cache shape)(child_cache:=ncs_child_cache shape)(upper:=ncs_upper shape)(body:=ncs_leaf shape)
    (child:=AffineSourceLeaf(ncs_leaf shape))(coordinates:=ncs_coordinates shape)(prefix:=[ncs_row shape;ncs_column shape])
    (parameters:=parameters)(pointers:=affine_proposed_pointers proposal)(bounds:=affine_proposed_leaf_bounds proposal)
    (window_lower:=affine_proposed_window_lower proposal)(window_upper:=affine_proposed_window_upper proposal)
    (certificate:=ncs_scan_leaf site)(code:=ncs_component_code site)
    (stable:=ncs_stable source parameters live shape)(public:=ncs_stable source parameters live shape)
    (live:=ncs_ports source parameters live shape)(leaf_written:=([]:list ident))(source_written:=[ncs_iterator shape])
    (observers:=observers)(fe:=fe)(entry:=entry)(ready:=ncs_header_ready shape)
    (root_bound:=signed_load_offset(ncs_pointer shape)(ncs_delta shape))
    (child_bound:=signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape))
    (valuation:=nested_constant_point_valuation(entry_temps entry)(ncs_row shape)(ncs_column shape))
    (controls:=ncs_scan_controls proposal)(values:=ncs_scan_values shape proposal)
    (row_cursor:=ncs_scan_controls proposal(ncs_row shape))(row_limit:=ncs_scan_controls proposal(ncs_root_cache shape))
    (column_cursor:=ncs_scan_controls proposal(ncs_column shape))(column_limit:=ncs_scan_controls proposal(ncs_child_helper shape))
    (flag:=affine_proposed_result proposal)(after:=after)(final:=final)
    as [CACHED OBSERVED].
  all: try finish_outer.
  all: try exact PREFIX.
  all: try exact ACCEPT.
  all: try exact(ncs_prepare_row receipt).
  all: try exact ORIGINAL.
  - exists after; split; [|exact PUBLIC].
    unfold ncs_model.
    eapply nested_constant_closed_preinitialized_model with(child_upper:=temp_word(ncs_child_cache shape)(entry_temps entry)).
    + exact(ncs_scan_model_unique site).
    + exact(affine_leaf_quiet(ncs_scan_leaf site)).
    + exact(affine_leaf_writes(ncs_scan_leaf site)).
    + destruct(proj2(ncs_receipt_ready headers)) as [b [o [r [P [READ WORD]]]]].
      unfold temp_word; rewrite WORD; reflexivity.
    + exact(ncs_prepare_child receipt).
    + exact(ncs_prepare_component receipt).
    + exact CACHED.
Qed.

End CONSUMER.

Print Assumptions ncs_outer_child_positive.
Print Assumptions ncs_outer_value_static.
Print Assumptions ncs_outer_scan_execution.
Print Assumptions ncs_outer_accepted_model.
