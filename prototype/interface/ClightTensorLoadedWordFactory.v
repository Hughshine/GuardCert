From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight Ctypes.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightSyntaxEquality ClightPrivateRegion ClightTempFootprint ClightNoWrap ClightMatrixGuard ClightRectangularGuard ClightCountedLoop.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryTensorSource GuardMemoryTiledCompiler.
From GuardInterface Require Import ClightNestedConstantSite ClightTensorLoadedWordDriver
  ClightTensorRegionPackage ClightTensorRegionPreservation ClightTensorRegionCompiler ClightTensorGeneratedCandidates
  ClightTensorGeneratedFactory ClightWordArithmeticTransport ClightDirectWordObservation
  ClightCheckPlanFrame ClightCheckPlan ClightStagedCheck ClightSharedGuard.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Source descriptions and names are untrusted data. The factory checks their
    actual syntax, finite scopes, typed allocation and canonical tensor model. *)
Record loaded_word_description := LoadedWordDescription {
  lwd_shape : nested_constant_shape;
  lwd_pointer : ident;
  lwd_index : expr;
  lwd_rhs : expr;
  lwd_row_cursor : ident; lwd_row_limit : ident;
  lwd_column_cursor : ident; lwd_column_limit : ident;
  lwd_component_cursor : ident; lwd_component_limit : ident;
  lwd_flag : ident;
  lwd_root_cap : Z; lwd_child_cap : Z
}.
Definition lwd_controls d := [lwd_row_cursor d;lwd_row_limit d;lwd_column_cursor d;
  lwd_column_limit d;lwd_component_cursor d;lwd_component_limit d;lwd_flag d].
Definition lwd_private d := ncs_root_cache(lwd_shape d)::ncs_child_cache(lwd_shape d)::
  ncs_component_helper(lwd_shape d)::lwd_controls d.
Definition lwd_stable live d := filter(fun id=>negb(tensor_member id(ncs_coordinates(lwd_shape d))))
  (tensor_word_driver_scan_live(lwd_shape d)live).
Definition lwd_rename d id :=
  if peq id(ncs_iterator(lwd_shape d))then lwd_component_cursor d else
  if peq id(ncs_column(lwd_shape d))then lwd_column_cursor d else
  if peq id(ncs_row(lwd_shape d))then lwd_row_cursor d else id.
Definition lwd_code d := tensor_word_driver_code(lwd_shape d)(lwd_pointer d)
  (lwd_row_cursor d)(lwd_row_limit d)(lwd_column_cursor d)(lwd_column_limit d)
  (lwd_component_cursor d)(lwd_component_limit d)(lwd_flag d)(lwd_index d)(lwd_rename d)
  (lwd_root_cap d)(lwd_child_cap d).
Definition lwd_integer_names (pool:list(ident*type)) := map fst(filter(fun pair=>if type_eq(snd pair)type_int32s then true else false)pool).
Definition lwd_candidate_pool (pool:list(ident*type)) d := filter(fun pair=>negb(tensor_member(fst pair)(lwd_private d)))pool.

(** These facts are internal checker output, not source-user proof fields. *)
Record loaded_word_static live d := LoadedWordStatic {
  lws_leaf : ncs_leaf(lwd_shape d)=direct_word_store(lwd_pointer d)(lwd_index d)(lwd_rhs d);
  lws_word : word_arithmetic_check(lwd_index d)=true;
  lws_nonnegative : 0<=ncs_upper(lwd_shape d);
  lws_upper : signed_range(ncs_upper(lwd_shape d));
  lws_root_cap : signed_range(lwd_root_cap d);
  lws_child_cap : signed_range(lwd_child_cap d);
  lws_original_frame : check_plan_frameable(ncs_original(lwd_shape d))=true;
  lws_cached_frame : check_plan_frameable(tensor_word_driver_cached(lwd_shape d))=true;
  lws_canonical_frame : check_plan_frameable(tensor_word_driver_canonical(lwd_shape d))=true;
  lws_cached_scope : tensor_subset(statement_temps(tensor_word_driver_cached(lwd_shape d)))
    (tensor_word_driver_scan_live(lwd_shape d)live)=true;
  lws_helper_cached : tensor_member(ncs_component_helper(lwd_shape d))
    (statement_temps(tensor_word_driver_cached(lwd_shape d)))=false;
  lws_private_unique : tensor_unique(lwd_private d)=true;
  lws_cache_private : tensor_disjoint[ncs_root_cache(lwd_shape d);ncs_child_cache(lwd_shape d);
    ncs_component_helper(lwd_shape d)](tensor_word_driver_ports(lwd_shape d)live)=true;
  lws_controls_private : tensor_disjoint(lwd_controls d)(tensor_word_driver_scan_live(lwd_shape d)live)=true;
  lws_coordinates_unique : tensor_unique(ncs_coordinates(lwd_shape d))=true;
  lws_stable_members : tensor_subset[ncs_component_helper(lwd_shape d);ncs_root_cache(lwd_shape d);
    ncs_child_cache(lwd_shape d);lwd_pointer d;ncs_pointer(lwd_shape d)](lwd_stable live d)=true;
  lws_index_scope : tensor_subset(expression_temps(lwd_index d))
    (ncs_iterator(lwd_shape d)::ncs_column(lwd_shape d)::ncs_row(lwd_shape d)::lwd_stable live d)=true
}.

Definition check_loaded_word_static live d : option(loaded_word_static live d).
Proof.
  destruct(statement_eq(ncs_leaf(lwd_shape d))(direct_word_store(lwd_pointer d)(lwd_index d)(lwd_rhs d)))as [LEAF|]; [|exact None].
  destruct(word_arithmetic_check(lwd_index d))eqn:WORD; [|exact None].
  destruct(Z_le_dec 0(ncs_upper(lwd_shape d)))as [NONNEG|]; [|exact None].
  destruct(Z_le_dec Int.min_signed(ncs_upper(lwd_shape d)))as [UL|]; [|exact None].
  destruct(Z_le_dec(ncs_upper(lwd_shape d))Int.max_signed)as [UH|]; [|exact None].
  destruct(Z_le_dec Int.min_signed(lwd_root_cap d))as [RL|]; [|exact None].
  destruct(Z_le_dec(lwd_root_cap d)Int.max_signed)as [RH|]; [|exact None].
  destruct(Z_le_dec Int.min_signed(lwd_child_cap d))as [CL|]; [|exact None].
  destruct(Z_le_dec(lwd_child_cap d)Int.max_signed)as [CH|]; [|exact None].
  destruct(check_plan_frameable(ncs_original(lwd_shape d)))eqn:ORIGINAL; [|exact None].
  destruct(check_plan_frameable(tensor_word_driver_cached(lwd_shape d)))eqn:CACHED; [|exact None].
  destruct(check_plan_frameable(tensor_word_driver_canonical(lwd_shape d)))eqn:CANONICAL; [|exact None].
  destruct(tensor_subset(statement_temps(tensor_word_driver_cached(lwd_shape d)))
    (tensor_word_driver_scan_live(lwd_shape d)live))eqn:SCOPE; [|exact None].
  destruct(tensor_member(ncs_component_helper(lwd_shape d))(statement_temps(tensor_word_driver_cached(lwd_shape d))))eqn:HELPER;
    [exact None|].
  destruct(tensor_unique(lwd_private d))eqn:UNIQUE; [|exact None].
  destruct(tensor_disjoint[ncs_root_cache(lwd_shape d);ncs_child_cache(lwd_shape d);ncs_component_helper(lwd_shape d)]
    (tensor_word_driver_ports(lwd_shape d)live))eqn:PRIVATE; [|exact None].
  destruct(tensor_disjoint(lwd_controls d)(tensor_word_driver_scan_live(lwd_shape d)live))eqn:CONTROLS; [|exact None].
  destruct(tensor_unique(ncs_coordinates(lwd_shape d)))eqn:COORDINATES; [|exact None].
  destruct(tensor_subset[ncs_component_helper(lwd_shape d);ncs_root_cache(lwd_shape d);ncs_child_cache(lwd_shape d);
    lwd_pointer d;ncs_pointer(lwd_shape d)](lwd_stable live d))eqn:STABLE; [|exact None].
  destruct(tensor_subset(expression_temps(lwd_index d))
    (ncs_iterator(lwd_shape d)::ncs_column(lwd_shape d)::ncs_row(lwd_shape d)::lwd_stable live d))eqn:INDEX; [|exact None].
  exact(Some(@LoadedWordStatic live d LEAF WORD NONNEG(conj UL UH)(conj RL RH)(conj CL CH)
    ORIGINAL CACHED CANONICAL SCOPE HELPER UNIQUE PRIVATE CONTROLS COORDINATES STABLE INDEX)).
Defined.

Lemma lwd_stable_scope live d : incl(lwd_stable live d)(tensor_word_driver_scan_live(lwd_shape d)live).
Proof. intros id MEMBER; apply filter_In in MEMBER; exact(proj1 MEMBER). Qed.
Lemma lwd_stable_coordinate_private live d id : In id(ncs_coordinates(lwd_shape d)) -> ~In id(lwd_stable live d).
Proof.
  intros COORD MEMBER; apply filter_In in MEMBER as [_ CHECK]; apply tensor_member_true in COORD.
  rewrite COORD in CHECK; discriminate.
Qed.
Lemma lwd_rename_stable live d id : In id(lwd_stable live d) -> lwd_rename d id=id.
Proof.
  intro MEMBER; unfold lwd_rename.
  destruct(peq id(ncs_iterator(lwd_shape d)))as [SAME|];
    [subst id; exfalso; eapply (@lwd_stable_coordinate_private live d (ncs_iterator(lwd_shape d))); [cbn; auto|exact MEMBER]|].
  destruct(peq id(ncs_column(lwd_shape d)))as [SAME|];
    [subst id; exfalso; eapply (@lwd_stable_coordinate_private live d (ncs_column(lwd_shape d))); [cbn; auto|exact MEMBER]|].
  destruct(peq id(ncs_row(lwd_shape d)))as [SAME|];
    [subst id; exfalso; eapply (@lwd_stable_coordinate_private live d (ncs_row(lwd_shape d))); [cbn; auto|exact MEMBER]|reflexivity].
Qed.
Lemma lwd_member_false id names : tensor_member id names=false -> ~In id names.
Proof. intros FALSE MEMBER; apply tensor_member_true in MEMBER; congruence. Qed.
Lemma lwd_integer_names_sound id pool : In id(lwd_integer_names pool) -> In(id,type_int32s)pool.
Proof.
  unfold lwd_integer_names; intro MEMBER; apply in_map_iff in MEMBER as [[actual ty][SAME MEMBER]].
  cbn in SAME; subst actual; apply filter_In in MEMBER as [MEMBER CHECK].
  cbn in CHECK; destruct(type_eq ty type_int32s); [subst; exact MEMBER|discriminate].
Qed.

Record loaded_word_site source live pool d := LoadedWordSite {
  lws_source : source=ncs_original(lwd_shape d);
  lws_static : loaded_word_static live d;
  lws_allocated : tensor_subset(lwd_private d)(lwd_integer_names pool)=true;
  lws_package : tensor_region_package(tensor_word_driver_canonical(lwd_shape d));
  lws_flag_private : ~In(lwd_flag d)(statement_temps(tensor_word_driver_canonical(lwd_shape d))++live++
    check_plan_reads(tree_check_plan(tensor_region_guard lws_package)))
}.
Definition check_loaded_word_site source live pool d (description:tensor_region_description) : option(loaded_word_site source live pool d).
Proof.
  destruct(statement_eq source(ncs_original(lwd_shape d)))as [SOURCE|]; [|exact None].
  destruct(check_loaded_word_static live d)as [STATIC|]; [|exact None].
  destruct(tensor_subset(lwd_private d)(lwd_integer_names pool))eqn:ALLOCATED; [|exact None].
  destruct(check_tensor_region_description(tensor_word_driver_canonical(lwd_shape d))description)as [package|]; [|exact None].
  destruct(in_dec peq(lwd_flag d)(statement_temps(tensor_word_driver_canonical(lwd_shape d))++live++
    check_plan_reads(tree_check_plan(tensor_region_guard package))))as [|FLAG]; [exact None|].
  exact(Some(@LoadedWordSite source live pool d SOURCE STATIC ALLOCATED package FLAG)).
Defined.

Theorem loaded_word_site_private_allocated source live pool d(site:loaded_word_site source live pool d) :
  forall id,In id(lwd_private d) -> In(id,type_int32s)pool.
Proof.
  intros id MEMBER; apply lwd_integer_names_sound.
  eapply tensor_subset_sound; [exact(lws_allocated site)|exact MEMBER].
Qed.

Theorem loaded_word_site_generated_contract source live pool d(site:loaded_word_site source live pool d) pairs proposal code :
  mayReturn(check_tensor_generated_region(lws_package site)live pairs proposal)(Some code) ->
  PrivateRegion.projected_region_contract live source
    (tensor_word_driver_generated_target(lws_package site)(lwd_code d)(lwd_flag d)code).
Proof.
  intro CHECK; pose(package:=lws_package site).
  change(PrivateRegion.projected_region_contract live source
    (tensor_word_driver_generated_target package(lwd_code d)(lwd_flag d)code)).
  rewrite(lws_source site).
  pose proof(lws_static site)as STATIC.
  pose proof(@tensor_unique_sound _ (lws_private_unique STATIC))as NAMES.
  pose proof(@tensor_unique_sound _ (lws_coordinates_unique STATIC))as COORDS.
  pose proof(@tensor_disjoint_sound _ _ (lws_cache_private STATIC))as CACHES.
  pose proof(@tensor_disjoint_sound _ _ (lws_controls_private STATIC))as CONTROLS.
  pose proof(@tensor_subset_sound _ _ (lws_stable_members STATIC))as STABLE.
  unfold lwd_private,lwd_controls in NAMES,CONTROLS; unfold ncs_coordinates in COORDS.
  repeat match goal with H:NoDup(_::_) |- _=>inversion H; clear H; subst end.
  cbn [In] in H1,H3,H4,H6,H7,H8,H9,H10,H11,H12,H13,H14.
  assert(RC:~In(lwd_row_cursor d)(tensor_word_driver_scan_live(lwd_shape d)live))by(apply CONTROLS; cbn; auto 10).
  assert(RL:~In(lwd_row_limit d)(tensor_word_driver_scan_live(lwd_shape d)live))by(apply CONTROLS; cbn; auto 10).
  assert(CC:~In(lwd_column_cursor d)(tensor_word_driver_scan_live(lwd_shape d)live))by(apply CONTROLS; cbn; auto 10).
  assert(CL:~In(lwd_column_limit d)(tensor_word_driver_scan_live(lwd_shape d)live))by(apply CONTROLS; cbn; auto 10).
  assert(KC:~In(lwd_component_cursor d)(tensor_word_driver_scan_live(lwd_shape d)live))by(apply CONTROLS; cbn; auto 10).
  assert(KL:~In(lwd_component_limit d)(tensor_word_driver_scan_live(lwd_shape d)live))by(apply CONTROLS; cbn; auto 10).
  assert(FL:~In(lwd_flag d)(tensor_word_driver_scan_live(lwd_shape d)live))by(apply CONTROLS; cbn; auto 10).
  eapply tensor_word_driver_generated_contract with(rhs:=lwd_rhs d)(stable:=lwd_stable live d).
  all: try solve[exact(lws_leaf STATIC)|apply word_arithmetic_check_sound; exact(lws_word STATIC)|
    exact(lws_nonnegative STATIC)|exact(lws_upper STATIC)|exact(lws_root_cap STATIC)|exact(lws_child_cap STATIC)|
    exact(lws_original_frame STATIC)|exact(lws_cached_frame STATIC)|exact(lws_canonical_frame STATIC)|
    exact(lws_flag_private site)|exact CHECK|apply lwd_stable_scope|apply lwd_rename_stable].
  all: try solve[apply tensor_subset_sound; exact(lws_cached_scope STATIC)|
    apply tensor_subset_sound; exact(lws_index_scope STATIC)|apply lwd_member_false; exact(lws_helper_cached STATIC)].
  all: try solve[eapply CACHES; cbn; auto 10|apply STABLE; cbn; auto 10|
    eapply lwd_stable_coordinate_private; cbn; auto].
  all: try solve[unfold incl; intros id MEMBER; eapply tensor_subset_sound;
    [exact(lws_cached_scope STATIC)|exact MEMBER]].
  all: try solve[unfold incl; intros id MEMBER; eapply tensor_subset_sound;
    [exact(lws_index_scope STATIC)|exact MEMBER]].
  all: try solve[intro SAME; apply(@lwd_stable_coordinate_private live d(ncs_column(lwd_shape d)));
    [cbn; auto|rewrite SAME; apply STABLE; cbn; auto 10]].
  all: try solve[unfold lwd_rename; repeat destruct(peq _ _); intuition congruence].
  all: try solve[cbn [In]; intuition congruence].
Qed.

Definition loaded_word_proposer := list ident -> list(ident*type) -> statement -> option loaded_word_description.
Definition check_loaded_word_generated_region live pool(describe:loaded_word_proposer)
    (tensor_describe:tensor_description_proposer)(propose:tensor_generated_proposer)source : Base.imp(option statement) :=
  match describe live pool source with
  | Some d=>match tensor_describe(tensor_word_driver_canonical(lwd_shape d))with
    | Some description=>match check_loaded_word_site source live pool d description,
      private_counter_pairs(lwd_candidate_pool pool d)with
      | Some site,Some pairs=>match propose[tensor_source_instruction(tensor_operation(lws_package site))]with
        | Some proposal=>BIND code <- check_tensor_generated_region(lws_package site)live pairs proposal -;
          pure(match code with Some code=>Some(tensor_word_driver_generated_target(lws_package site)
            (lwd_code d)(lwd_flag d)code)|None=>None end)
        | None=>pure None end
      | _,_=>pure None end
    | None=>pure None end
  | None=>pure None end.

Theorem check_loaded_word_generated_region_sound live pool describe tensor_describe propose source target :
  mayReturn(check_loaded_word_generated_region live pool describe tensor_describe propose source)(Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold check_loaded_word_generated_region.
  destruct(describe live pool source)as [d|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(tensor_describe(tensor_word_driver_canonical(lwd_shape d)))as [description|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(check_loaded_word_site source live pool d description)as [site|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(private_counter_pairs(lwd_candidate_pool pool d))as [pairs|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(propose[tensor_source_instruction(tensor_operation(lws_package site))])as [proposal|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN generated CHECK; apply mayReturn_pure in RUN.
  destruct generated as [code|]; [|discriminate]; inversion RUN; subst target.
  eapply loaded_word_site_generated_contract; exact CHECK.
Qed.

Fixpoint checked_loaded_word_generated_regions live pool describe tensor_describe propose sources := match sources with
| []=>pure []
| source::rest=>BIND target <- check_loaded_word_generated_region live pool describe tensor_describe propose source -;
  BIND table <- checked_loaded_word_generated_regions live pool describe tensor_describe propose rest -;
  pure(match target with Some target=>(source,target)::table|None=>table end)end.
Theorem checked_loaded_word_generated_regions_sound live pool describe tensor_describe propose sources table :
  mayReturn(checked_loaded_word_generated_regions live pool describe tensor_describe propose sources)table ->
  Forall(fun pair=>PrivateRegion.projected_region_contract live(fst pair)(snd pair))table.
Proof.
  revert table; induction sources as [|source sources IH]; intros table RUN; cbn in RUN.
  - apply mayReturn_pure in RUN; subst; constructor.
  - bind_imp_destruct RUN target CHECK; bind_imp_destruct RUN rest REST; apply mayReturn_pure in RUN.
    destruct target; subst; [constructor; [eapply check_loaded_word_generated_region_sound; exact CHECK|]|]; apply IH; exact REST.
Qed.

Print Assumptions check_loaded_word_static.
Print Assumptions lwd_stable_scope.
Print Assumptions lwd_stable_coordinate_private.
Print Assumptions lwd_rename_stable.
Print Assumptions lwd_integer_names_sound.
Print Assumptions check_loaded_word_site.
Print Assumptions loaded_word_site_private_allocated.
Print Assumptions loaded_word_site_generated_contract.
Print Assumptions check_loaded_word_generated_region_sound.
Print Assumptions checked_loaded_word_generated_regions_sound.
