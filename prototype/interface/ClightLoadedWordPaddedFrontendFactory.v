From Stdlib Require Import List Bool.
From compcert.common Require Import AST Events.
From compcert.cfrontend Require Import Clight ClightBigstep Ctypes.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightGuard ClightSyntaxEquality ClightPrivateRegion ClightTempFootprint
  ClightRegionProgress ClightRectangularLoops.
From GuardInterface Require Import ClightNestedConstantSite ClightNestedFrontendRegion
  ClightLoadedWordFrontendFactory ClightTensorLoadedWordFactory ClightTensorGeneratedFactory ClightTensorRegionCompiler
  ClightExecutionCongruence ClightStrictLoopProgress ClightSignedExpressionProgress
  ClightNestedExpressionCapture ClightConstantBoundModel.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** The real C frontend also inserts a skip before the leaf assignment. This
    adapter checks that exact syntax and proves its source equivalence. *)
Definition lwd_padded_shape shape := NestedConstantShape(ncs_row shape)(ncs_column shape)(ncs_iterator shape)
  (ncs_root_cache shape)(ncs_child_cache shape)(ncs_child_helper shape)(ncs_component_helper shape)
  (ncs_upper shape)(Ssequence Sskip(ncs_leaf shape))(ncs_pointer shape)(ncs_index shape)(ncs_delta shape)(ncs_child_delta shape).
Lemma lwd_padded_original_equivalent shape : statement_execution_equivalent(ncs_original(lwd_padded_shape shape))(ncs_original shape).
Proof.
  unfold ncs_original,nested_expression_source,nested_expression_body,constant_body_source,lwd_padded_shape;
    cbn [ncs_row ncs_column ncs_iterator ncs_pointer ncs_index ncs_delta ncs_child_delta ncs_upper ncs_leaf].
  apply statement_strict_body_equivalent,statement_sequence_equivalent;
    [unfold statement_execution_equivalent; intros; reflexivity|].
  apply statement_strict_body_equivalent,statement_sequence_equivalent;
    [unfold statement_execution_equivalent; intros; reflexivity|].
  apply statement_strict_body_equivalent,statement_skip_prefix_equivalent.
Qed.
Lemma lwd_padded_original_temps shape : statement_temps(ncs_original(lwd_padded_shape shape))=statement_temps(ncs_original shape).
Proof.
  unfold ncs_original,nested_expression_source,nested_expression_body,constant_body_source,lwd_padded_shape;
    cbn [ncs_row ncs_column ncs_iterator ncs_pointer ncs_index ncs_delta ncs_child_delta ncs_upper ncs_leaf
      strict_frontend_loop signed_expression_test statement_temps expression_temps]; reflexivity.
Qed.
Theorem loaded_word_padded_frontend_contract indexed shape live target :
  PrivateRegion.projected_region_contract live(ncs_original shape)target ->
  PrivateRegion.projected_region_contract live(ncs_frontend_source indexed(lwd_padded_shape shape))target.
Proof.
  intros CONTRACT temps p locals le current memory after final SCOPE AGREE SOURCE fn continuation.
  unfold statement_scope in SCOPE; rewrite ncs_frontend_temps,lwd_padded_original_temps in SCOPE.
  apply(proj1(@ncs_frontend_execution_equivalent indexed(adapter_entry temps)(globalenv p)locals le memory
    (lwd_padded_shape shape)E0 after final Out_normal))in SOURCE.
  apply(proj1(lwd_padded_original_equivalent shape(adapter_entry temps)(globalenv p)locals le memory
    E0 after final Out_normal))in SOURCE.
  exact(CONTRACT temps p locals le current memory after final SCOPE AGREE SOURCE fn continuation).
Qed.

Definition check_loaded_word_padded_frontend_region live pool(describe:loaded_word_frontend_proposer)
    (tensor_describe:tensor_description_proposer)(propose:tensor_generated_proposer)source :=
  match describe live pool source with
  | Some(indexed,d)=>if statement_eq source(ncs_frontend_source indexed(lwd_padded_shape(lwd_shape d)))then
      check_loaded_word_generated_region live pool(fun _ _ _=>Some d)tensor_describe propose(ncs_original(lwd_shape d))
    else check_loaded_word_frontend_region live pool(fun _ _ _=>Some(indexed,d))tensor_describe propose source
  | None=>pure None end.
Theorem check_loaded_word_padded_frontend_region_sound live pool describe tensor_describe propose source target :
  mayReturn(check_loaded_word_padded_frontend_region live pool describe tensor_describe propose source)(Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold check_loaded_word_padded_frontend_region.
  destruct(describe live pool source)as [[indexed d]|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(statement_eq source(ncs_frontend_source indexed(lwd_padded_shape(lwd_shape d))))as [SOURCE|].
  - intro CHECK; subst source; apply loaded_word_padded_frontend_contract.
    eapply check_loaded_word_generated_region_sound; exact CHECK.
  - apply check_loaded_word_frontend_region_sound.
Qed.
Fixpoint checked_loaded_word_padded_frontend_regions live pool describe tensor_describe propose sources := match sources with
| []=>pure []
| source::rest=>BIND target <- check_loaded_word_padded_frontend_region live pool describe tensor_describe propose source -;
  BIND table <- checked_loaded_word_padded_frontend_regions live pool describe tensor_describe propose rest -;
  pure(match target with Some target=>(source,target)::table|None=>table end)end.
Theorem checked_loaded_word_padded_frontend_regions_sound live pool describe tensor_describe propose sources table :
  mayReturn(checked_loaded_word_padded_frontend_regions live pool describe tensor_describe propose sources)table ->
  Forall(fun pair=>PrivateRegion.projected_region_contract live(fst pair)(snd pair))table.
Proof.
  revert table; induction sources as [|source sources IH]; intros table RUN; cbn in RUN.
  - apply mayReturn_pure in RUN; subst; constructor.
  - bind_imp_destruct RUN target CHECK; bind_imp_destruct RUN rest REST; apply mayReturn_pure in RUN.
    destruct target; subst; [constructor; [eapply check_loaded_word_padded_frontend_region_sound; exact CHECK|]|]; apply IH; exact REST.
Qed.
Print Assumptions lwd_padded_original_equivalent.
Print Assumptions lwd_padded_original_temps.
Print Assumptions loaded_word_padded_frontend_contract.
Print Assumptions check_loaded_word_padded_frontend_region_sound.
Print Assumptions checked_loaded_word_padded_frontend_regions_sound.
