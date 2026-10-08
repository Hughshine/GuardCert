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
From GuardInterface Require Import ClightLoadedWordPaddedFrontendFactory ClightTensorZeroRmwFactory.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

Definition zero_loaded_word_frontend_proposer := list ident -> list(ident*type) -> statement ->
  option(bool*(loaded_word_description*ident)).
Definition check_zero_loaded_word_frontend_region live pool(describe:zero_loaded_word_frontend_proposer)
    (tensor_describe:tensor_description_proposer)(propose:tensor_generated_proposer)source :=
  match describe live pool source with
  | Some(indexed,(d,alpha))=>
    if statement_eq source(ncs_frontend_source indexed(lwd_padded_shape(lwd_shape d)))then
      check_zero_loaded_word_generated_region live pool(fun _ _ _=>Some(d,alpha))tensor_describe propose(ncs_original(lwd_shape d))
    else if statement_eq source(ncs_frontend_source indexed(lwd_shape d))then
      check_zero_loaded_word_generated_region live pool(fun _ _ _=>Some(d,alpha))tensor_describe propose(ncs_original(lwd_shape d))
    else pure None
  | None=>pure None end.
Theorem check_zero_loaded_word_frontend_region_sound live pool describe tensor_describe propose source target :
  mayReturn(check_zero_loaded_word_frontend_region live pool describe tensor_describe propose source)(Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold check_zero_loaded_word_frontend_region.
  destruct(describe live pool source)as [[indexed [d alpha]]|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(statement_eq source(ncs_frontend_source indexed(lwd_padded_shape(lwd_shape d))))as [SOURCE|].
  - intro CHECK; subst source; apply loaded_word_padded_frontend_contract.
    eapply check_zero_loaded_word_generated_region_sound; exact CHECK.
  - destruct(statement_eq source(ncs_frontend_source indexed(lwd_shape d)))as [SOURCE|];
      [|intro RUN; apply mayReturn_pure in RUN; discriminate].
    intro CHECK; subst source; apply loaded_word_frontend_contract.
    eapply check_zero_loaded_word_generated_region_sound; exact CHECK.
Qed.
Fixpoint checked_zero_loaded_word_frontend_regions live pool describe tensor_describe propose sources := match sources with
| []=>pure []
| source::rest=>BIND target <- check_zero_loaded_word_frontend_region live pool describe tensor_describe propose source -;
  BIND table <- checked_zero_loaded_word_frontend_regions live pool describe tensor_describe propose rest -;
  pure(match target with Some target=>(source,target)::table|None=>table end)end.
Theorem checked_zero_loaded_word_frontend_regions_sound live pool describe tensor_describe propose sources table :
  mayReturn(checked_zero_loaded_word_frontend_regions live pool describe tensor_describe propose sources)table ->
  Forall(fun pair=>PrivateRegion.projected_region_contract live(fst pair)(snd pair))table.
Proof.
  revert table; induction sources as [|source sources IH]; intros table RUN; cbn in RUN.
  - apply mayReturn_pure in RUN; subst; constructor.
  - bind_imp_destruct RUN target CHECK; bind_imp_destruct RUN rest REST; apply mayReturn_pure in RUN.
    destruct target; subst; [constructor; [eapply check_zero_loaded_word_frontend_region_sound; exact CHECK|]|]; apply IH; exact REST.
Qed.

Print Assumptions check_zero_loaded_word_frontend_region_sound.
Print Assumptions checked_zero_loaded_word_frontend_regions_sound.
