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
From GuardInterface Require Import ClightTensorLoadedWordFactory ClightTensorZeroRmwPreparation
  ClightTensorZeroRmwDriver ClightTensorZeroRmwScanBridge ClightTensorPreparedGenerated.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** An optimizer supplies only a source description, a scalar identifier,
    a canonical tensor model, and a generated schedule candidate. All proof
    fields below are checked or produced internally by the source factory. *)
Definition zero_loaded_word_proposer := list ident -> list(ident*type) -> statement ->
  option(loaded_word_description*ident).

Theorem zero_loaded_word_site_generated_contract source live pool d alpha
  (site:loaded_word_site source live pool d)(static:tensor_zero_rmw_static live d alpha)
  pairs proposal code :
  mayReturn(check_tensor_generated_region(lws_package site)live pairs proposal)(Some code) ->
  PrivateRegion.projected_region_contract live source
    (prepared_tensor_generated_target source(lws_package site)(lwd_zero_code d alpha)(lwd_flag d)code).
Proof.
  intro CHECK; pose(package:=lws_package site).
  change(PrivateRegion.projected_region_contract live source
    (prepared_tensor_generated_target source package(lwd_zero_code d alpha)(lwd_flag d)code)).
  rewrite(lws_source site).
  eapply prepared_tensor_generated_contract with
    (preparation:=lwd_zero_preparation_certificate static).
  - exact(lws_flag_private site).
  - exact CHECK.
Qed.

Definition check_zero_loaded_word_generated_region live pool(describe:zero_loaded_word_proposer)
    (tensor_describe:tensor_description_proposer)(propose:tensor_generated_proposer)source : Base.imp(option statement) :=
  match describe live pool source with
  | Some(d,alpha)=>match check_tensor_zero_rmw_static live d alpha with
    | Some static=>match tensor_describe(tensor_word_driver_canonical(lwd_shape d))with
    | Some description=>match check_loaded_word_site source live pool d description,
      private_counter_pairs(lwd_candidate_pool pool d)with
      | Some site,Some pairs=>match propose[tensor_source_instruction(tensor_operation(lws_package site))]with
        | Some proposal=>BIND code <- check_tensor_generated_region(lws_package site)live pairs proposal -;
          pure(match code with Some code=>Some(prepared_tensor_generated_target source(lws_package site)
            (lwd_zero_code d alpha)(lwd_flag d)code)|None=>None end)
        | None=>pure None end
      | _,_=>pure None end
    | None=>pure None end
    | None=>pure None end
  | None=>pure None end.

Theorem check_zero_loaded_word_generated_region_sound live pool describe tensor_describe propose source target :
  mayReturn(check_zero_loaded_word_generated_region live pool describe tensor_describe propose source)(Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold check_zero_loaded_word_generated_region.
  destruct(describe live pool source)as [[d alpha]|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(check_tensor_zero_rmw_static live d alpha)as [static|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
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
  eapply zero_loaded_word_site_generated_contract; [exact static|exact CHECK].
Qed.

Fixpoint checked_zero_loaded_word_generated_regions live pool describe tensor_describe propose sources := match sources with
| []=>pure []
| source::rest=>BIND target <- check_zero_loaded_word_generated_region live pool describe tensor_describe propose source -;
  BIND table <- checked_zero_loaded_word_generated_regions live pool describe tensor_describe propose rest -;
  pure(match target with Some target=>(source,target)::table|None=>table end)end.
Theorem checked_zero_loaded_word_generated_regions_sound live pool describe tensor_describe propose sources table :
  mayReturn(checked_zero_loaded_word_generated_regions live pool describe tensor_describe propose sources)table ->
  Forall(fun pair=>PrivateRegion.projected_region_contract live(fst pair)(snd pair))table.
Proof.
  revert table; induction sources as [|source sources IH]; intros table RUN; cbn in RUN.
  - apply mayReturn_pure in RUN; subst; constructor.
  - bind_imp_destruct RUN target CHECK; bind_imp_destruct RUN rest REST; apply mayReturn_pure in RUN.
    destruct target; subst; [constructor; [eapply check_zero_loaded_word_generated_region_sound; exact CHECK|]|]; apply IH; exact REST.
Qed.

Print Assumptions zero_loaded_word_site_generated_contract.
Print Assumptions check_zero_loaded_word_generated_region_sound.
Print Assumptions checked_zero_loaded_word_generated_regions_sound.
