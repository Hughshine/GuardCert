(** Frontend administrative skips are handled by a proved language service.
    The candidate factory still checks the actual normalized source, and the
    installation host still checks progress on the original frontend AST. *)
From Stdlib Require Import List.
From compcert.common Require Import AST Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightGuard ClightPrivateRegion ClightTempFootprint.
From GuardInterface Require Import ClightAdministrative ClightLoopAdministrative ClightWordNestedStoreAffine.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

Lemma join_statements_temps first second :
  statement_temps (join_statements first second)=statement_temps first++statement_temps second.
Proof.
  destruct first; cbn [join_statements statement_temps]; try reflexivity;
    destruct second; cbn [statement_temps]; try reflexivity; apply eq_sym,app_nil_r.
Qed.
Theorem trim_loop_skips_temps source : statement_temps (trim_loop_skips source)=statement_temps source.
Proof.
  revert source; fix IH 1; intro source; destruct source; cbn [trim_loop_skips statement_temps];
    try reflexivity.
  - rewrite join_statements_temps,IH,IH; reflexivity.
  - rewrite IH,IH; reflexivity.
  - destruct source1; cbn [trim_loop_skips statement_temps]; try reflexivity;
      rewrite IH; reflexivity.
Qed.
Theorem word_nested_store_frontend_contract public source target :
  PrivateRegion.projected_region_contract public (trim_loop_skips source) target ->
  PrivateRegion.projected_region_contract public source target.
Proof.
  intros CONTRACT temps p locals le current memory after final SCOPE AGREE SOURCE fn continuation.
  assert (NORMALIZED_SCOPE : statement_scope public (trim_loop_skips source)).
  { intros id MEMBER; apply SCOPE; rewrite <-trim_loop_skips_temps; exact MEMBER. }
  apply (proj2 (trim_loop_skips_equivalent (adapter_entry temps) source
    (globalenv p) locals le memory E0 after final Out_normal)) in SOURCE.
  exact (CONTRACT temps p locals le current memory after final NORMALIZED_SCOPE AGREE SOURCE fn continuation).
Qed.
Definition check_word_nested_store_frontend_affine_region public typed_pool describe describe_cached propose source :=
  check_word_nested_store_affine_region public typed_pool describe describe_cached propose (trim_loop_skips source).
Theorem check_word_nested_store_frontend_affine_region_contract public typed_pool describe describe_cached propose source target :
  mayReturn (check_word_nested_store_frontend_affine_region public typed_pool describe describe_cached propose source)
    (Some target) -> PrivateRegion.projected_region_contract public source target.
Proof.
  intro CHECK; apply word_nested_store_frontend_contract.
  eapply check_word_nested_store_affine_region_contract; exact CHECK.
Qed.
Fixpoint checked_word_nested_store_frontend_affine_regions public typed_pool describe describe_cached propose sources :=
  match sources with
  | []=>pure []
  | source::rest=>
    BIND target <- check_word_nested_store_frontend_affine_region public typed_pool describe describe_cached propose source -;
    BIND table <- checked_word_nested_store_frontend_affine_regions public typed_pool describe describe_cached propose rest -;
    pure (match target with Some target=>(source,target)::table|None=>table end)
  end.
Theorem checked_word_nested_store_frontend_affine_regions_sound public typed_pool describe describe_cached propose sources table :
  mayReturn (checked_word_nested_store_frontend_affine_regions public typed_pool describe describe_cached propose sources) table ->
  Forall (fun pair=>PrivateRegion.projected_region_contract public (fst pair) (snd pair)) table.
Proof.
  revert table; induction sources as [|source sources IH]; intros table RUN; cbn in RUN.
  - apply mayReturn_pure in RUN; subst; constructor.
  - bind_imp_destruct RUN target CHECK; bind_imp_destruct RUN rest REST; apply mayReturn_pure in RUN.
    destruct target; subst;
      [constructor; [eapply check_word_nested_store_frontend_affine_region_contract; exact CHECK|]|]; apply IH; exact REST.
Qed.
Print Assumptions join_statements_temps.
Print Assumptions trim_loop_skips_temps.
Print Assumptions word_nested_store_frontend_contract.
Print Assumptions check_word_nested_store_frontend_affine_region_contract.
Print Assumptions checked_word_nested_store_frontend_affine_regions_sound.
