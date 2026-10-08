From Stdlib Require Import List.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight Ctypes.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion.
Import ListNotations CoreAlarmed PrivateRegion.
Set Implicit Arguments.

(** A Clight library interface above the semantic kernel. A verified domain
    implementation registers this record once; ordinary source/candidate
    proposals remain data inputs to that implementation. Installation still
    belongs to the language host and checks each actual rewrite site. *)
Record certified_region_builder := {
  build_certified_region : list ident -> list (ident * type) -> statement ->
    Base.imp (option statement);
  build_certified_region_sound : forall public pool source target,
    mayReturn (build_certified_region public pool source) (Some target) ->
    projected_region_contract public source target
}.

(** Static refusal of one implementation permits another. Runtime guard
    refusal is already handled inside the returned certified statement. *)
Definition build_region_or_else first second public pool source :=
  BIND target <- build_certified_region first public pool source -;
  match target with
  | Some code => pure (Some code)
  | None => build_certified_region second public pool source
  end.

Theorem build_region_or_else_sound first second public pool source target :
  mayReturn (build_region_or_else first second public pool source) (Some target) ->
  projected_region_contract public source target.
Proof.
  unfold build_region_or_else; intro RUN; bind_imp_destruct RUN selected FIRST.
  destruct selected as [code|].
  - apply mayReturn_pure in RUN; inversion RUN; subst code.
    eapply build_certified_region_sound; exact FIRST.
  - eapply build_certified_region_sound; exact RUN.
Qed.

Definition certified_region_or_else first second : certified_region_builder :=
  {| build_certified_region := build_region_or_else first second;
     build_certified_region_sound := @build_region_or_else_sound first second |}.

Fixpoint checked_certified_regions builder public pool sources :=
  match sources with
  | [] => pure []
  | source :: rest =>
    BIND target <- build_certified_region builder public pool source -;
    BIND table <- checked_certified_regions builder public pool rest -;
    pure (match target with Some code => (source,code)::table | None => table end)
  end.

Theorem checked_certified_regions_sound builder public pool sources table :
  mayReturn (checked_certified_regions builder public pool sources) table ->
  Forall (fun pair => projected_region_contract public (fst pair) (snd pair)) table.
Proof.
  revert table; induction sources as [|source sources IH]; intros table RUN; cbn in RUN.
  - apply mayReturn_pure in RUN; subst; constructor.
  - bind_imp_destruct RUN target CHECK; bind_imp_destruct RUN rest REST.
    apply mayReturn_pure in RUN; destruct target; subst.
    + constructor; [eapply build_certified_region_sound; exact CHECK|apply IH; exact REST].
    + apply IH; exact REST.
Qed.

Print Assumptions build_region_or_else_sound.
Print Assumptions checked_certified_regions_sound.
