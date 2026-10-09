From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Coqlib.
From compcert.common Require Import AST Globalenvs.
From compcert.cfrontend Require Import Ctypes Clight.
From Guard Require Import ClightTempFootprint ClightTempScope ClightRegionProgress ClightScopedPrivateRegion.
Import ListNotations.
Set Implicit Arguments.

(** Check only the environment and public scope used by a proved source
    profile. Function bodies and global initial values are not compared. *)
Definition program_environment_check (reference p : Clight.program) :=
  if list_eq_dec composite_def_eq (prog_types reference) (prog_types p) then
    PTree.beq Pos.eqb (Genv.genv_symb (globalenv reference)) (Genv.genv_symb (globalenv p)) else false.
Lemma program_environment_check_sound reference p : program_environment_check reference p=true ->
  preserving_globals (globalenv reference) (globalenv p).
Proof.
  unfold program_environment_check; destruct (list_eq_dec composite_def_eq (prog_types reference) (prog_types p))
    as [TYPES|DIFFERENT]; [|discriminate].
  intro SYMBOLS; split.
  - cbn [globalenv genv_cenv]; pose proof (prog_comp_env_eq reference) as FIRST;
      pose proof (prog_comp_env_eq p) as SECOND; rewrite TYPES in FIRST; congruence.
  - intro identifier; unfold Genv.find_symbol; rewrite PTree.beq_correct in SYMBOLS.
    specialize (SYMBOLS identifier).
    change (match (Genv.genv_symb (globalenv reference)) ! identifier,
      (Genv.genv_symb (globalenv p)) ! identifier with
      | Some first,Some second => Pos.eqb first second=true
      | None,None => True | _,_ => False end) in SYMBOLS.
    remember ((Genv.genv_symb (globalenv reference)) ! identifier) as REFLOOKUP in *.
    remember ((Genv.genv_symb (globalenv p)) ! identifier) as ACTUALLOOKUP in *.
    destruct REFLOOKUP,ACTUALLOOKUP; cbn in SYMBOLS; try contradiction; auto.
    f_equal; symmetry; apply Pos.eqb_eq; exact SYMBOLS.
Qed.
Definition program_temp_scope_check live p :=
  forallb (fun identifier => existsb (Pos.eqb identifier) live) (program_temps p).
Lemma program_temp_scope_check_sound live p : program_temp_scope_check live p=true -> program_scope live p.
Proof.
  intro CHECK; intros name fd MEMBER identifier USED.
  pose proof (@program_scope_computed p name fd MEMBER identifier USED) as IN.
  unfold program_temp_scope_check in CHECK; apply forallb_forall with (x:=identifier) in CHECK; [|exact IN].
  apply existsb_exists in CHECK as [found [FOUND SAME]]; apply Pos.eqb_eq in SAME; subst found; exact FOUND.
Qed.
Lemma preserving_globals_compose first second third : preserving_globals first second ->
  preserving_globals second third -> preserving_globals first third.
Proof. intros [C1 S1] [C2 S2]; split; [congruence|intro identifier; rewrite S2,S1; reflexivity]. Qed.
Lemma scoped_contract_reference_transport live reference current globals source target :
  preserving_globals reference current ->
  ScopedPrivateRegion.projected_region_contract live reference globals source target ->
  ScopedPrivateRegion.projected_region_contract live current globals source target.
Proof.
  intros GLOBAL CONTRACT temps p locals le tle memory exit final PRESERVED LOCAL SCOPE FRAME RUN.
  eapply CONTRACT; [eapply preserving_globals_compose; eauto|exact LOCAL|exact SCOPE|exact FRAME|exact RUN].
Qed.
Print Assumptions program_environment_check_sound.
Print Assumptions program_temp_scope_check_sound.
Print Assumptions scoped_contract_reference_transport.
