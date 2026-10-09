From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Coqlib.
From compcert.common Require Import AST Values Memory Globalenvs.
From compcert.cfrontend Require Import Ctypes Clight.
From Guard Require Import ClightTempFootprint ClightRegionProgress ClightGlobalScope.
From GuardMemory Require Import GuardMemoryDoubleLocations.
Import ListNotations.
Set Implicit Arguments.

(** Static declarations establish symbols and types, independently of which
    memory reads a particular source execution reaches. *)
Definition global_declaration_check (p : program) (declaration : ident * type) :=
  existsb (fun definition => Pos.eqb (fst declaration) (fst definition) &&
    match snd definition with
    | Gvar variable => if type_eq (gvar_info variable) (snd declaration) then true else false
    | Gfun _ => false end) (prog_defs p).
Definition global_declarations_check p declarations := forallb (global_declaration_check p) declarations.
Lemma global_declaration_check_sound p identifier expected :
  global_declaration_check p (identifier,expected)=true ->
  exists variable, In (identifier,Gvar variable) (prog_defs p) /\ gvar_info variable=expected.
Proof.
  unfold global_declaration_check; intros CHECK; apply existsb_exists in CHECK as [[name definition] [MEMBER CHECK]].
  apply andb_true_iff in CHECK as [SAME TYPE]; cbn [fst snd] in SAME,TYPE.
  apply Pos.eqb_eq in SAME; subst name; destruct definition; try discriminate.
  destruct (type_eq (gvar_info v) expected); [exists v; auto|discriminate].
Qed.
Lemma global_declarations_check_sound p declarations : global_declarations_check p declarations=true ->
  forall identifier expected, In (identifier,expected) declarations ->
  exists variable, In (identifier,Gvar variable) (prog_defs p) /\ gvar_info variable=expected.
Proof.
  intros CHECK identifier expected MEMBER; unfold global_declarations_check in CHECK.
  apply forallb_forall with (x:=(identifier,expected)) in CHECK; [apply global_declaration_check_sound; exact CHECK|exact MEMBER].
Qed.
Theorem checked_global_binding p declarations ge locals identifier expected :
  global_declarations_check p declarations=true -> In (identifier,expected) declarations ->
  preserving_globals (globalenv p) ge -> locals_avoid (var_names declarations) locals ->
  exists block, double_global_binding ge locals identifier block.
Proof.
  intros CHECK MEMBER [_ SYMBOLS] LOCAL.
  destruct (@global_declarations_check_sound p declarations CHECK identifier expected MEMBER) as [variable [DECL TYPE]].
  destruct (Genv.find_symbol_exists p identifier (Gvar variable) DECL) as [block SYMBOL].
  exists block; split.
  - apply LOCAL; unfold var_names; apply in_map_iff; exists (identifier,expected); split; [reflexivity|exact MEMBER].
  - rewrite SYMBOLS; exact SYMBOL.
Qed.

Print Assumptions global_declarations_check_sound.
Print Assumptions checked_global_binding.
