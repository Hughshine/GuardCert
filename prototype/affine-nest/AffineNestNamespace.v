From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestProbeRenaming AffineNestProbeStage.
Import ListNotations.
Set Implicit Arguments.

Definition affine_rename_injective_check registers rename := forallb(fun first=>forallb(fun second=>
  Pos.eqb first second || negb(Pos.eqb(rename first)(rename second))) registers) registers.
Lemma affine_rename_injective_check_sound registers rename :
  affine_rename_injective_check registers rename=true -> affine_rename_injective registers rename.
Proof.
  intros CHECK first second FIRST SECOND SAME.
  apply forallb_forall with(x:=first) in CHECK; [|exact FIRST].
  apply forallb_forall with(x:=second) in CHECK; [|exact SECOND].
  apply orb_true_iff in CHECK as [EQUAL|DIFFERENT]; [apply Pos.eqb_eq; exact EQUAL|].
  rewrite SAME,Pos.eqb_refl in DIFFERENT; discriminate.
Qed.

Definition affine_private_names_check (controls public : list ident) (rename : ident -> ident) result :=
  negb(existsb(Pos.eqb result) public) && forallb(fun identifier=>negb(existsb(Pos.eqb(rename identifier)) public)) controls.
Lemma affine_private_names_check_sound controls public rename result : affine_private_names_check controls public rename result=true ->
  ~In result public /\ (forall identifier, In identifier controls -> ~In(rename identifier) public).
Proof.
  intros CHECK; apply andb_true_iff in CHECK as [RESULT PRIVATE]; split.
  - apply negb_true_iff in RESULT; intro BAD.
    assert (FOUND:existsb(Pos.eqb result) public=true).
    { apply existsb_exists; exists result; split; [exact BAD|apply Pos.eqb_refl]. } congruence.
  - intros identifier MEMBER BAD; apply forallb_forall with(x:=identifier) in PRIVATE; [|exact MEMBER].
    apply negb_true_iff in PRIVATE.
    assert (FOUND:existsb(Pos.eqb(rename identifier)) public=true).
    { apply existsb_exists; exists(rename identifier); split; [exact BAD|apply Pos.eqb_refl]. } congruence.
Qed.

Definition affine_parameter_rename_check iterator bound parameters rename := forallb(fun identifier=>
  Pos.eqb identifier iterator || Pos.eqb identifier bound || Pos.eqb(rename identifier) identifier) parameters.
Lemma affine_parameter_rename_check_sound iterator bound parameters rename : affine_parameter_rename_check iterator bound parameters rename=true ->
  forall identifier, In identifier parameters -> identifier<>iterator -> identifier<>bound -> rename identifier=identifier.
Proof.
  intros CHECK identifier MEMBER ITERATOR BOUND; apply forallb_forall with(x:=identifier) in CHECK; [|exact MEMBER].
  repeat rewrite orb_true_iff in CHECK; destruct CHECK as [[SAME|SAME]|SAME]; apply Pos.eqb_eq in SAME; congruence.
Qed.

Definition affine_probe_registry nest parameters := affine_nest_controls nest++parameters.
Lemma affine_probe_registry_coverage nest parameters : affine_probe_stage_coverage(affine_probe_registry nest parameters) nest [] parameters.
Proof. intros identifier MEMBER; unfold affine_probe_registry; repeat rewrite in_app_iff in *; cbn in *; tauto. Qed.

Record affine_guard_namespace iterator bound expression body child parameters live rename result := AffineGuardNamespace {
  affine_names_injective : affine_rename_injective(affine_probe_registry(AffineSourceAxis iterator bound expression body child) parameters) rename;
  affine_names_root_distinct : rename iterator<>rename bound;
  affine_names_result_private : ~In result(parameters++[iterator;bound]++live);
  affine_names_controls_private : forall identifier, In identifier(affine_nest_controls(AffineSourceAxis iterator bound expression body child)) ->
    ~In(rename identifier)(parameters++[iterator;bound]++live);
  affine_names_parameters : forall identifier, In identifier parameters -> identifier<>iterator -> identifier<>bound -> rename identifier=identifier
}.
Definition check_affine_guard_namespace iterator bound expression body child parameters live rename result :
  option(affine_guard_namespace iterator bound expression body child parameters live rename result).
Proof.
  destruct(affine_rename_injective_check(affine_probe_registry(AffineSourceAxis iterator bound expression body child) parameters) rename) eqn:UNIQUE;
    [|exact None].
  destruct(Pos.eqb(rename iterator)(rename bound)) eqn:DISTINCT; [exact None|].
  destruct(affine_private_names_check(affine_nest_controls(AffineSourceAxis iterator bound expression body child))
    (parameters++[iterator;bound]++live) rename result) eqn:PRIVATE; [|exact None].
  destruct(affine_parameter_rename_check iterator bound parameters rename) eqn:PARAMETERS; [|exact None].
  assert (ROOT:rename iterator<>rename bound) by (intro SAME; rewrite SAME,Pos.eqb_refl in DISTINCT; discriminate).
  exact(Some(@AffineGuardNamespace iterator bound expression body child parameters live rename result
    (@affine_rename_injective_check_sound _ _ UNIQUE) ROOT
    (proj1(@affine_private_names_check_sound _ _ _ _ PRIVATE))
    (proj2(@affine_private_names_check_sound _ _ _ _ PRIVATE))
    (@affine_parameter_rename_check_sound _ _ _ _ PARAMETERS))).
Defined.
Print Assumptions check_affine_guard_namespace.
