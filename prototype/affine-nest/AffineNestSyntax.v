From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality ClightFrontendRegion ClightStraightLine
  ClightCountedLoop ClightStructuredProgress ClightRectangularLoops ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceReifier
  GuardMemoryRecursiveSyntax.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Each child bound is recomputed in its actual parent body. The root's
    expression is metadata for its already available upper-bound temporary.
    The syntax certificate checks complete ASTs rather than accepting an
    interface whose source-execution premise is left to the caller. *)
Inductive affine_source_nest :=
| AffineSourceLeaf (code : statement)
| AffineSourceAxis (iterator bound : ident) (expression : memory_source_affine)
    (body : statement) (child : affine_source_nest).

Definition affine_nest_source nest := match nest with
  | AffineSourceLeaf code => code
  | AffineSourceAxis iterator bound _ body _ => frontend_counted_loop iterator bound body end.
Fixpoint affine_nest_leaf nest := match nest with
  | AffineSourceLeaf code => code
  | AffineSourceAxis _ _ _ _ child => affine_nest_leaf child end.
Fixpoint affine_nest_iterators nest := match nest with
  | AffineSourceLeaf _ => []
  | AffineSourceAxis iterator _ _ _ child => iterator::affine_nest_iterators child end.
Fixpoint affine_nest_bounds nest := match nest with
  | AffineSourceLeaf _ => []
  | AffineSourceAxis _ bound _ _ child => bound::affine_nest_bounds child end.
Definition affine_nest_child_prefix child := match child with
  | AffineSourceLeaf _ => []
  | AffineSourceAxis iterator bound expression _ _ =>
      [Sset bound (memory_source_affine_code expression);rectangle_reset iterator] end.
Definition affine_nest_child_shape body child := match child with
  | AffineSourceLeaf code => body = code
  | AffineSourceAxis _ _ _ _ _ =>
      flatten_region body = affine_nest_child_prefix child++[affine_nest_source child] end.
Fixpoint affine_nest_shapes nest := match nest with
  | AffineSourceLeaf _ => True
  | AffineSourceAxis _ _ _ body child => affine_nest_child_shape body child /\ affine_nest_shapes child end.
Fixpoint affine_nest_bound_dependencies prefix parameters nest := match nest with
  | AffineSourceLeaf _ => True
  | AffineSourceAxis iterator _ expression _ child =>
      (forall identifier, In identifier (memory_source_affine_reads expression) -> In identifier (prefix++parameters)) /\
      affine_nest_bound_dependencies (prefix++[iterator]) parameters child end.
Definition affine_nest_fresh nest := NoDup (affine_nest_iterators nest++affine_nest_bounds nest).
Definition affine_root_expression_valid nest := match nest with
  | AffineSourceLeaf _ => False
  | AffineSourceAxis _ bound expression _ _ => expression = MemorySourceTemp bound end.
Definition affine_root_expression_check nest := match nest with
  | AffineSourceAxis _ bound (MemorySourceTemp identifier) _ _ => Pos.eqb identifier bound
  | _ => false end.
Lemma affine_root_expression_check_sound nest : affine_root_expression_check nest = true -> affine_root_expression_valid nest.
Proof.
  destruct nest; [discriminate|]; destruct expression; try discriminate; cbn.
  intro SAME; apply Pos.eqb_eq in SAME; subst; reflexivity.
Qed.
Definition affine_parameters_fresh parameters nest :=
  forall identifier, In identifier parameters -> ~ In identifier (affine_nest_iterators nest++tl (affine_nest_bounds nest)).
Definition affine_parameters_fresh_check parameters nest :=
  forallb (fun identifier => negb (existsb (Pos.eqb identifier)
    (affine_nest_iterators nest++tl (affine_nest_bounds nest)))) parameters.
Lemma affine_parameters_fresh_check_sound parameters nest :
  affine_parameters_fresh_check parameters nest = true -> affine_parameters_fresh parameters nest.
Proof.
  intros CHECK identifier MEMBER BAD.
  apply forallb_forall with (x:=identifier) in CHECK; [|exact MEMBER].
  apply negb_true_iff in CHECK.
  assert (FOUND : existsb (Pos.eqb identifier) (affine_nest_iterators nest++tl (affine_nest_bounds nest)) = true).
  { apply existsb_exists; exists identifier; split; [exact BAD|apply Pos.eqb_refl]. }
  congruence.
Qed.

Definition affine_nest_child_shape_check body child := match child with
  | AffineSourceLeaf code => if statement_eq body code then true else false
  | AffineSourceAxis _ _ _ _ _ =>
      if list_eq_dec statement_eq (flatten_region body)
        (affine_nest_child_prefix child++[affine_nest_source child]) then true else false end.
Fixpoint affine_nest_shapes_check nest := match nest with
  | AffineSourceLeaf _ => true
  | AffineSourceAxis _ _ _ body child => affine_nest_child_shape_check body child && affine_nest_shapes_check child end.
Theorem affine_nest_shapes_check_sound nest : affine_nest_shapes_check nest = true -> affine_nest_shapes nest.
Proof.
  induction nest; cbn [affine_nest_shapes_check affine_nest_shapes]; intro CHECK; [exact I|].
  apply andb_true_iff in CHECK as [SHAPE REST]; split; [|apply IHnest; exact REST].
  destruct nest; cbn [affine_nest_child_shape_check affine_nest_child_shape] in *;
    repeat destruct statement_eq; repeat destruct list_eq_dec; try discriminate; assumption.
Qed.
Fixpoint affine_nest_dependencies_check prefix parameters nest := match nest with
  | AffineSourceLeaf _ => true
  | AffineSourceAxis iterator _ expression _ child =>
      forallb (fun identifier => existsb (Pos.eqb identifier) (prefix++parameters))
        (memory_source_affine_reads expression) &&
      affine_nest_dependencies_check (prefix++[iterator]) parameters child end.
Theorem affine_nest_dependencies_check_sound prefix parameters nest :
  affine_nest_dependencies_check prefix parameters nest = true -> affine_nest_bound_dependencies prefix parameters nest.
Proof.
  revert prefix; induction nest; intros prefix CHECK; cbn [affine_nest_bound_dependencies]; [exact I|].
  apply andb_true_iff in CHECK as [READS CHILD]; split; [|apply IHnest; exact CHILD].
  intros identifier MEMBER; apply forallb_forall with (x:=identifier) in READS; [|exact MEMBER].
  apply existsb_exists in READS as [found [IN SAME]]; apply Pos.eqb_eq in SAME; subst found; exact IN.
Qed.

Definition affine_nest_with_expression expression nest := match nest with
  | AffineSourceLeaf code => AffineSourceLeaf code
  | AffineSourceAxis iterator bound _ body child => AffineSourceAxis iterator bound expression body child end.
Fixpoint propose_affine_source_nest fuel source : affine_source_nest := match fuel with
  | O => AffineSourceLeaf source
  | S remaining => match propose_frontend_shape source with
      | Some (iterator,bound,body) =>
          let child := match flatten_region body with
            | [Sset child_bound code;reset;nested] =>
                match propose_frontend_shape nested,propose_memory_source_affine code with
                | Some (_,_,_),Some expression =>
                    affine_nest_with_expression expression (propose_affine_source_nest remaining nested)
                | _,_ => AffineSourceLeaf body end
            | _ => AffineSourceLeaf body end in
          AffineSourceAxis iterator bound (MemorySourceTemp bound) body child
      | None => AffineSourceLeaf source end end.

Record affine_nest_description source parameters := AffineNestDescription {
  described_affine_nest : affine_source_nest;
  described_affine_source : source = affine_nest_source described_affine_nest;
  described_affine_nonempty : affine_nest_iterators described_affine_nest <> [];
  described_affine_shapes : affine_nest_shapes described_affine_nest;
  described_affine_fresh : affine_nest_fresh described_affine_nest;
  described_affine_dependencies : affine_nest_bound_dependencies [] parameters described_affine_nest;
  described_affine_root_expression : affine_root_expression_valid described_affine_nest;
  described_affine_parameters_fresh : affine_parameters_fresh parameters described_affine_nest
}.
Definition check_affine_nest source parameters (nest : affine_source_nest) : option (affine_nest_description source parameters).
Proof.
  destruct (statement_eq source (affine_nest_source nest)) as [EXACT|]; [|exact None].
  destruct (list_eq_dec peq (affine_nest_iterators nest) []) as [|NONEMPTY]; [exact None|].
  destruct (affine_nest_shapes_check nest) eqn:SHAPES; [|exact None].
  destruct (memory_identifiers_unique_check (affine_nest_iterators nest++affine_nest_bounds nest)) eqn:FRESH; [|exact None].
  destruct (affine_nest_dependencies_check [] parameters nest) eqn:READS; [|exact None].
  destruct (affine_root_expression_check nest) eqn:ROOT; [|exact None].
  destruct (affine_parameters_fresh_check parameters nest) eqn:PARAMETERS; [|exact None].
  exact (Some (@AffineNestDescription source parameters nest EXACT NONEMPTY
    (@affine_nest_shapes_check_sound nest SHAPES)
    (@memory_identifiers_unique_check_sound _ FRESH)
    (@affine_nest_dependencies_check_sound [] parameters nest READS)
    (@affine_root_expression_check_sound nest ROOT)
    (@affine_parameters_fresh_check_sound parameters nest PARAMETERS))).
Defined.
Definition describe_affine_nest source parameters :=
  check_affine_nest source parameters (propose_affine_source_nest (progress_syntax_size source) source).
Print Assumptions affine_nest_shapes_check_sound.
Print Assumptions affine_nest_dependencies_check_sound.
Print Assumptions check_affine_nest.
