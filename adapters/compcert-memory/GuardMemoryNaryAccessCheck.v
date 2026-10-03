From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight Ctypes Cop.
From polcert.lib Require Import Linalg.
From Guard Require Import ClightSyntaxEquality ClightRectangularStore.
From GuardMemory Require Import GuardMemoryAffineSourceReifier GuardMemoryAffineSourceExpressions
  GuardMemoryNaryAffineExpressions GuardMemoryNaryRanges GuardMemoryNaryAffineAccess.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition memory_nary_term_eq : forall first second : constraint, {first=second}+{first<>second}.
Proof. decide equality; [apply Z.eq_dec|apply list_eq_dec,Z.eq_dec]. Defined.
Definition memory_nary_access_valid limits (layout : list ident) access :=
  rectangle_layout_valid (memory_nary_access_shape access) /\
  memory_encode_nary_index layout (memory_nary_access_expression access) = Some (memory_nary_access_index access) /\
  forall values, memory_nary_ranges limits values ->
    0 <= memory_nary_index_value (memory_nary_access_index access) values < rectangle_extent (memory_nary_access_shape access).
Definition memory_nary_access_check limits layout access :=
  rectangle_layout_check (memory_nary_access_shape access) &&
  memory_nary_box_check limits (rectangle_extent (memory_nary_access_shape access)) (memory_nary_access_index access) &&
  match memory_encode_nary_index layout (memory_nary_access_expression access) with
  | Some term => if memory_nary_term_eq term (memory_nary_access_index access) then true else false
  | None => false end.
Lemma memory_nary_access_check_sound limits layout access :
  memory_nary_access_check limits layout access = true -> memory_nary_access_valid limits layout access.
Proof.
  unfold memory_nary_access_check; rewrite !andb_true_iff; intros [[LAYOUT BOX] ENCODE].
  destruct (memory_encode_nary_index layout (memory_nary_access_expression access)) as [term|] eqn:EXPRESSION; [|discriminate].
  destruct (memory_nary_term_eq term (memory_nary_access_index access)) as [SAME|]; [subst term|discriminate].
  split; [apply rectangle_layout_check_sound; exact LAYOUT|]; split; [exact EXPRESSION|].
  intros values RANGE; eapply memory_nary_box_sound; eassumption.
Qed.
Definition propose_memory_nary_access layout source :=
  match source with
  | Ederef (Ebinop Oadd (Evar array (Tarray _ extent _)) index _) _ =>
      match propose_memory_source_affine index with
      | Some expression => match memory_encode_nary_index layout expression with
          | Some term => Some (MemoryNaryAccess array (RectangleShape extent 1 0 0) expression term)
          | None => None end
      | None => None end
  | _ => None end.
Record memory_nary_access_package limits layout (source : expr) := MemoryNaryAccessPackage {
  nary_access_value : memory_nary_access;
  nary_access_valid : memory_nary_access_valid limits layout nary_access_value;
  nary_access_source_exact : source = memory_nary_access_code nary_access_value
}.
Definition describe_memory_nary_access limits layout source : option (memory_nary_access_package limits layout source).
Proof.
  destruct (propose_memory_nary_access layout source) as [access|]; [|exact None].
  destruct (memory_nary_access_check limits layout access) eqn:VALID; [|exact None].
  destruct (expression_eq source (memory_nary_access_code access)) as [SOURCE|]; [|exact None].
  exact (Some (@MemoryNaryAccessPackage limits layout source access (@memory_nary_access_check_sound limits layout access VALID) SOURCE)).
Defined.
Print Assumptions memory_nary_access_check_sound.
Print Assumptions describe_memory_nary_access.
