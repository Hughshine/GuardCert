From Stdlib Require Import List Bool.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightStraightLine ClightSyntaxEquality ClightRegionProgress.
From GuardInterface Require Import ClightSourceObservation ClightLoadedBoundSyntax.
Import ListNotations.
Set Implicit Arguments.

Definition propose_source_load atom : option (ident * ident) :=
  match atom with
  | Sset target (Ederef (Etempvar pointer ty) result_ty) =>
    if expression_eq (Ederef (Etempvar pointer ty) result_ty) (signed_load pointer)
    then Some (target,pointer) else None
  | _ => None end.
Fixpoint take_source_loads atoms : list (ident * ident) * list statement :=
  match atoms with
  | [] => ([],[])
  | atom::rest => match propose_source_load atom with
    | Some load => let '(loads,tail) := take_source_loads rest in (load::loads,tail)
    | None => ([],atoms) end end.
Definition source_statement_list atoms := fold_right Ssequence Sskip atoms.

(** This binds the actual normalized source, not a caller-provided assertion
    about dominating reads. Every load remains ordinary source code; the
    suffix is retained with all its effects. The flattening certificate handles
    frontend grouping, sequence association and empty statements. *)
Record observed_pointer_source_package source := ObservedPointerSourcePackage {
  observed_source_loads : list (ident * ident);
  observed_source_loop : statement;
  observed_source_suffix : statement;
  observed_source_flat : flatten_region source = flatten_region
    (Ssequence (Ssequence (source_load_prefix observed_source_loads) observed_source_loop) observed_source_suffix);
  observed_source_suffix_quiet : quiet_statement observed_source_suffix = true
}.

Definition check_observed_pointer_source source (loads : list (ident * ident)) (body suffix : statement) :
  option (observed_pointer_source_package source).
Proof.
  destruct (list_eq_dec statement_eq (flatten_region source)
    (flatten_region (Ssequence (Ssequence (source_load_prefix loads) body) suffix))) as [FLAT|]; [|exact None].
  destruct (Bool.bool_dec (quiet_statement suffix) true) as [QUIET|]; [|exact None].
  exact (Some (@ObservedPointerSourcePackage source loads body suffix FLAT QUIET)).
Defined.

Definition describe_observed_pointer_source source :=
  let '(loads,rest) := take_source_loads (flatten_region source) in
  match rest with
  | body::suffix => check_observed_pointer_source source loads body (source_statement_list suffix)
  | [] => None end.

Print Assumptions check_observed_pointer_source.
