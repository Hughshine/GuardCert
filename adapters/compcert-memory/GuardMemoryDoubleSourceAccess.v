From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Globalenvs.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightSyntaxEquality ClightGlobalScope ClightRegionProgress CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryDoubleValue GuardMemoryDoubleLocations
  GuardMemoryDoubleAssignment GuardMemoryDoubleTensorBackend GuardMemoryDynamicTensorLayout
  GuardMemoryDoubleProgramBindings.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The descriptor retains actual coordinate expressions. The reconstruction
    gate verifies the entire lvalue, including all array/pointer types. *)
Record double_source_access := DoubleSourceAccess {
  double_source_array : ident;
  double_source_dimensions : list Z;
  double_source_coordinates : list expr
}.
Fixpoint propose_double_source_dimensions ty : option (list Z) := match ty with
| Tfloat F64 _ => Some []
| Tarray child dimension _ => option_map (cons dimension) (propose_double_source_dimensions child)
| _ => None end.
Fixpoint propose_double_source_access source : option double_source_access := match source with
| Evar name ty => option_map (fun dimensions => DoubleSourceAccess name dimensions [])
    (propose_double_source_dimensions ty)
| Ederef (Ebinop Oadd base coordinate _) _ =>
    match propose_double_source_access base with
    | Some access => Some (DoubleSourceAccess (double_source_array access) (double_source_dimensions access)
        (double_source_coordinates access++[coordinate]))
    | None => None end
| _ => None end.
Definition double_source_access_code access := double_tensor_lvalue_code
  (Evar (double_source_array access) (double_tensor_type (double_source_dimensions access)))
  (double_source_dimensions access) (double_source_coordinates access).
Definition describe_double_source_access source : option double_source_access :=
  match propose_double_source_access source with
  | Some access => match double_source_access_code access with
    | Some code => if expression_eq source code then Some access else None
    | None => None end
  | None => None end.
Lemma describe_double_source_access_exact source access :
  describe_double_source_access source=Some access -> double_source_access_code access=Some source.
Proof.
  unfold describe_double_source_access; destruct (propose_double_source_access source) as [proposed|]; try discriminate.
  destruct (double_source_access_code proposed) as [code|] eqn:CODE; try discriminate.
  destruct (expression_eq source code) as [SAME|]; try discriminate.
  intro RESULT; inversion RESULT; subst access; subst source; exact CODE.
Qed.
Theorem double_source_access_receipt ge locals temps memory source access block coordinates index :
  describe_double_source_access source=Some access ->
  double_global_binding ge locals (double_source_array access) block ->
  8*tensor_volume (double_source_dimensions access)<=Ptrofs.modulus ->
  Forall2 (fun code value => typeof code=memory_long_type /\
    eval_expr ge locals temps memory code (Vlong (Int64.repr value)))
    (double_source_coordinates access) coordinates ->
  tensor_index (double_source_dimensions access) coordinates=Some index ->
  double_memory_location_receipt ge locals temps memory source (MemoryLocation Mfloat64 block (8*index)).
Proof.
  intros DESCRIBE [LOCAL SYMBOL] SPAN OPERANDS INDEX.
  pose proof (@describe_double_source_access_exact source access DESCRIBE) as CODE.
  unfold double_source_access_code in CODE.
  pose proof (@tensor_index_bounds (double_source_dimensions access) coordinates index INDEX) as RANGE.
  unfold double_memory_location_receipt; split.
  - eapply (@double_tensor_lvalue_type (double_source_dimensions access)
      (Evar (double_source_array access) (double_tensor_type (double_source_dimensions access)))
      (double_source_coordinates access) source); [reflexivity|exact CODE].
  - split; [reflexivity|]; split; [cbn; lia|]; split.
    + cbn; nia.
    + replace (8*index) with (0+8*index) by ring.
      eapply (@double_tensor_lvalue_execution (double_source_dimensions access) ge locals temps memory
        (Evar (double_source_array access) (double_tensor_type (double_source_dimensions access)))
        (double_source_coordinates access) coordinates block 0 index source);
        [reflexivity| |exact OPERANDS|exact INDEX|exact CODE].
      change (eval_lvalue ge locals temps memory
        (Evar (double_source_array access) (double_tensor_type (double_source_dimensions access))) block Ptrofs.zero Full).
      apply eval_Evar_global; assumption.
Qed.

Definition double_source_access_static_check p access :=
  global_declaration_check p (double_source_array access,double_tensor_type (double_source_dimensions access)) &&
  (forallb (fun dimension => 0<?dimension) (double_source_dimensions access) &&
   (8*tensor_volume (double_source_dimensions access)<=?Ptrofs.modulus)).
Theorem double_source_access_static_sound p access ge locals :
  double_source_access_static_check p access=true ->
  preserving_globals (globalenv p) ge -> locals_avoid [double_source_array access] locals ->
  exists block, double_global_binding ge locals (double_source_array access) block /\
    Forall (fun dimension => 0<dimension) (double_source_dimensions access) /\
    8*tensor_volume (double_source_dimensions access)<=Ptrofs.modulus.
Proof.
  unfold double_source_access_static_check; intro CHECK.
  apply andb_true_iff in CHECK as [DECL CHECK]; apply andb_true_iff in CHECK as [POSITIVE SPAN].
  apply Z.leb_le in SPAN; intros GLOBAL LOCAL.
  assert (DECLS : global_declarations_check p
    [(double_source_array access,double_tensor_type (double_source_dimensions access))]=true).
  { unfold global_declarations_check; cbn [forallb]; rewrite DECL; reflexivity. }
  destruct (@checked_global_binding p
    [(double_source_array access,double_tensor_type (double_source_dimensions access))] ge locals
    (double_source_array access) (double_tensor_type (double_source_dimensions access))
    DECLS ltac:(cbn; auto) GLOBAL LOCAL) as [block BINDING].
  exists block; split; [exact BINDING|]; split; [|exact SPAN].
  apply Forall_forall; intros dimension MEMBER; apply forallb_forall with (x:=dimension) in POSITIVE;
    [apply Z.ltb_lt; exact POSITIVE|exact MEMBER].
Qed.

Print Assumptions describe_double_source_access_exact.
Print Assumptions double_source_access_receipt.
Print Assumptions double_source_access_static_sound.
