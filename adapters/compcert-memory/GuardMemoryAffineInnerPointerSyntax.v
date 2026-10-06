From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality ClightStraightLine ClightCountedLoop
  ClightRectangularStore ClightRectangularLoops ClightFrontendLoopProtocol ClightFrontendRegion.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryAffineSourceExpressions
  GuardMemoryAffineSourceReifier GuardMemoryAffineSourceContext GuardMemoryAffineSourceLoop
  GuardMemoryParametricSourceClight GuardMemoryParamPointerSyntax GuardMemoryMultiPointerComputeSyntax
  GuardMemoryScalarPointerComputeSyntax GuardMemoryMultiPointerIdentifiers GuardMemoryPointerCompute
  GuardMemoryNaryCompute GuardMemoryMultiPointerCompute GuardMemoryPointerSourceWords GuardMemorySourceParameters
  GuardMemoryRecursiveSyntax.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** This description records actual affine-inner control. It is not a
    rectangular source nest or an array-layout description. Metadata proposed
    by a caller is accepted only after the full source and body are checked. *)
Record memory_affine_inner_pointer_shape := MemoryAffineInnerPointerShape {
  affine_inner_pointer_row : ident;
  affine_inner_pointer_bound : ident;
  affine_inner_pointer_column : ident;
  affine_inner_pointer_inner_bound : ident;
  affine_inner_pointer_body : statement;
  affine_inner_pointer_outer_body : statement
}.
Definition memory_affine_inner_pointer_source shape :=
  frontend_counted_loop (affine_inner_pointer_row shape) (affine_inner_pointer_bound shape)
    (affine_inner_pointer_outer_body shape).
Definition memory_affine_inner_pointer_header shape expression :=
  memory_source_context (affine_inner_pointer_row shape) (affine_inner_pointer_bound shape) expression.
Definition memory_affine_inner_pointer_parameters shape expression body_parameters :=
  memory_affine_inner_pointer_header shape expression ++ body_parameters.
Definition memory_affine_inner_pointer_layout shape expression body_parameters :=
  [affine_inner_pointer_row shape;affine_inner_pointer_column shape] ++
    memory_affine_inner_pointer_parameters shape expression body_parameters.
Definition memory_affine_inner_pointer_limits (row_limit column_limit : Z) (header_limits body_limits : list Z) :=
  [row_limit;column_limit] ++ ((row_limit+1)::header_limits++body_limits).

Definition memory_identifiers_avoid_check (written protected : list ident) :=
  forallb (fun identifier => negb (existsb (Pos.eqb identifier) written)) protected.
Lemma memory_identifiers_avoid_check_sound written protected :
  memory_identifiers_avoid_check written protected = true ->
  forall identifier, In identifier protected -> ~ In identifier written.
Proof.
  unfold memory_identifiers_avoid_check; intros CHECK identifier MEMBER BAD.
  apply forallb_forall with (x := identifier) in CHECK; [|exact MEMBER].
  apply negb_true_iff in CHECK.
  assert (FOUND : existsb (Pos.eqb identifier) written = true).
  { apply existsb_exists; exists identifier; split; [exact BAD|apply Pos.eqb_refl]. }
  congruence.
Qed.

Definition memory_affine_inner_pointer_expr_eq : forall first second : L.expr, {first = second}+{first <> second}.
Proof. decide equality; try apply Z.eq_dec; apply Nat.eq_dec. Defined.

Record memory_affine_inner_pointer_certificate source shape expression encoded row_limit column_limit
  header_limits body_parameters body_limits pointers extent scalars operations := MemoryAffineInnerPointerCertificate {
  affine_inner_pointer_source_exact : source = memory_affine_inner_pointer_source shape;
  affine_inner_pointer_body_exact : flatten_region (affine_inner_pointer_body shape) =
    map memory_pointer_compute_statement operations;
  affine_inner_pointer_outer_exact : flatten_region (affine_inner_pointer_outer_body shape) =
    [memory_parametric_setup (affine_inner_pointer_inner_bound shape) (memory_source_affine_code expression);
      rectangle_reset (affine_inner_pointer_column shape);
      frontend_counted_loop (affine_inner_pointer_column shape) (affine_inner_pointer_inner_bound shape)
        (affine_inner_pointer_body shape)];
  affine_inner_pointer_rn : affine_inner_pointer_row shape <> affine_inner_pointer_bound shape;
  affine_inner_pointer_rc : affine_inner_pointer_row shape <> affine_inner_pointer_column shape;
  affine_inner_pointer_nc : affine_inner_pointer_bound shape <> affine_inner_pointer_column shape;
  affine_inner_pointer_rk : affine_inner_pointer_row shape <> affine_inner_pointer_inner_bound shape;
  affine_inner_pointer_nk : affine_inner_pointer_bound shape <> affine_inner_pointer_inner_bound shape;
  affine_inner_pointer_ck : affine_inner_pointer_column shape <> affine_inner_pointer_inner_bound shape;
  affine_inner_pointer_control_limits : Forall (fun cap => 0 < cap /\ signed_range cap) [row_limit;column_limit];
  affine_inner_pointer_bound_limit : signed_range (row_limit+1);
  affine_inner_pointer_header_limits_length : length header_limits =
    length (memory_source_other_parameters (affine_inner_pointer_row shape) (affine_inner_pointer_bound shape) expression);
  affine_inner_pointer_body_limits_length : length body_limits = length body_parameters;
  affine_inner_pointer_parameter_limits : Forall (fun cap => 0 < cap /\ signed_range cap) (header_limits++body_limits);
  affine_inner_pointer_window : 0 < extent /\ extent <= Int.max_signed+1 /\ 4*extent <= Ptrofs.modulus;
  affine_inner_pointer_protected : forall identifier,
    In identifier (pointers++(memory_affine_inner_pointer_parameters shape expression body_parameters++scalars)) ->
    ~ In identifier [affine_inner_pointer_row shape;affine_inner_pointer_column shape;affine_inner_pointer_inner_bound shape];
  affine_inner_pointer_unique : NoDup (memory_affine_inner_pointer_layout shape expression body_parameters++scalars);
  affine_inner_pointer_body_parameters_used : forall identifier, In identifier body_parameters -> exists operation,
    In operation operations /\ In identifier (memory_pointer_operation_address_reads operation);
  affine_inner_pointer_scalars_used : forall identifier, In identifier scalars -> exists operation index,
    In operation operations /\ nth_error (memory_affine_inner_pointer_layout shape expression body_parameters++scalars) index = Some identifier /\
    In index (memory_source_parameter_positions (memory_nary_compute_value operation));
  affine_inner_pointer_operations_nonempty : operations <> [];
  affine_inner_pointer_operations_valid : Forall (memory_multi_pointer_compute_valid
    (memory_affine_inner_pointer_limits row_limit column_limit header_limits body_limits)
    (memory_affine_inner_pointer_layout shape expression body_parameters) scalars extent) operations;
  affine_inner_pointer_operations_covered : Forall (memory_multi_pointer_operation_covered pointers) operations;
  affine_inner_pointer_header_encoding : memory_source_loop_expression (affine_inner_pointer_row shape)
    (memory_affine_inner_pointer_header shape expression) expression = Some encoded;
  affine_inner_pointer_full_encoding : memory_source_loop_expression (affine_inner_pointer_row shape)
    (memory_affine_inner_pointer_parameters shape expression body_parameters++scalars) expression = Some encoded
}.

Lemma memory_positive_caps_check_sound caps :
  forallb (fun cap => (0 <? cap) && (cap <=? Int.max_signed)) caps = true ->
  Forall (fun cap => 0 < cap /\ signed_range cap) caps.
Proof.
  intros CHECK; apply Forall_forall; intros cap MEMBER.
  apply forallb_forall with (x := cap) in CHECK; [|exact MEMBER].
  rewrite andb_true_iff,Z.ltb_lt,Z.leb_le in CHECK.
  unfold signed_range; change Int.min_signed with (-2147483648); split; lia.
Qed.

Definition check_memory_affine_pointer source shape expression encoded row_limit column_limit
  header_limits body_parameters body_limits pointers extent scalars operations :
  option (memory_affine_inner_pointer_certificate source shape expression encoded row_limit column_limit
    header_limits body_parameters body_limits pointers extent scalars operations).
Proof.
  destruct (statement_eq source (memory_affine_inner_pointer_source shape)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (affine_inner_pointer_body shape))
    (map memory_pointer_compute_statement operations)) as [BODY|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (affine_inner_pointer_outer_body shape))
    [memory_parametric_setup (affine_inner_pointer_inner_bound shape) (memory_source_affine_code expression);
      rectangle_reset (affine_inner_pointer_column shape);
      frontend_counted_loop (affine_inner_pointer_column shape) (affine_inner_pointer_inner_bound shape)
        (affine_inner_pointer_body shape)]) as [OUTER|]; [|exact None].
  destruct (peq (affine_inner_pointer_row shape) (affine_inner_pointer_bound shape)) as [|RN]; [exact None|].
  destruct (peq (affine_inner_pointer_row shape) (affine_inner_pointer_column shape)) as [|RC]; [exact None|].
  destruct (peq (affine_inner_pointer_bound shape) (affine_inner_pointer_column shape)) as [|NC]; [exact None|].
  destruct (peq (affine_inner_pointer_row shape) (affine_inner_pointer_inner_bound shape)) as [|RK]; [exact None|].
  destruct (peq (affine_inner_pointer_bound shape) (affine_inner_pointer_inner_bound shape)) as [|NK]; [exact None|].
  destruct (peq (affine_inner_pointer_column shape) (affine_inner_pointer_inner_bound shape)) as [|CK]; [exact None|].
  destruct (forallb (fun cap => (0 <? cap) && (cap <=? Int.max_signed)) [row_limit;column_limit]) eqn:CAPS; [|exact None].
  destruct (row_limit+1 <=? Int.max_signed) eqn:BOUND_CAP; [|exact None].
  destruct (Nat.eqb (length header_limits)
    (length (memory_source_other_parameters (affine_inner_pointer_row shape) (affine_inner_pointer_bound shape) expression))) eqn:HLEN; [|exact None].
  destruct (Nat.eqb (length body_limits) (length body_parameters)) eqn:BLEN; [|exact None].
  destruct (forallb (fun cap => (0 <? cap) && (cap <=? Int.max_signed)) (header_limits++body_limits)) eqn:PCAPS; [|exact None].
  destruct ((0 <? extent) && (extent <=? Int.max_signed+1) && (4*extent <=? Ptrofs.modulus)) eqn:EXTENT; [|exact None].
  destruct (memory_identifiers_avoid_check
    [affine_inner_pointer_row shape;affine_inner_pointer_column shape;affine_inner_pointer_inner_bound shape]
    (pointers++(memory_affine_inner_pointer_parameters shape expression body_parameters++scalars))) eqn:PROTECTED; [|exact None].
  destruct (memory_identifiers_unique_check (memory_affine_inner_pointer_layout shape expression body_parameters++scalars)) eqn:UNIQUE; [|exact None].
  destruct (memory_pointer_address_parameters_check body_parameters operations) eqn:B_USED; [|exact None].
  destruct (memory_scalar_pointer_registers_check
    (memory_affine_inner_pointer_layout shape expression body_parameters) scalars operations) eqn:S_USED; [|exact None].
  destruct operations as [|operation operations]; [exact None|].
  destruct (forallb (memory_multi_pointer_compute_check
    (memory_affine_inner_pointer_limits row_limit column_limit header_limits body_limits)
    (memory_affine_inner_pointer_layout shape expression body_parameters) scalars extent) (operation::operations)) eqn:VALID; [|exact None].
  destruct (forallb (memory_multi_pointer_operation_covered_check pointers) (operation::operations)) eqn:COVER; [|exact None].
  destruct (memory_source_loop_expression (affine_inner_pointer_row shape)
    (memory_affine_inner_pointer_header shape expression) expression) as [header_encoded|] eqn:HEADER; [|exact None].
  destruct (memory_affine_inner_pointer_expr_eq header_encoded encoded) as [SAME|]; [|exact None]; subst header_encoded.
  destruct (memory_source_loop_expression (affine_inner_pointer_row shape)
    (memory_affine_inner_pointer_parameters shape expression body_parameters++scalars) expression) as [full_encoded|] eqn:FULL; [|exact None].
  destruct (memory_affine_inner_pointer_expr_eq full_encoded encoded) as [SAME|]; [|exact None]; subst full_encoded.
  apply Nat.eqb_eq in HLEN,BLEN.
  assert (BOUND_LIMIT : signed_range (row_limit+1)).
  { pose proof (@memory_positive_caps_check_sound _ CAPS) as LIMITS.
    inversion LIMITS; subst; apply Z.leb_le in BOUND_CAP.
    unfold signed_range; change Int.min_signed with (-2147483648); lia. }
  assert (WINDOW : 0 < extent /\ extent <= Int.max_signed+1 /\ 4*extent <= Ptrofs.modulus).
  { rewrite !andb_true_iff,Z.ltb_lt,!Z.leb_le in EXTENT; tauto. }
  assert (OPS : Forall (memory_multi_pointer_compute_valid
    (memory_affine_inner_pointer_limits row_limit column_limit header_limits body_limits)
    (memory_affine_inner_pointer_layout shape expression body_parameters) scalars extent) (operation::operations)).
  { apply Forall_forall; intros op MEMBER; apply memory_multi_pointer_compute_check_sound.
    apply forallb_forall with (x := op) in VALID; assumption. }
  assert (COVERED : Forall (memory_multi_pointer_operation_covered pointers) (operation::operations)).
  { apply Forall_forall; intros op MEMBER; apply memory_multi_pointer_operation_covered_check_sound.
    apply forallb_forall with (x := op) in COVER; assumption. }
  exact (Some (@MemoryAffineInnerPointerCertificate source shape expression encoded row_limit column_limit
    header_limits body_parameters body_limits pointers extent scalars (operation::operations)
    SOURCE BODY OUTER RN RC NC RK NK CK (@memory_positive_caps_check_sound _ CAPS) BOUND_LIMIT HLEN BLEN
    (@memory_positive_caps_check_sound _ PCAPS) WINDOW (@memory_identifiers_avoid_check_sound _ _ PROTECTED)
    (@memory_identifiers_unique_check_sound _ UNIQUE) (@memory_pointer_address_parameters_check_sound _ _ B_USED)
    (@memory_scalar_pointer_registers_check_sound _ _ _ S_USED) ltac:(discriminate) OPS COVERED HEADER FULL)).
Defined.

Definition propose_memory_affine_inner_pointer_shape source :=
  match propose_frontend_shape source with
  | Some (row,bound,outer_body) => match flatten_region outer_body with
    | [Sset inner_bound header;Sset column _;inner_loop] =>
      match propose_frontend_shape inner_loop,propose_memory_source_affine header with
      | Some (_,_,body),Some expression =>
        Some (MemoryAffineInnerPointerShape row bound column inner_bound body outer_body,expression)
      | _,_ => None end
    | _ => None end
  | None => None end.
Record memory_affine_inner_pointer_package source := MemoryAffineInnerPointerPackage {
  affine_inner_pointer_shape : memory_affine_inner_pointer_shape;
  affine_inner_pointer_expression : memory_source_affine;
  affine_inner_pointer_encoded : L.expr;
  affine_inner_pointer_row_limit : Z;
  affine_inner_pointer_column_limit : Z;
  affine_inner_pointer_header_limits : list Z;
  affine_inner_pointer_body_parameters : list ident;
  affine_inner_pointer_body_limits : list Z;
  affine_inner_pointer_pointers : list ident;
  affine_inner_pointer_extent : Z;
  affine_inner_pointer_scalars : list ident;
  affine_inner_pointer_operations : list memory_nary_compute;
  affine_inner_pointer_syntax : memory_affine_inner_pointer_certificate source affine_inner_pointer_shape affine_inner_pointer_expression
    affine_inner_pointer_encoded affine_inner_pointer_row_limit affine_inner_pointer_column_limit affine_inner_pointer_header_limits
    affine_inner_pointer_body_parameters affine_inner_pointer_body_limits affine_inner_pointer_pointers affine_inner_pointer_extent
    affine_inner_pointer_scalars affine_inner_pointer_operations
}.
Definition describe_memory_affine_pointer source row_limit column_limit header_limits
  body_parameters body_limits pointers extent : option (memory_affine_inner_pointer_package source) :=
  match propose_memory_affine_inner_pointer_shape source with
  | Some (shape,expression) =>
    let layout := memory_affine_inner_pointer_layout shape expression body_parameters in
    let sources := flatten_region (affine_inner_pointer_body shape) in
    let scalars := propose_memory_pointer_scalars layout sources in
    match memory_source_loop_expression (affine_inner_pointer_row shape) (memory_affine_inner_pointer_header shape expression) expression,
      propose_memory_scalar_pointer_computes extent layout scalars sources with
    | Some encoded,Some operations =>
      match check_memory_affine_pointer source shape expression encoded row_limit column_limit header_limits
        body_parameters body_limits pointers extent scalars operations with
      | Some CERT => Some (@MemoryAffineInnerPointerPackage source shape expression encoded row_limit column_limit
          header_limits body_parameters body_limits pointers extent scalars operations CERT)
      | None => None end
    | _,_ => None end
  | None => None end.

Print Assumptions memory_identifiers_avoid_check_sound.
Print Assumptions check_memory_affine_pointer.
Print Assumptions describe_memory_affine_pointer.
