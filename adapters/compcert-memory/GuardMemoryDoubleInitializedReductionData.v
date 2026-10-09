From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightSyntaxEquality ClightLoopSyntax ClightRegionProgress ClightTempFrame.
From GuardMemory Require Import GuardMemoryValueInstr GuardMemoryDoubleLocations GuardMemoryDoubleAssignmentFactory
  GuardMemoryDoubleAffineSourceAccess GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceTransport
  GuardMemoryDoubleProgramBindings GuardMemoryLongControl GuardMemoryLongLoopControl GuardMemoryDoubleMatmulLoops.
Import ListNotations.
Set Implicit Arguments.

(** A recurring source pattern: an assignment followed by an initialized
    reduction loop. Names, access functions and operation trees come from ASTs. *)
Record double_initialized_reduction := DoubleInitializedReduction {
  initialized_reduction_iterator : ident;
  initialized_reduction_header : ident;
  initialized_reduction_initializer : statement;
  initialized_reduction_body : statement;
  initialized_reduction_initial_instruction : double_source_instruction;
  initialized_reduction_body_instruction : double_source_instruction
}.
Definition double_initialized_reduction_code description := Ssequence
  (initialized_reduction_initializer description)
  (memory_long_initialized_loop (initialized_reduction_iterator description)
    (double_matmul_long_condition (initialized_reduction_iterator description) (initialized_reduction_header description))
    (initialized_reduction_body description)).
Definition double_initialized_reduction_accesses description :=
  double_source_instruction_accesses (initialized_reduction_initial_instruction description)++
  double_source_instruction_accesses (initialized_reduction_body_instruction description).
Definition double_initialized_reduction_layouts description := double_source_layouts (double_initialized_reduction_accesses description).
Definition double_initialized_reduction_globals description := initialized_reduction_header description::
  map (fun access => fst (double_affine_source_function access)) (double_initialized_reduction_accesses description).
Definition double_initialized_reduction_static_check p controls description :=
  negb (existsb (Pos.eqb (initialized_reduction_iterator description)) controls) &&
  (global_declaration_check p (initialized_reduction_header description,memory_long_type) &&
  (negb (Pos.eqb (fst (value_instruction_write (double_source_instruction_model
      (initialized_reduction_initial_instruction description)))) (initialized_reduction_header description)) &&
  (negb (Pos.eqb (fst (value_instruction_write (double_source_instruction_model
      (initialized_reduction_body_instruction description)))) (initialized_reduction_header description)) &&
   double_source_layout_check (double_initialized_reduction_layouts description)
     (double_initialized_reduction_accesses description)))).
Record double_initialized_reduction_shape := DoubleInitializedReductionShape {
  reduction_shape_iterator : ident;
  reduction_shape_header : ident;
  reduction_shape_initializer : statement;
  reduction_shape_body : statement
}.
Definition propose_double_initialized_reduction_shape source :=
  match source with
  | Ssequence initializer (Ssequence (Sset iterator _) (Sloop
      (Ssequence (Sifthenelse (Ebinop Olt (Etempvar _ _) (Evar header _) _) Sskip Sbreak) reduction) _)) =>
      Some (DoubleInitializedReductionShape iterator header initializer reduction)
  | _ => None end.
Definition checked_double_initialized_reduction p controls source : option double_initialized_reduction :=
  match propose_double_initialized_reduction_shape source with
  | Some shape =>
    match checked_double_source_instruction p controls (reduction_shape_initializer shape),
      checked_double_source_instruction p (controls++[reduction_shape_iterator shape]) (reduction_shape_body shape) with
    | Some initial_instruction,Some body_instruction =>
      let description := DoubleInitializedReduction (reduction_shape_iterator shape) (reduction_shape_header shape)
        (reduction_shape_initializer shape) (reduction_shape_body shape) initial_instruction body_instruction in
      if statement_eq source (double_initialized_reduction_code description) then
        if double_initialized_reduction_static_check p controls description then Some description else None
      else None
    | _,_ => None end
  | _ => None end.
Lemma checked_double_initialized_reduction_sound p controls source description :
  checked_double_initialized_reduction p controls source=Some description ->
  source=double_initialized_reduction_code description /\
  checked_double_source_instruction p controls (initialized_reduction_initializer description)=
    Some (initialized_reduction_initial_instruction description) /\
  checked_double_source_instruction p (controls++[initialized_reduction_iterator description]) (initialized_reduction_body description)=
    Some (initialized_reduction_body_instruction description) /\
  double_initialized_reduction_static_check p controls description=true.
Proof.
  unfold checked_double_initialized_reduction;
    destruct (propose_double_initialized_reduction_shape source) as [[iterator header initializer reduction]|]; try discriminate.
  cbn [reduction_shape_iterator reduction_shape_header reduction_shape_initializer reduction_shape_body].
  destruct (checked_double_source_instruction p controls initializer) as [initial|] eqn:INITIAL; try discriminate.
  destruct (checked_double_source_instruction p (controls++[iterator]) reduction) as [body|] eqn:BODY; try discriminate.
  destruct (statement_eq _ _) as [EXACT|]; try discriminate.
  destruct (double_initialized_reduction_static_check p controls _) eqn:STATIC; try discriminate.
  intro RESULT; inversion RESULT; subst description; auto.
Qed.
Lemma double_initialized_reduction_static_sound p controls description :
  double_initialized_reduction_static_check p controls description=true ->
  ~ In (initialized_reduction_iterator description) controls /\
  global_declaration_check p (initialized_reduction_header description,memory_long_type)=true /\
  fst (value_instruction_write (double_source_instruction_model (initialized_reduction_initial_instruction description)))<>
    initialized_reduction_header description /\
  fst (value_instruction_write (double_source_instruction_model (initialized_reduction_body_instruction description)))<>
    initialized_reduction_header description /\
  double_source_layout_certificate (initialized_reduction_initial_instruction description) (double_initialized_reduction_layouts description) /\
  double_source_layout_certificate (initialized_reduction_body_instruction description) (double_initialized_reduction_layouts description).
Proof.
  unfold double_initialized_reduction_static_check; intro CHECK.
  apply andb_true_iff in CHECK as [CONTROL CHECK]; apply andb_true_iff in CHECK as [DECL CHECK].
  apply andb_true_iff in CHECK as [INITIAL CHECK]; apply andb_true_iff in CHECK as [BODY LAYOUT].
  apply negb_true_iff in CONTROL,INITIAL,BODY; apply Pos.eqb_neq in INITIAL,BODY.
  pose proof (@double_source_layout_check_sound (double_initialized_reduction_layouts description)
    (double_initialized_reduction_accesses description) LAYOUT) as REGISTRY.
  split.
  - intro MEMBER; assert (FOUND : existsb (Pos.eqb (initialized_reduction_iterator description)) controls=true).
    { apply existsb_exists; exists (initialized_reduction_iterator description); split; [exact MEMBER|apply Pos.eqb_refl]. }
    congruence.
  - split; [exact DECL|]; split; [exact INITIAL|]; split; [exact BODY|]; split;
      intros access MEMBER; apply REGISTRY; unfold double_initialized_reduction_accesses; apply in_or_app; auto.
Qed.

Print Assumptions checked_double_initialized_reduction_sound.
Print Assumptions double_initialized_reduction_static_sound.
