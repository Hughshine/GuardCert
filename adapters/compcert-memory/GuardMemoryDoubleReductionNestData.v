From Stdlib Require Import List Bool Arith ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality ClightLoopSyntax ClightRegionProgress ClightTempFrame ClightSkipPrefix.
From GuardMemory Require Import GuardMemoryValueInstr GuardMemoryDoubleLocations GuardMemoryDoubleAssignmentFactory
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleInitializedNestData GuardMemoryDoubleInitializedRawNest
  GuardMemoryDoubleMatmulLoops GuardMemoryLongLoopControl GuardMemoryLongRawLoadedProgress
  GuardMemoryDoubleProgramBindings.
Import ListNotations.
Set Implicit Arguments.

(** Pure assignment nests retain the actual source assignment and every loaded
    bound test. The common header and dimensions are obtained from the AST. *)
Fixpoint double_reduction_nest_code (iterators : list ident) header body : statement :=
  match iterators with
  | [] => body
  | iterator::rest => memory_long_initialized_loop iterator
      (double_matmul_long_condition iterator header) (double_reduction_nest_code rest header body) end.
Fixpoint double_reduction_raw_nest_code (iterators : list ident) header body : statement :=
  match iterators with
  | [] => Ssequence Sskip body
  | iterator::rest => long_raw_initialized_loop iterator (Evar header memory_long_type)
      (double_reduction_raw_nest_code rest header body) end.
Record double_reduction_nest := DoubleReductionNest {
  reduction_nest_iterators : list ident;
  reduction_nest_header : ident;
  reduction_nest_body : statement;
  reduction_nest_instruction : double_source_instruction
}.
Fixpoint checked_double_reduction_nest_fuel fuel p controls header source : option (list ident*(statement*double_source_instruction)) :=
  match fuel with
  | O => None
  | S fuel => match checked_double_source_instruction p controls source with
    | Some description => Some ([],(source,description))
    | None => match double_initialized_outer_shape source with
      | Some (iterator,body) => if negb (existsb (Pos.eqb iterator) controls) then
          match checked_double_reduction_nest_fuel fuel p (controls++[iterator]) header body with
          | Some (rest,(leaf,description)) =>
            if statement_eq source (double_reduction_nest_code (iterator::rest) header leaf)
            then Some (iterator::rest,(leaf,description)) else None
          | None => None end
        else None
      | None => None end end end.
Lemma checked_double_reduction_nest_fuel_sound fuel : forall p controls header source iterators body description,
  checked_double_reduction_nest_fuel fuel p controls header source=Some (iterators,(body,description)) ->
  source=double_reduction_nest_code iterators header body /\
  checked_double_source_instruction p (controls++iterators) body=Some description /\
  double_initialized_nest_fresh controls iterators.
Proof.
  induction fuel as [|fuel IH]; intros p controls header source iterators body description;
    cbn [checked_double_reduction_nest_fuel]; [discriminate|].
  destruct (checked_double_source_instruction p controls source) as [leaf|] eqn:LEAF.
  - intro RUN; inversion RUN; subst; split; [reflexivity|split; [rewrite app_nil_r; exact LEAF|exact I]].
  - destruct (double_initialized_outer_shape source) as [[iterator child]|]; [|discriminate].
    destruct (negb (existsb (Pos.eqb iterator) controls)) eqn:FRESH; [|discriminate].
    destruct (checked_double_reduction_nest_fuel fuel p (controls++[iterator]) header child)
      as [[rest [leaf instruction]]|] eqn:CHILD; [|discriminate].
    destruct (statement_eq source (double_reduction_nest_code (iterator::rest) header leaf)) as [CODE|]; [|discriminate].
    intro RUN; inversion RUN; subst iterators body description.
    destruct (@IH p (controls++[iterator]) header child rest leaf instruction CHILD) as [SHAPE [CHECK FRESH_REST]].
    split; [exact CODE|split].
    + replace (controls++iterator::rest) with ((controls++[iterator])++rest)
        by (rewrite <- app_assoc; reflexivity); exact CHECK.
    + split; [|exact FRESH_REST].
      intro MEMBER; apply negb_true_iff in FRESH.
      assert (FOUND : existsb (Pos.eqb iterator) controls=true)
        by (apply existsb_exists; exists iterator; split; [exact MEMBER|apply Pos.eqb_refl]).
      congruence.
Qed.
Definition double_reduction_root_header source := match source with
  | Ssequence _ (Sloop (Ssequence (Sifthenelse (Ebinop _ _ (Evar header _) _) _ _) _) _) => Some header
  | _ => None end.
Definition checked_double_reduction_nest p controls source : option double_reduction_nest :=
  match double_reduction_root_header source with
  | Some header => match checked_double_reduction_nest_fuel (double_initialized_nest_fuel source)
      p controls header source with
    | Some (iterator::rest,(body,description)) =>
      if global_declaration_check p (header,memory_long_type) then
      if negb (Pos.eqb (fst (value_instruction_write (double_source_instruction_model description))) header) then
        Some (DoubleReductionNest (iterator::rest) header body description)
      else None else None
    | _ => None end
  | None => None end.
Theorem checked_double_reduction_nest_sound p controls source description :
  checked_double_reduction_nest p controls source=Some description ->
  source=double_reduction_nest_code (reduction_nest_iterators description)
    (reduction_nest_header description) (reduction_nest_body description) /\
  checked_double_source_instruction p (controls++reduction_nest_iterators description)
    (reduction_nest_body description)=Some (reduction_nest_instruction description) /\
  double_initialized_nest_fresh controls (reduction_nest_iterators description) /\
  reduction_nest_iterators description<>[] /\
  global_declaration_check p (reduction_nest_header description,memory_long_type)=true /\
  fst (value_instruction_write (double_source_instruction_model (reduction_nest_instruction description)))<>
    reduction_nest_header description.
Proof.
  unfold checked_double_reduction_nest.
  destruct (double_reduction_root_header source) as [header|]; [|discriminate].
  destruct (checked_double_reduction_nest_fuel _ p controls header source) as [[iterators [body instruction]]|] eqn:CHECK;
    [|discriminate].
  destruct iterators as [|iterator rest]; [discriminate|].
  destruct (global_declaration_check p (header,memory_long_type)) eqn:DECL; [|discriminate].
  destruct (negb (Pos.eqb (fst (value_instruction_write (double_source_instruction_model instruction))) header)) eqn:DISTINCT;
    [|discriminate].
  intro RUN; inversion RUN; subst description; cbn.
  destruct (@checked_double_reduction_nest_fuel_sound _ p controls header source (iterator::rest) body instruction CHECK)
    as [CODE [LEAF FRESH]].
  split; [exact CODE|split; [exact LEAF|split; [exact FRESH|split; [discriminate|split; [exact DECL|]]]]].
  apply negb_true_iff in DISTINCT; apply Pos.eqb_neq; exact DISTINCT.
Qed.
Definition checked_double_reduction_raw_nest p controls source :=
  match checked_double_reduction_nest p controls (double_initialized_elide_skips source) with
  | Some description => if statement_eq source (double_reduction_raw_nest_code
      (reduction_nest_iterators description) (reduction_nest_header description) (reduction_nest_body description))
    then Some description else None
  | None => None end.
Theorem checked_double_reduction_raw_nest_sound p controls source description :
  checked_double_reduction_raw_nest p controls source=Some description ->
  source=double_reduction_raw_nest_code (reduction_nest_iterators description)
    (reduction_nest_header description) (reduction_nest_body description) /\
  checked_double_reduction_nest p controls (double_reduction_nest_code (reduction_nest_iterators description)
    (reduction_nest_header description) (reduction_nest_body description))=Some description /\
  statement_execution_equivalent source (double_reduction_nest_code (reduction_nest_iterators description)
    (reduction_nest_header description) (reduction_nest_body description)).
Proof.
  unfold checked_double_reduction_raw_nest.
  destruct (checked_double_reduction_nest p controls (double_initialized_elide_skips source)) as [d|] eqn:CHECK;
    [|discriminate].
  destruct (statement_eq _ _) as [RAW|]; [|discriminate].
  intro RUN; inversion RUN; subst description.
  destruct (@checked_double_reduction_nest_sound p controls (double_initialized_elide_skips source) d CHECK) as [CODE REST].
  split; [exact RAW|split; [rewrite <- CODE; exact CHECK|]].
  rewrite <- CODE; apply double_initialized_elide_skips_execution.
Qed.
Lemma double_reduction_nest_quiet iterators header body : quiet_statement body=true ->
  quiet_statement (double_reduction_nest_code iterators header body)=true.
Proof.
  intro BODY; induction iterators; cbn [double_reduction_nest_code]; [exact BODY|].
  unfold memory_long_initialized_loop,memory_long_frontend_loop; cbn [quiet_statement]; rewrite IHiterators; reflexivity.
Qed.
Lemma double_reduction_nest_normal iterators header body :
  (exists target rhs, body=Sassign target rhs) -> normal_statement (double_reduction_nest_code iterators header body)=true.
Proof.
  intros [target [rhs BODY]]; destruct iterators; cbn [double_reduction_nest_code]; rewrite ?BODY; [reflexivity|].
  unfold memory_long_initialized_loop,memory_long_frontend_loop; cbn [normal_statement quiet_statement].
  rewrite double_reduction_nest_quiet by reflexivity; reflexivity.
Qed.
Lemma double_reduction_nest_writes iterators header body :
  (exists target rhs, body=Sassign target rhs) -> writes_only iterators (double_reduction_nest_code iterators header body).
Proof.
  intros [target [rhs BODY]]; induction iterators; cbn [double_reduction_nest_code]; [rewrite BODY; constructor|].
  unfold memory_long_initialized_loop,memory_long_frontend_loop,memory_long_increment.
  apply writes_sequence; [constructor; cbn; auto|apply writes_loop].
  - apply writes_sequence.
    + apply writes_if; constructor.
    + eapply writes_only_weaken; [intros key MEMBER; right; exact MEMBER|exact IHiterators].
  - constructor; cbn; auto.
Qed.

Print Assumptions checked_double_reduction_nest_fuel_sound.
Print Assumptions checked_double_reduction_nest_sound.
Print Assumptions checked_double_reduction_raw_nest_sound.
Print Assumptions double_reduction_nest_normal.
Print Assumptions double_reduction_nest_writes.
