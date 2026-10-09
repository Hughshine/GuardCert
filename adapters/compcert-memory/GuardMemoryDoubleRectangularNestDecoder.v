From Stdlib Require Import List Bool Arith ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality ClightLoopSyntax ClightRegionProgress ClightTempFrame ClightSkipPrefix.
From GuardMemory Require Import GuardMemoryValueInstr GuardMemoryDoubleLocations GuardMemoryDoubleSourceInstruction
  GuardMemoryDoubleInitializedNestData GuardMemoryDoubleInitializedRawNest GuardMemoryDoubleProgramBindings
  GuardMemoryDoubleReductionNestData GuardMemoryDoubleRectangularNestData.
Import ListNotations.
Set Implicit Arguments.

Record double_rectangular_nest := DoubleRectangularNest {
  rectangular_nest_axes : double_rectangular_axes;
  rectangular_nest_body : statement;
  rectangular_nest_instruction : double_source_instruction
}.
Fixpoint checked_double_rectangular_nest_fuel fuel p controls source : option double_rectangular_nest :=
  match fuel with
  | O=>None
  | S fuel=>match checked_double_source_instruction p controls source with
    | Some instruction=>Some (DoubleRectangularNest [] source instruction)
    | None=>match double_initialized_outer_shape source,double_reduction_root_header source with
      | Some (iterator,child),Some header=>if negb (existsb (Pos.eqb iterator) controls) then
        match checked_double_rectangular_nest_fuel fuel p (controls++[iterator]) child with
        | Some nested=>let axes := (iterator,header)::rectangular_nest_axes nested in
          if statement_eq source (double_rectangular_nest_code axes (rectangular_nest_body nested))
          then Some (DoubleRectangularNest axes (rectangular_nest_body nested) (rectangular_nest_instruction nested))
          else None
        | None=>None end else None
      | _,_=>None end end end.
Theorem checked_double_rectangular_nest_fuel_sound fuel : forall p controls source description,
  checked_double_rectangular_nest_fuel fuel p controls source=Some description ->
  source=double_rectangular_nest_code (rectangular_nest_axes description) (rectangular_nest_body description) /\
  checked_double_source_instruction p (controls++double_rectangular_iterators (rectangular_nest_axes description))
    (rectangular_nest_body description)=Some (rectangular_nest_instruction description) /\
  double_initialized_nest_fresh controls (double_rectangular_iterators (rectangular_nest_axes description)).
Proof.
  induction fuel as [|fuel IH]; intros p controls source description;
    cbn [checked_double_rectangular_nest_fuel]; [discriminate|].
  destruct (checked_double_source_instruction p controls source) as [instruction|] eqn:LEAF.
  - intro RUN; inversion RUN; subst description;
      cbn [rectangular_nest_axes rectangular_nest_body rectangular_nest_instruction
        double_rectangular_nest_code double_rectangular_iterators].
    split; [reflexivity|split; [rewrite app_nil_r; exact LEAF|exact I]].
  - destruct (double_initialized_outer_shape source) as [[iterator child]|],
      (double_reduction_root_header source) as [header|]; try discriminate.
    destruct (negb (existsb (Pos.eqb iterator) controls)) eqn:FRESH; [|discriminate].
    destruct (checked_double_rectangular_nest_fuel fuel p (controls++[iterator]) child) as [nested|] eqn:CHILD; [|discriminate].
    destruct (statement_eq source (double_rectangular_nest_code
      ((iterator,header)::rectangular_nest_axes nested) (rectangular_nest_body nested))) as [CODE|]; [|discriminate].
    intro RUN; inversion RUN; subst description;
      cbn [rectangular_nest_axes rectangular_nest_body rectangular_nest_instruction
        double_rectangular_iterators map fst].
    destruct (@IH p (controls++[iterator]) child nested CHILD) as [CHILD_CODE [CHECK CHILD_FRESH]].
    split; [exact CODE|split].
    + change (checked_double_source_instruction p
        (controls++iterator::double_rectangular_iterators (rectangular_nest_axes nested))
        (rectangular_nest_body nested)=Some (rectangular_nest_instruction nested)).
      replace (controls++iterator::double_rectangular_iterators (rectangular_nest_axes nested)) with
        ((controls++[iterator])++double_rectangular_iterators (rectangular_nest_axes nested))
        by (rewrite <- app_assoc; reflexivity); exact CHECK.
    + split; [|exact CHILD_FRESH].
      intro MEMBER; apply negb_true_iff in FRESH.
      assert (FOUND : existsb (Pos.eqb iterator) controls=true)
        by (apply existsb_exists; exists iterator; split; [exact MEMBER|apply Pos.eqb_refl]).
      congruence.
Qed.
Definition double_rectangular_headers_check p description := forallb
  (fun axis => global_declaration_check p (snd axis,memory_long_type) &&
    negb (Pos.eqb (fst (value_instruction_write (double_source_instruction_model
      (rectangular_nest_instruction description)))) (snd axis))) (rectangular_nest_axes description).
Theorem double_rectangular_headers_check_sound p description :
  double_rectangular_headers_check p description=true ->
  forall axis, In axis (rectangular_nest_axes description) ->
    global_declaration_check p (snd axis,memory_long_type)=true /\
    fst (value_instruction_write (double_source_instruction_model (rectangular_nest_instruction description)))<>snd axis.
Proof.
  intros CHECK axis MEMBER; unfold double_rectangular_headers_check in CHECK.
  apply forallb_forall with (x:=axis) in CHECK; [|exact MEMBER].
  apply andb_true_iff in CHECK as [DECL DISTINCT]; split; [exact DECL|].
  apply negb_true_iff in DISTINCT; apply Pos.eqb_neq; exact DISTINCT.
Qed.
Definition checked_double_rectangular_nest p controls source :=
  match checked_double_rectangular_nest_fuel (double_initialized_nest_fuel source) p controls source with
  | Some description=>match rectangular_nest_axes description with
    | []=>None
    | _::_=>if double_rectangular_headers_check p description then Some description else None end
  | None=>None end.
Theorem checked_double_rectangular_nest_sound p controls source description :
  checked_double_rectangular_nest p controls source=Some description ->
  source=double_rectangular_nest_code (rectangular_nest_axes description) (rectangular_nest_body description) /\
  checked_double_source_instruction p (controls++double_rectangular_iterators (rectangular_nest_axes description))
    (rectangular_nest_body description)=Some (rectangular_nest_instruction description) /\
  double_initialized_nest_fresh controls (double_rectangular_iterators (rectangular_nest_axes description)) /\
  rectangular_nest_axes description<>[] /\ double_rectangular_headers_check p description=true.
Proof.
  unfold checked_double_rectangular_nest.
  destruct (checked_double_rectangular_nest_fuel _ p controls source) as [nested|] eqn:DECODE; [|discriminate].
  destruct (rectangular_nest_axes nested) as [|axis rest] eqn:AXES; [discriminate|].
  destruct (double_rectangular_headers_check p nested) eqn:HEADERS; [|discriminate].
  intro RUN; inversion RUN; subst description.
  destruct (@checked_double_rectangular_nest_fuel_sound _ p controls source nested DECODE) as [CODE [LEAF FRESH]].
  repeat split; try assumption; rewrite AXES; discriminate.
Qed.
Definition checked_double_rectangular_raw_nest p controls source :=
  match checked_double_rectangular_nest p controls (double_initialized_elide_skips source) with
  | Some description=>if statement_eq source (double_rectangular_raw_nest_code
      (rectangular_nest_axes description) (rectangular_nest_body description)) then Some description else None
  | None=>None end.
Theorem checked_double_rectangular_raw_nest_sound p controls source description :
  checked_double_rectangular_raw_nest p controls source=Some description ->
  source=double_rectangular_raw_nest_code (rectangular_nest_axes description) (rectangular_nest_body description) /\
  checked_double_rectangular_nest p controls (double_rectangular_nest_code
    (rectangular_nest_axes description) (rectangular_nest_body description))=Some description /\
  statement_execution_equivalent source (double_rectangular_nest_code
    (rectangular_nest_axes description) (rectangular_nest_body description)).
Proof.
  unfold checked_double_rectangular_raw_nest.
  destruct (checked_double_rectangular_nest p controls (double_initialized_elide_skips source)) as [nested|] eqn:CHECK;
    [|discriminate].
  destruct (statement_eq _ _) as [RAW|]; [|discriminate].
  intro RUN; inversion RUN; subst description.
  destruct (@checked_double_rectangular_nest_sound p controls (double_initialized_elide_skips source) nested CHECK) as [CODE REST].
  split; [exact RAW|split; [rewrite <- CODE; exact CHECK|]].
  rewrite <- CODE; apply double_initialized_elide_skips_execution.
Qed.

Print Assumptions checked_double_rectangular_nest_fuel_sound.
Print Assumptions double_rectangular_headers_check_sound.
Print Assumptions checked_double_rectangular_nest_sound.
Print Assumptions checked_double_rectangular_raw_nest_sound.
