From Stdlib Require Import List Bool ZArith.
From polcert.lib Require Import Linalg ImpureAlarmConfig.
From polcert.src Require Import PolyBase.
From polcert.polygen Require Import CodeGen Result.
From Vpl Require Import Impure ImpureConfig.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryPolyhedral GuardMemoryLoops GuardMemoryExtractorTrace GuardMemoryGeneratedBounds.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Module MemoryCodeGen := CodeGen GuardMemoryIRs.
Module PL := GuardMemoryIRs.PolyLang.

(** Schedule construction is a proposal. Source domains, accesses, arguments
    and instructions come from the actual extractor. The generated Loop is
    independently checked before any guarded replacement can be returned. *)
Definition memory_reschedule_instruction dimension (pi : PL.PolyInstr) schedule : PL.PolyInstr :=
  {| PL.pi_depth := PL.pi_depth pi; PL.pi_instr := PL.pi_instr pi;
     PL.pi_poly := PL.pi_poly pi; PL.pi_schedule :=
       map (fun term => (resize (dimension + PL.pi_depth pi) (fst term),snd term)) schedule;
     PL.pi_point_witness := PL.pi_point_witness pi;
     PL.pi_transformation := PL.pi_transformation pi;
     PL.pi_access_transformation := PL.pi_access_transformation pi;
     PL.pi_waccess := PL.pi_waccess pi; PL.pi_raccess := PL.pi_raccess pi |}.
Fixpoint memory_reschedule_instructions dimension instructions schedules :=
  match instructions,schedules with
  | [],[] => Some []
  | instruction::rest,schedule::tail =>
    if forallb (fun term => Nat.leb (length (fst term)) (dimension + PL.pi_depth instruction)) schedule then
    match memory_reschedule_instructions dimension rest tail with
    | Some remaining => Some (memory_reschedule_instruction dimension instruction schedule::remaining)
    | None => None end
    else None
  | _,_ => None end.

(** A generator alarm discards the proposal and restores an alarm-free result.
    It never turns the alarmed default Loop into an accepted candidate. *)
Definition memory_attempt_codegen program : CoreAlarmed.Base.imp (option L.stmt) :=
  ImpureConfig.Core.Base.bind (MemoryCodeGen.codegen program)
    (fun result => ImpureConfig.Core.Base.pure
      ((if snd result then Some (fst (fst (fst result))) else None),true)).
Theorem memory_attempt_codegen_accept program candidate :
  mayReturn (memory_attempt_codegen program) (Some candidate) ->
  exists generated, mayReturn (MemoryCodeGen.codegen program) generated /\ fst (fst generated) = candidate.
Proof.
  unfold memory_attempt_codegen,CoreAlarmed.Base.mayReturn; intro RUN.
  destruct (ImpureConfig.Core.Base.mayReturn_bind _ _ _ _ _ RUN) as [[generated alarm_free] [GEN RESULT]].
  apply ImpureConfig.Core.Base.mayReturn_pure in RESULT.
  destruct alarm_free; cbn in RESULT; [inversion RESULT; subst; eauto|discriminate].
Qed.

Definition memory_schedule_row_eq : forall first second : list Z * Z,
  {first = second}+{first <> second}.
Proof. decide equality; [apply Z.eq_dec|apply (List.list_eq_dec Z.eq_dec)]. Defined.
Definition memory_schedule_static (row : list Z * Z) := forallb (fun coefficient => Z.eqb coefficient 0) (fst row).
Fixpoint memory_schedule_common_depth first others :=
  match first with
  | [] => 0%nat
  | row::rest =>
    if forallb (fun schedule => match schedule with
      | other::_ => if memory_schedule_row_eq row other then true else false
      | [] => false end) others then
      ((if memory_schedule_static row then 0 else 1) +
        memory_schedule_common_depth rest (map (@tl (list Z * Z)) others))%nat
    else 0%nat end.
Fixpoint memory_schedule_before first second :=
  match first,second with
  | row::rest,other::tail =>
    if memory_schedule_row_eq row other then memory_schedule_before rest tail
    else if memory_schedule_static row && memory_schedule_static other
      then Z.leb (snd row) (snd other) else false
  | _,_ => false end.
Fixpoint memory_schedule_insert (instruction : PL.PolyInstr) instructions :=
  match instructions with
  | [] => [instruction]
  | first::rest =>
    if memory_schedule_before (PL.pi_schedule instruction) (PL.pi_schedule first)
    then instruction::instructions
    else first::memory_schedule_insert instruction rest end.
Fixpoint memory_schedule_sort instructions :=
  match instructions with
  | [] => []
  | first::rest => memory_schedule_insert first (memory_schedule_sort rest) end.
Fixpoint memory_generate_schedule_statements context instructions : CoreAlarmed.Base.imp (option (list L.stmt)) :=
  match instructions with
  | [] => pure (Some [])
  | instruction::rest =>
    BIND candidate <- memory_attempt_codegen
      ([instruction],context,map (fun parameter => (parameter,tt)) context) -;
    match candidate with
    | None => pure None
    | Some candidate =>
      BIND remaining <- memory_generate_schedule_statements context rest -;
      pure (option_map (fun tail => memory_generated_affine_bounds candidate::tail) remaining)
    end end.
Definition memory_generate_scheduled_loop source schedules : CoreAlarmed.Base.imp (option L.stmt) :=
  match MemoryExtractor.extractor source with
  | Okk (instructions,context,_) =>
    match memory_reschedule_instructions (length context) instructions schedules with
    | Some proposed =>
      let proposed := memory_schedule_sort proposed in
      let depth := match proposed with
        | [] => 0%nat
        | first::rest => memory_schedule_common_depth (PL.pi_schedule first) (map PL.pi_schedule rest) end in
      BIND candidates <- memory_generate_schedule_statements context proposed -;
      pure (option_map (memory_generated_fuse_list depth) candidates)
    | None => pure None end
  | Err _ => pure None end.

Definition memory_checked_generated_loop source schedules (check : L.stmt -> CoreAlarmed.Base.imp bool) :=
  BIND candidate <- memory_generate_scheduled_loop source schedules -;
  match candidate with
  | Some candidate => BIND accepted <- check candidate -;
    pure (if accepted then Some candidate else None)
  | None => pure None end.
Theorem memory_checked_generated_loop_certificate source schedules check candidate :
  mayReturn (memory_checked_generated_loop source schedules check) (Some candidate) ->
  mayReturn (check candidate) true.
Proof.
  unfold memory_checked_generated_loop; intro RUN; bind_imp_destruct RUN generated GENERATED.
  destruct generated as [generated|]; [|apply mayReturn_pure in RUN; discriminate].
  bind_imp_destruct RUN accepted ACCEPTED; apply mayReturn_pure in RUN.
  destruct accepted; [inversion RUN; subst; exact ACCEPTED|discriminate].
Qed.
Print Assumptions memory_checked_generated_loop_certificate.
