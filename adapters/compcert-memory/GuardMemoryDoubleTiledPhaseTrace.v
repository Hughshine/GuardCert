From Stdlib Require Import List String.
From polcert.src Require Import OpenScop TilingWitness.
From polcert.polygen Require Import Result.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure Debugging.
From GuardMemory Require Import GuardMemoryDoublePolyhedral GuardMemoryDoubleUniformPrepared
  GuardMemoryDoubleTiledPrepared.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope string_scope.

(** A thunk places the begin marker before eager evaluation after extraction.
    Both markers are the existing logical identity trace primitive. *)
Definition double_phase_stage {A : Type} (label : string) (task : unit -> A) : A :=
  let result := (trace INFO ("guardcert-phase/" ++ label ++ "/begin") task) tt in
  trace INFO ("guardcert-phase/" ++ label ++ "/end") result.
Lemma double_phase_stage_exact {A : Type} label (task : unit -> A) :
  double_phase_stage label task = task tt.
Proof. reflexivity. Qed.

Definition traced_double_tiled_prepared_phase
  (phase : OpenScop -> result (OpenScop * OpenScop * list statement_tiling_witness))
  (source : DoubleAssignmentIRs.PolyLang.t) :=
  match double_phase_stage "export" (fun _ => export_double_uniform_model source) with
  | None => pure None
  | Some before => match double_phase_stage "proposal" (fun _ => phase before) with
    | Err _ => pure None
    | Okk (middle_scop,after_scop,witnesses) =>
      match double_phase_stage "schedule-import" (fun _ => import_double_uniform_schedule source middle_scop) with
      | Err _ => pure None
      | Okk middle =>
        BIND affine_ok <- double_phase_stage "affine-validation"
          (fun _ => DoubleAssignmentValidator.validate source middle) -;
        if affine_ok then
          match double_phase_stage "tile-import"
            (fun _ => DoubleAssignmentTilingValidator.import_canonical_tiled_after_poly middle after_scop witnesses) with
          | Err _ => pure None
          | Okk tiled =>
            BIND tiling_ok <- double_phase_stage "tiling-validation"
              (fun _ => DoubleAssignmentTilingValidator.checked_tiling_validate_poly middle tiled witnesses) -;
            if tiling_ok then
              BIND generated <- double_phase_stage "prepared-codegen"
                (fun _ => DoubleAssignmentPrepare.prepared_codegen
                  (DoubleAssignmentIRs.PolyLang.current_view_pprog tiled)) -;
              pure (Some (generated,witnesses))
            else pure None
          end
        else pure None
      end
    end
  end.
Theorem traced_double_tiled_prepared_phase_exact phase source :
  traced_double_tiled_prepared_phase phase source = checked_double_tiled_prepared_phase phase source.
Proof.
  unfold traced_double_tiled_prepared_phase, checked_double_tiled_prepared_phase,
    double_phase_stage, trace; reflexivity.
Qed.

Print Assumptions double_phase_stage_exact.
Print Assumptions traced_double_tiled_prepared_phase_exact.
