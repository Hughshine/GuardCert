From Stdlib Require Import List Bool ZArith.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSkipPrefix ClightSyntaxEquality.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleInitializedReductionData
  GuardMemoryDoubleInitializedNestData GuardMemoryLongControl GuardMemoryLongRawLoadedProgress.
Import ListNotations.
Set Implicit Arguments.

(** Only administrative skip prefixes are removed. Labels and other atomic
    statements are retained literally; this is an execution-certified service. *)
Fixpoint double_initialized_elide_skips source := match source with
  | Ssequence first second => match first with
    | Sskip => double_initialized_elide_skips second
    | _ => Ssequence (double_initialized_elide_skips first) (double_initialized_elide_skips second) end
  | Sifthenelse condition yes no => Sifthenelse condition (double_initialized_elide_skips yes) (double_initialized_elide_skips no)
  | Sloop body latch => Sloop (double_initialized_elide_skips body) (double_initialized_elide_skips latch)
  | _ => source end.
Lemma double_initialized_elide_skips_relation source : skip_prefix_relation source (double_initialized_elide_skips source).
Proof.
  induction source; cbn [double_initialized_elide_skips]; try apply skip_prefix_same.
  - destruct source1; cbn [double_initialized_elide_skips] in *;
      try (apply skip_prefix_sequence; assumption).
    apply skip_prefix_insert; exact IHsource2.
  - apply skip_prefix_choice; assumption.
  - apply skip_prefix_loop; assumption.
Qed.
Theorem double_initialized_elide_skips_execution source :
  statement_execution_equivalent source (double_initialized_elide_skips source).
Proof. apply skip_prefix_execution_equivalent, double_initialized_elide_skips_relation. Qed.
Fixpoint double_initialized_raw_nest_code outers description := match outers with
  | [] => Ssequence (Ssequence Sskip (initialized_reduction_initializer description))
      (long_raw_initialized_loop (initialized_reduction_iterator description)
        (Evar (initialized_reduction_header description) memory_long_type)
        (Ssequence Sskip (initialized_reduction_body description)))
  | iterator::rest => long_raw_initialized_loop iterator
      (Evar (initialized_reduction_header description) memory_long_type)
      (double_initialized_raw_nest_code rest description) end.
Definition checked_double_initialized_raw_nest p controls source :=
  match checked_double_initialized_nest p controls (double_initialized_elide_skips source) with
  | Some (outers,description) =>
      if statement_eq source (double_initialized_raw_nest_code outers description)
      then Some (outers,description) else None
  | None => None end.
Theorem checked_double_initialized_raw_nest_sound p controls source outers description :
  checked_double_initialized_raw_nest p controls source=Some (outers,description) ->
  source=double_initialized_raw_nest_code outers description /\
  checked_double_initialized_nest p controls (double_initialized_nest_code outers description)=Some (outers,description) /\
  statement_execution_equivalent source (double_initialized_nest_code outers description).
Proof.
  unfold checked_double_initialized_raw_nest.
  destruct (checked_double_initialized_nest p controls (double_initialized_elide_skips source))
    as [[outer_ids leaf]|] eqn:CHECK; [|discriminate].
  destruct (statement_eq source (double_initialized_raw_nest_code outer_ids leaf)) as [SHAPE|]; [|discriminate].
  intro RESULT; inversion RESULT; subst outers description.
  destruct (@checked_double_initialized_nest_sound p controls (double_initialized_elide_skips source)
    outer_ids leaf CHECK) as [CODE REST].
  split; [exact SHAPE|]; split; [rewrite <- CODE; exact CHECK|].
  rewrite <- CODE; apply double_initialized_elide_skips_execution.
Qed.

Print Assumptions double_initialized_elide_skips_execution.
Print Assumptions checked_double_initialized_raw_nest_sound.
